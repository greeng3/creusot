//! This implementation is an adaption from:
//! https://sites.google.com/site/1024cores/home/lock-free-algorithms/queues/bounded-mpmc-queue

#![allow(unused)]

use core::{borrow::BorrowMut, cmp::Ordering, mem::MaybeUninit};
use creusot_std::{
    cell::PermCell,
    ghost::{
        invariant::{AtomicInvariant, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment, Resource, fmap_view},
    },
    logic::{
        FMap, Id,
        ra::{RA, UnitRA, auth::Auth, excl::Excl, lattice::SemiLattice},
        seq::Seq,
    },
    partial_ord_laws_impl,
    prelude::*,
    std::sync::{
        atomic::{
            AtomicUsize,
            ordering::{Acquire, Relaxed, Release},
        },
        committer::Committer,
        view::{AtView, HasTimestamp, SyncView},
    },
};

declare_namespace! { BOUNDED_MPMC_QUEUE }

type Item<T> = Perm<PermCell<MaybeUninit<T>>>;
type Value<T> = (T, SyncView);
type ValueO<T> = Option<Excl<Seq<Value<T>>>>;

pub struct QueueOwn<T>(pub Fragment<ValueO<T>>);

struct QueueInv<T> {
    head_own: Perm<AtomicUsize>,
    tail_own: Perm<AtomicUsize>,
    items_own: Seq<AtView<Item<T>>>,      // in [0; N]
    statuses_own: Seq<Perm<AtomicUsize>>, // in [0; N]

    values_auth: Authority<ValueO<T>>,
    statuses_auth: Seq<Authority<StatusWithView>>, // in [0; N]
    tokens_auth: fmap_view::Authority<Int, Excl<Option<Value<T>>>>,

    head: Snapshot<Int>,
    tail: Snapshot<Int>,
    values: Snapshot<Seq<Value<T>>>, // in [self.tail; self.head - 1]
}

impl<T> Protocol for QueueInv<T> {
    type Public = (AtomicUsize, AtomicUsize, Seq<PermCell<MaybeUninit<T>>>);

    #[logic]
    fn public(self) -> Self::Public {
        (
            *self.head_own.ward(),
            *self.tail_own.ward(),
            self.items_own.map(|x: AtView<Item<T>>| *x.val().ward()),
        )
    }

    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            let len = self.statuses_own.len();

            (self.statuses_own.len() == self.items_own.len()) &&
            (self.statuses_own.len() == self.statuses_auth.len()) &&

            // 0 <= t <= h <= t + len
            (0 <= *self.tail && *self.tail <= *self.head && *self.head <= *self.tail + len) &&

            // head ~> (h, H)
            (forall<ts>
                self.head_own.val().contains(ts) ==>
                    self.head_own.val()[ts].0@ == *self.head ||
                    self.head_own.val().contains(ts + 1)
            ) &&

            // tail ~> (t, T)
            (forall<ts>
                self.tail_own.val().contains(ts) ==>
                    self.tail_own.val()[ts].0@ == *self.tail ||
                    self.tail_own.val().contains(ts + 1)
            ) &&

            // statuses ~>* [(s_0, S_0), ..., (s_len - 1, S_len - 1)]
            // { i -> •(s_i, S_i) | 0 <= i < len }
            (forall<i> 0 <= i && i < len ==>
                 forall<ts>
                 match (self.statuses_own[i].val().get(ts)) {
                     Some((status, view)) => StatusWithView { status: status@, view } >= self.statuses_auth[i]@,
                     _ => true
                 }) &&

            // • [(v_t, V_t), ..., (v_h-1, V_h-1)]
            self.values_auth@ == Some(Excl(*self.values)) &&
            self.values.len() == *self.head - *self.tail &&

            // •({ k -> ()         | h - len <= k < t }
            //   { k -> (v_k, V_k) |       t <= k < h })
            (forall<k> *self.head <= k && k < *self.tail + len ==> self.tokens_auth@[k] == Excl(None)) &&
            (forall<k> *self.tail <= k && k < *self.head ==> self.tokens_auth@[k] == Excl(Some(self.values[k - *self.tail]))) &&

            // ∗{h - len <= k < t} s_k = 2k + 1 \/ Available k (s_k, S_k)
            (forall<k> *self.head <= k && k < *self.tail + len ==>
             match self.statuses_auth[k % len]@ {
                 StatusWithView { status, view } =>
                     (status == 2 * (k - len) + 1) ||
                     (status == 2 * k &&
                      view >= self.items_own[k % len].view() &&
                      self.tokens_auth@[k] == Excl(None)),
             }) &&

            // ∗{t <= k < h} s_k = 2k \/ Occupied k (s_k, S_k) (v_k, V_k)
            (forall<k> *self.tail <= k && k < *self.head ==>
             match self.statuses_auth[k % len]@ {
                 StatusWithView { status, view } =>
                     (status == 2 * k) ||
                     { let value = self.values[k];
                       status == 2 * k + 1 &&
                       view >= self.items_own[k % len].view() &&
                       self.tokens_auth@[k] == Excl(Some(value)) &&
                       self.items_own[k % len].val().val()@ == Some(value.0) && value.1 <= view },
            })
        }
    }
}

struct StatusWithView {
    pub status: Int,
    pub view: SyncView,
}

impl PartialOrdLogic for StatusWithView {
    #[logic(open)]
    fn lt_log(self, other: Self) -> bool {
        (self.status < other.status) || (self.status == other.status && self.view > other.view)
    }

    partial_ord_laws_impl! {}
}

impl SemiLattice for StatusWithView {
    #[logic]
    #[ensures(self <= result)]
    #[ensures(other <= result)]
    #[ensures(forall<r> self <= r ==> other <= r ==> result <= r)]
    fn join(self, other: Self) -> Self {
        match self.status.cmp_log(other.status) {
            Ordering::Less => other,
            Ordering::Greater => self,
            Ordering::Equal => {
                StatusWithView { status: self.status, view: self.view.meet(other.view) }
            }
        }
    }
}

// TODO: [VL] Maybe trusted SyncView minimal ?
impl UnitRA for StatusWithView {
    #[logic(opaque)]
    #[ensures(forall<x: Self> #[trigger(x.op(result))] x.op(result) == Some(x))]
    #[trusted]
    fn unit() -> Self {
        dead
    }

    #[logic]
    #[ensures(self.core_total().op(self.core_total()) == Some(self.core_total()))]
    #[ensures(self.core_total().op(self) == Some(self))]
    #[trusted]
    fn core_total_idemp(self) {}
}

pub struct Queue<T> {
    pub items: Vec<QueueCell<T>>,
    pub head: AtomicUsize,
    pub tail: AtomicUsize,
    inv: Ghost<AtomicInvariant<QueueInv<T>>>,
}

struct QueueCell<T> {
    item: PermCell<MaybeUninit<T>>,
    status: AtomicUsize,
}

impl<T> Invariant for Queue<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            let len = self.items@.len();

            0 < len &&
            self.inv.public() == (
                self.head,
                self.tail,
                Seq::create(len, |i| self.items@[i]).map(|c: QueueCell<T>| c.item),
            )
        }
    }
}

impl<T> Queue<T> {
    #[requires(0 < 2 * length@ && 2 * length@ <= usize::MAX@)]
    #[ensures((*result.1).0@ != None)]
    #[ensures((*result.1).0@.unwrap_logic().0.len() == 0)]
    pub fn new(length: usize) -> (Self, Ghost<QueueOwn<T>>) {
        let mut tokens_auth: Ghost<fmap_view::Authority<Int, Excl<Option<Value<T>>>>> =
            fmap_view::Authority::new();

        let mut statuses_auth: Ghost<Seq<Authority<StatusWithView>>> = Seq::new();
        let mut items_own: Ghost<Seq<AtView<Item<T>>>> = Seq::new();
        let mut statuses_own: Ghost<Seq<Perm<AtomicUsize>>> = Seq::new();
        let mut items: Vec<QueueCell<T>> = Vec::new();

        let mut values_auth: Ghost<Authority<ValueO<T>>> = Authority::alloc();
        let queue_own = ghost!(values_auth.add_fragment(snapshot!(Some(Excl(Seq::empty())))));

        #[invariant(items@.len() == produced.len())]
        #[invariant(items_own.len() == produced.len())]
        #[invariant(statuses_auth.len() == produced.len())]
        #[invariant(statuses_own.len() == produced.len())]
        #[invariant(tokens_auth@.len() == produced.len())]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==> *items_own[i].val().ward() == items@[i].item)]
        #[invariant(forall<i> produced.len() <= i ==> statuses_auth.get(i) == None)]
        #[invariant(forall<i> produced.len() <= i ==> tokens_auth@.get(i) == None)]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==> *items_own[i].val().ward() == items@[i].item)]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==> *statuses_own[i].ward() == items@[i].status)]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==> tokens_auth@[i] == Excl(None))]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==>
             forall<ts>
             match statuses_own[i].val().get(ts) {
                 Some((status, view)) => StatusWithView { status: status@, view } >= statuses_auth[i]@,
                 _ => true
             }
        )]
        #[invariant(forall<i> 0 <= i && i < produced.len() ==>
             match statuses_auth[i]@ {
                 StatusWithView { status, view } => status == 2 * i && view >= items_own[i].view()
             }
        )]
        for i in 0..length {
            let (item, item_own) = PermCell::new(MaybeUninit::uninit());

            let at_view = AtView::new(item_own);
            let mut view = ghost!(at_view.0);
            let at_view = ghost!(at_view.into_inner().1);

            let (status, status_own) = AtomicUsize::new(2 * i, view.borrow_mut());

            ghost! {
                let status_view = Resource::alloc(snapshot!(Auth::new_auth(StatusWithView { status: 2 * i@, view: *view })));

                items_own.push_back_ghost(at_view.into_inner());
                statuses_own.push_back_ghost(status_own.into_inner());
                statuses_auth.push_back_ghost(Authority::from_resource(status_view.into_inner()).0);
                tokens_auth.insert(snapshot!(i@), snapshot!(Excl(None)));
            };

            items.push(QueueCell { item, status })
        }

        let (head, head_own) = AtomicUsize::new(0, SyncView::new().borrow_mut());
        let (tail, tail_own) = AtomicUsize::new(0, SyncView::new().borrow_mut());

        let inv = AtomicInvariant::new(
            ghost!(QueueInv {
                head_own: head_own.into_inner(),
                tail_own: tail_own.into_inner(),
                items_own: items_own.into_inner(),
                statuses_own: statuses_own.into_inner(),

                values_auth: values_auth.into_inner(),
                statuses_auth: statuses_auth.into_inner(),
                tokens_auth: tokens_auth.into_inner(),

                head: snapshot!(0),
                tail: snapshot!(0),
                values: snapshot!(Seq::empty()),
            }),
            snapshot!(BOUNDED_MPMC_QUEUE()),
        );

        let queue = Queue { items, head, tail, inv };

        (queue, ghost!(QueueOwn(queue_own.into_inner())))
    }

    // TODO [VL]: Add a user committer at the serialisation point
    // It might only contains •([(v_t, V_t), ..., [(v_h-1, V_h-1)]])
    #[requires(tokens.contains(BOUNDED_MPMC_QUEUE()))]
    #[requires(queue_own.0@ != None)]
    #[requires(queue_own.0@.unwrap_logic().0.len() == self.items@.len())]
    #[ensures(result != None ==> {
        let old_len = queue_own.0@.unwrap_logic().0.len();
        (result.unwrap_logic().0@ != None) &&
        (result.unwrap_logic().0@.unwrap_logic().0.len() == old_len + 1) &&
        (forall<i> 0 <= i && i < old_len ==>
            queue_own.0@.unwrap_logic().0[i] == result.unwrap_logic().0@.unwrap_logic().0[i]) &&
        (result.unwrap_logic().0@.unwrap_logic().0[old_len] == (item, *view))
    })]
    pub fn try_enqueue(
        &self,
        item: T,
        mut tokens: Ghost<Tokens>,
        mut view: Ghost<SyncView>,
        queue_own: Ghost<QueueOwn<T>>,
    ) -> Option<Ghost<QueueOwn<T>>> {
        let mut witness: Ghost<Option<Fragment<StatusWithView>>> = ghost!(None);

        let head = self.head.load(ghost! { |c: &Committer<_, _, Relaxed, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                c.shoot_load(&inv.head_own, &mut view.borrow_mut());
            });
        } });

        let cell = &self.items[head % self.items.len()];
        let status = cell.status.load(ghost! { |c: &Committer<_, _, Acquire, _>| {
            self.inv.open(tokens.reborrow(), |inv: &mut QueueInv<T>| {
                let index = snapshot!(head.view() % self.items.view().len()).into_ghost();
                c.shoot_load(&inv.statuses_own[*index], &mut view.borrow_mut());

                let head_ghost = snapshot!(head@).into_ghost();
                let mut status_auth = &mut inv.statuses_auth[*head_ghost];
                let status_view = snapshot!(StatusWithView { status: c.val_load()@, view: *view });
                *witness = Some(status_auth.add_fragment(status_view));
            });
        } });

        if 2 * head != status {
            return None;
        }

        let res = self.head.compare_exchange_weak::<_, Relaxed, Relaxed>(
            head,
            head + 1,
            ghost! { |c: Result<&mut _, &_>| { /* TODO */ }},
        );

        if res.is_err() {
            return None;
        }

        unsafe { cell.item.set(Ghost::conjure(), MaybeUninit::new(item)) };
        cell.status.store(head + 1, ghost! { |c: &mut Committer<_, _, _, Release>| { /* TODO */ }});

        None
    }

    pub fn try_dequeue(&self) -> Option<T> {
        let tail = self.tail.load(ghost! { |c: &Committer<_, _, Relaxed, _>| {} });

        let cell = &self.items[tail % self.items.len()];
        let status = cell.status.load(ghost! { |c: &Committer<_, _, Acquire, _>| {} });

        if tail + 1 != status {
            return None;
        }

        let res = self.tail.compare_exchange_weak::<_, Relaxed, Relaxed>(
            tail,
            tail + 1,
            ghost! { |c: Result<&mut _, &_>| {}},
        );

        if res.is_err() {
            return None;
        }

        let item = unsafe {
            let v = cell.item.replace(Ghost::conjure(), MaybeUninit::uninit());
            v.assume_init()
        };
        cell.status
            .store(tail + self.items.len(), ghost! { |c: &mut Committer<_, _, _, Release>| {} });

        Some(item)
    }
}
