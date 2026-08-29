#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
#![allow(unused_imports)]


use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::cell::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::{pervasive::*, prelude::*, *};

verus! {

use verus_state_machines_macros::tokenized_state_machine;

#[is_variant]
pub enum ProducerState {
    Idle(nat),
    Producing(nat),
}

#[is_variant]
pub enum ConsumerState {
    Idle(nat),
    Consuming(nat),
}

tokenized_state_machine!{FifoQueue<T> {
    fields {

        #[sharding(constant)]
        pub backing_cells: Seq<CellId>,


        #[sharding(storage_map)]
        pub storage: Map<nat, cell::PointsTo<T>>,


        #[sharding(variable)]
        pub head: nat,


        #[sharding(variable)]
        pub tail: nat,


        #[sharding(variable)]
        pub producer: ProducerState,


        #[sharding(variable)]
        pub consumer: ConsumerState,
    }

    pub open spec fn len(&self) -> nat {
        self.backing_cells.len()
    }

    pub open spec fn inc_wrap(i: nat, len: nat) -> nat {
        if i + 1 == len { 0 } else { i + 1 }
    }


    #[invariant]
    pub fn not_overlapping(&self) -> bool {
        match (self.producer, self.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                head != tail
                && Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
                true
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                head != tail
            }
        }
    }


    #[invariant]
    pub fn in_bounds(&self) -> bool {
        0 <= self.head && self.head < self.len() &&
        0 <= self.tail && self.tail < self.len()
        && match self.producer {
            ProducerState::Producing(tail) => {
                self.tail == tail
            }
            ProducerState::Idle(tail) => {
                self.tail == tail
            }
        }
        && match self.consumer {
            ConsumerState::Consuming(head) => {
                self.head == head
            }
            ConsumerState::Idle(head) => {
                self.head == head
            }
        }
    }


    pub open spec fn in_active_range(&self, i: nat) -> bool {
        0 <= i && i < self.len() && (
            if self.head <= self.tail {
                self.head <= i && i < self.tail
            } else {
                i >= self.head || i < self.tail
            }
        )
    }


    pub open spec fn is_checked_out(&self, i: nat) -> bool {
        self.producer == ProducerState::Producing(i)
        || self.consumer == ConsumerState::Consuming(i)
    }


    pub open spec fn valid_storage_at_idx(&self, i: nat) -> bool {
        if self.is_checked_out(i) {
            !self.storage.dom().contains(i)
        } else {
            self.storage.dom().contains(i)

            && self.storage.index(i).id() == self.backing_cells.index(i as int)

            && if self.in_active_range(i) {
                self.storage.index(i).is_init()
            } else {
                self.storage.index(i).is_uninit()
            }
        }
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        forall|i: nat| 0 <= i && i < self.len() ==>
            self.valid_storage_at_idx(i)
    }

    init!{
        initialize(backing_cells: Seq<CellId>, storage: Map<nat, cell::PointsTo<T>>) {

            require(
                (forall|i: nat| 0 <= i && i < backing_cells.len() ==>
                    #[trigger] storage.dom().contains(i)
                    && storage.index(i).id() == backing_cells.index(i as int)
                    && storage.index(i).is_uninit())
            );
            require(backing_cells.len() > 0);

            init backing_cells = backing_cells;
            init storage = storage;
            init head = 0;
            init tail = 0;
            init producer = ProducerState::Idle(0);
            init consumer = ConsumerState::Idle(0);
        }
    }

    transition!{
        produce_start() {
            require(pre.producer.is_Idle());

            let tail = pre.producer.get_Idle_0();
            let head = pre.head;

            assert(0 <= tail && tail < pre.backing_cells.len());

            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());

            require(next_tail != head);

            update producer = ProducerState::Producing(tail);

            withdraw storage -= [tail => let perm] by {
                assert(pre.valid_storage_at_idx(tail));
            };

            assert(
                perm.id() == pre.backing_cells.index(tail as int)
                && perm.is_uninit()
            ) by {
                assert(!pre.in_active_range(tail));
                assert(pre.valid_storage_at_idx(tail));
            };
        }
    }

    transition!{
        produce_end(perm: cell::PointsTo<T>) {
            require(pre.producer.is_Producing());
            let tail = pre.producer.get_Producing_0();

            assert(0 <= tail && tail < pre.backing_cells.len());

            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());



            require(perm.id() == pre.backing_cells.index(tail as int)
              && perm.is_init());

            update producer = ProducerState::Idle(next_tail);
            update tail = next_tail;

            deposit storage += [tail => perm] by { assert(pre.valid_storage_at_idx(tail)); };
        }
    }

    transition!{
        consume_start() {
            require(pre.consumer.is_Idle());

            let head = pre.consumer.get_Idle_0();
            let tail = pre.tail;

            assert(0 <= head && head < pre.backing_cells.len());

            require(head != tail);

            update consumer = ConsumerState::Consuming(head);


            birds_eye let perm = pre.storage.index(head);
            withdraw storage -= [head => perm] by {
                assert(pre.valid_storage_at_idx(head));
            };

            assert(perm.id() == pre.backing_cells.index(head as int)) by {
                assert(pre.valid_storage_at_idx(head));
            };
            assert(perm.is_init()) by {
                assert(pre.in_active_range(head));
                assert(pre.valid_storage_at_idx(head));
            };
        }
    }

    transition!{
        consume_end(perm: cell::PointsTo<T>) {
            require(pre.consumer.is_Consuming());
            let head = pre.consumer.get_Consuming_0();

            assert(0 <= head && head < pre.backing_cells.len());
            let next_head = Self::inc_wrap(head, pre.backing_cells.len());

            update consumer = ConsumerState::Idle(next_head);
            update head = next_head;

            require(perm.id() == pre.backing_cells.index(head as int)
              && perm.is_uninit());
            deposit storage += [head => perm] by { assert(pre.valid_storage_at_idx(head)); };
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, backing_cells: Seq<CellId>, storage: Map<nat, cell::PointsTo<T>>) {
        assert forall|i: nat|
            0 <= i && i < post.len() implies post.valid_storage_at_idx(i)
        by {
            assert(post.storage.dom().contains(i));
        }
    }


    #[inductive(produce_start)]
    fn produce_start_inductive(pre: Self, post: Self) {
        let tail = pre.producer.get_Idle_0();
        assert(!pre.in_active_range(tail));
        match (post.producer, post.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                assert(Self::inc_wrap(tail, post.len()) != head);
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
                assert(Self::inc_wrap(tail, post.len()) != head);
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
            }
        }
        assert(forall|i| pre.valid_storage_at_idx(i) ==> post.valid_storage_at_idx(i));
    }

    #[inductive(produce_end)]
    fn produce_end_inductive(pre: Self, post: Self, perm: cell::PointsTo<T>) {
        assert forall |i|
            pre.valid_storage_at_idx(i) implies
            post.valid_storage_at_idx(i)
        by {
        }
    }

    #[inductive(consume_start)]
    fn consume_start_inductive(pre: Self, post: Self) {
        assert forall |i|
            pre.valid_storage_at_idx(i) implies post.valid_storage_at_idx(i)
        by { }
    }

    #[inductive(consume_end)]
    fn consume_end_inductive(pre: Self, post: Self, perm: cell::PointsTo<T>) {
        let head = pre.consumer.get_Consuming_0();
        assert(post.storage.dom().contains(head));
        assert(
                post.storage.index(head).id() ==
                post.backing_cells.index(head as int)
            );
        assert(if post.in_active_range(head) {
                post.storage.index(head).is_init()
            } else {
                post.storage.index(head).is_uninit()
            });

        match (pre.producer, pre.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                assert(pre.head != pre.tail);
            }
        };

        assert(pre.head != pre.tail);
        assert(!post.is_checked_out(head));
        assert(post.valid_storage_at_idx(head));

        assert forall |i|
            pre.valid_storage_at_idx(i) implies post.valid_storage_at_idx(i)
        by { }
    }
}}

struct_with_invariants!{
    struct Queue<T> {
        buffer: Vec<PCell<T>>,
        head: AtomicU64<_, FifoQueue::head<T>, _>,
        tail: AtomicU64<_, FifoQueue::tail<T>, _>,

        instance: Tracked<FifoQueue::Instance<T>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.instance@.backing_cells().len() == self.buffer@.len()
            &&& forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
                self.instance@.backing_cells().index(i) ==
                    self.buffer@.index(i).id()
        }

        invariant on head with (instance) is (v: u64, g: FifoQueue::head<T>) {
            &&& g.instance_id() == instance@.id()
            &&& g.value() == v as int
        }

        invariant on tail with (instance) is (v: u64, g: FifoQueue::tail<T>) {
            &&& g.instance_id() == instance@.id()
            &&& g.value() == v as int
        }
    }
}

pub struct Producer<T> {
    queue: Arc<Queue<T>>,
    tail: usize,
    producer: Tracked<FifoQueue::producer<T>>,
}

impl<T> Producer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.queue).wf()
            && self.producer@.instance_id() == (*self.queue).instance@.id()
            && self.producer@.value() == ProducerState::Idle(self.tail as nat)
            && (self.tail as int) < (*self.queue).buffer@.len()
    }
}

pub struct Consumer<T> {
    queue: Arc<Queue<T>>,
    head: usize,
    consumer: Tracked<FifoQueue::consumer<T>>,
}

impl<T> Consumer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.queue).wf()
            && self.consumer@.instance_id() == (*self.queue).instance@.id()
            && self.consumer@.value() == ConsumerState::Idle(self.head as nat)
            && (self.head as int) < (*self.queue).buffer@.len()
    }
}

pub fn new_queue<T>(len: usize) -> (pc: (Producer<T>, Consumer<T>))
    requires
        len > 0,
    ensures
        pc.0.wf(),
        pc.1.wf(),
{
    let mut backing_cells_vec = Vec::<PCell<T>>::new();
    let tracked mut perms = Map::<nat, cell::PointsTo<T>>::tracked_empty();
    while backing_cells_vec.len() < len
        invariant
            forall|j: nat|
                #![trigger( perms.dom().contains(j) )]
                #![trigger( backing_cells_vec@.index(j as int) )]
                #![trigger( perms.index(j) )]
                0 <= j && j < backing_cells_vec.len() as int ==> perms.dom().contains(j)
                    && backing_cells_vec@.index(j as int).id() == perms.index(j).id()
                    && perms.index(j).is_uninit(),
    {
        let ghost i = backing_cells_vec.len();
        let (cell, cell_perm) = PCell::empty();
        backing_cells_vec.push(cell);
        proof {
            perms.tracked_insert(i as nat, cell_perm.get());
        }
        assert(perms.dom().contains(i as nat));
        assert(backing_cells_vec@.index(i as int).id() == perms.index(i as nat).id());
        assert(perms.index(i as nat).is_uninit());
    }

    let ghost mut backing_cells_ids = Seq::<CellId>::new(
        backing_cells_vec@.len(),
        |i: int| backing_cells_vec@.index(i).id(),
    );
    let tracked (
        Tracked(instance),
        Tracked(head_token),
        Tracked(tail_token),
        Tracked(producer_token),
        Tracked(consumer_token),
    ) = FifoQueue::Instance::initialize(backing_cells_ids, perms, perms);
    let tracked_inst: Tracked<FifoQueue::Instance<T>> = Tracked(instance.clone());
    let head_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(head_token));
    let tail_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(tail_token));
    let queue = Queue::<T> {
        instance: Tracked(instance),
        head: head_atomic,
        tail: tail_atomic,
        buffer: backing_cells_vec,
    };
    let queue_arc = Arc::new(queue);
    let prod = Producer::<T> {
        queue: queue_arc.clone(),
        tail: 0,
        producer: Tracked(producer_token),
    };
    let cons = Consumer::<T> { queue: queue_arc, head: 0, consumer: Tracked(consumer_token) };
    (prod, cons)
}

impl<T> Consumer<T> {
    fn dequeue(&mut self) -> (t: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        loop
            invariant
                self.wf(),
        {
            let queue = &*self.queue;
            let len = queue.buffer.len();
            assert(0 <= self.head && self.head < len);
            let next_head = if self.head + 1 == len {
                0
            } else {
                self.head + 1
            };
            let tracked cell_perm: Option<cell::PointsTo<T>> = Option::None;
            let tail =
                atomic_with_ghost!(&queue.tail => load();
                returning tail;
                ghost tail_token => {
                    if self.head as u64 != tail {
                        let tracked (ghost_map, Tracked(perm)) =
                            self.queue.instance.borrow().consume_start(
                                &mut tail_token,
                                &mut self.consumer,
                            );
                        cell_perm = Option::Some(perm);
                    }
                }
            );
            if self.head as u64 != tail {
                let tracked mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => {
                        assert(false);
                        proof_from_false()
                    },
                };
                let t = queue.buffer[self.head].take(Tracked(&mut cell_perm));
                atomic_with_ghost!(&queue.head => store(next_head as u64); ghost head_token => {
                    self.queue.instance.borrow().consume_end(
                        cell_perm,
                        cell_perm,
                        &mut head_token,
                        &mut self.consumer,
                    );
                });
                self.head = next_head;
                return t;
            }
        }
    }
}

fn main() {
}

}
