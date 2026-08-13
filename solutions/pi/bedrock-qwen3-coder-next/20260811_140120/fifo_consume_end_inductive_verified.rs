// rust_verify/tests/example.rs expect-warnings
#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
#![allow(unused_imports)]

// port of single-producer single-consumer queue from LinearDafny
// https://github.com/vmware-labs/verified-betrfs/tree/concurrency-experiments/concurrency/spsc-queue

// ANCHOR:full
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

// ANCHOR: enum_state
#[is_variant]
pub enum ProducerState {
    Idle(nat),  // local copy of tail
    Producing(nat),
}

#[is_variant]
pub enum ConsumerState {
    Idle(nat),  // local copy of head
    Consuming(nat),
}
// ANCHOR_END: enum_state

// ANCHOR: fields
tokenized_state_machine!{FifoQueue<T> {
    fields {
        // IDs of the cells used in the ring buffer.
        // These are fixed throughout the protocol.

        #[sharding(constant)]
        pub backing_cells: Seq<CellId>,

        // All the stored permissions

        #[sharding(storage_map)]
        pub storage: Map<nat, cell::PointsTo<T>>,

        // Represents the shared `head` field

        #[sharding(variable)]
        pub head: nat,

        // Represents the shared `tail` field

        #[sharding(variable)]
        pub tail: nat,

        // Represents the local state of the single-producer

        #[sharding(variable)]
        pub producer: ProducerState,

        // Represents the local state of the single-consumer

        #[sharding(variable)]
        pub consumer: ConsumerState,
    }
    // ANCHOR_END: fields

    pub open spec fn len(&self) -> nat {
        self.backing_cells.len()
    }

    // ANCHOR: inc_wrap
    pub open spec fn inc_wrap(i: nat, len: nat) -> nat {
        if i + 1 == len { 0 } else { i + 1 }
    }
    // ANCHOR_END: inc_wrap

    // Make sure the producer state and the consumer state aren't inconsistent.

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

    // `head` and `tail` are in-bounds
    // shared `head` and `tail` fields agree with the ProducerState and ConsumerState

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

    // Indicates whether we expect the cell at index `i` to be full based on
    // the values of the `head` and `tail`.

    pub open spec fn in_active_range(&self, i: nat) -> bool {
        // Note that self.head = self.tail means empty range
        0 <= i && i < self.len() && (
            if self.head <= self.tail {
                self.head <= i && i < self.tail
            } else {
                i >= self.head || i < self.tail
            }
        )
    }

    // Indicates whether we expect a cell to be checked out or not,
    // based on the producer/consumer state.

    pub open spec fn is_checked_out(&self, i: nat) -> bool {
        self.producer == ProducerState::Producing(i)
        || self.consumer == ConsumerState::Consuming(i)
    }

    // Predicate to determine that the state at cell index `i`
    // is correct. For each index, there are three possibilities:
    //
    //  1. No cell permission is stored
    //  2. Permission is stored; permission indicates a full cell
    //  3. Permission is stored; permission indicates an empty cell
    //
    // Which of these 3 possibilities we should be in depends on the
    // producer/consumer/head/tail state.

    pub open spec fn valid_storage_at_idx(&self, i: nat) -> bool {
        if self.is_checked_out(i) {
            // No cell permission is stored
            !self.storage.dom().contains(i)
        } else {
            // Permission is stored
            self.storage.dom().contains(i)

            // Permission must be for the correct cell:
            && self.storage.index(i).id() == self.backing_cells.index(i as int)

            && if self.in_active_range(i) {
                // The cell is full
                self.storage.index(i).is_init()
            } else {
                // The cell is empty
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
            // Upon initialization, the user needs to deposit _all_ the relevant
            // cell permissions to start with. Each permission should indicate
            // an empty cell.

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

    // ANCHOR: transition_produce_start
    transition!{
        produce_start() {
            // In order to begin, we have to be in ProducerState::Idle.
            require(pre.producer.is_Idle());

            // We'll be comparing the producer's _local_ copy of the tail
            // with the _shared_ version of the head.
            let tail = pre.producer.get_Idle_0();
            let head = pre.head;

            assert(0 <= tail && tail < pre.backing_cells.len());

            // Compute the incremented tail, wrapping around if necessary.
            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());

            // We have to check that the buffer isn't full to proceed.
            require(next_tail != head);

            // Update the producer's local state to be in the `Producing` state.
            update producer = ProducerState::Producing(tail);

            // Withdraw ("check out") the permission stored at index `tail`.
            // This creates a proof obligation for the transition system to prove that
            // there is actually a permission stored at this index.
            withdraw storage -= [tail => let perm] by {
                assert(pre.valid_storage_at_idx(tail));
            };

            // The transition needs to guarantee to the client that the
            // permission they are checking out:
            //  (i) is for the cell at index `tail` (the IDs match)
            //  (ii) the permission indicates that the cell is empty
            assert(
                perm.id() == pre.backing_cells.index(tail as int)
                && perm.is_uninit()
            ) by {
                assert(!pre.in_active_range(tail));
                assert(pre.valid_storage_at_idx(tail));
            };
        }
    }
    // ANCHOR_END: transition_produce_start

    // ANCHOR: transition_produce_end
    transition!{
        // This transition is parameterized by the value of the permission
        // being inserted. Since the permission is being deposited
        // (coming from "outside" the system) we can't compute it as a
        // function of the current state, unlike how we did it for the
        // `produce_start` transition).
        produce_end(perm: cell::PointsTo<T>) {
            // In order to complete the produce step,
            // we have to be in ProducerState::Producing.
            require(pre.producer.is_Producing());
            let tail = pre.producer.get_Producing_0();

            assert(0 <= tail && tail < pre.backing_cells.len());

            // Compute the incremented tail, wrapping around if necessary.
            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());

            // This time, we don't need to compare the `head` and `tail` - we already
            // check that, and anyway, we don't have access to the `head` field
            // for this transition. (This transition is supposed to occur while
            // modifying the `tail` field, so we can't do both.)

            // However, we _do_ need to check that the permission token being
            // checked in satisfies its requirements. It has to be associated
            // with the correct cell, and it has to be full.

            require(perm.id() == pre.backing_cells.index(tail as int)
              && perm.is_init());

            // Perform our updates. Update the tail to the computed value,
            // both the shared version and the producer's local copy.
            // Also, move back to the Idle state.
            update producer = ProducerState::Idle(next_tail);
            update tail = next_tail;

            // Check the permission back into the storage map.
            deposit storage += [tail => perm] by { assert(pre.valid_storage_at_idx(tail)); };
        }
    }
    // ANCHOR_END: transition_produce_end

    transition!{
        consume_start() {
            // In order to begin, we have to be in ConsumerState::Idle.
            require(pre.consumer.is_Idle());

            // We'll be comparing the consumer's _local_ copy of the head
            // with the _shared_ version of the tail.
            let head = pre.consumer.get_Idle_0();
            let tail = pre.tail;

            assert(0 <= head && head < pre.backing_cells.len());

            // We have to check that the buffer isn't empty to proceed.
            require(head != tail);

            // Update the consumer's local state to be in the `Consuming` state.
            update consumer = ConsumerState::Consuming(head);

            // Withdraw ("check out") the permission stored at index `tail`.

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
        // Need to prove: valid_storage_all for post
        // Post state: head = 0, tail = 0, producer = Idle(0), consumer = Idle(0)
        // For any i in [0, len):
        //   - is_checked_out(i) = false (both are Idle)
        //   - storage.dom().contains(i) (from init requirement)
        //   - storage.index(i).id() == backing_cells.index(i) (from init requirement)
        //   - in_active_range(i) = false (head = tail = 0, range is empty)
        //   - storage.index(i).is_uninit() (from init requirement)
        // So valid_storage_at_idx(i) holds
        broadcast use group_map_properties, group_multiset_axioms;
    }
    #[inductive(produce_start)]
    fn produce_start_inductive(pre: Self, post: Self) {
        // Need to prove: valid_storage_all for post
        // Pre invariant: valid_storage_all(pre)
        // In produce_start:
        //   - tail = pre.producer.Idle_0
        //   - next_tail = inc_wrap(tail, len)
        //   - producer: Idle(tail) -> Producing(tail)
        //   - storage: withdraw storage -= [tail => _] (removes tail from domain)
        //
        // For i != tail:
        //   - is_checked_out(i) unchanged
        //   - storage unchanged
        //   - in_active_range unchanged (head, tail unchanged for this)
        //   - valid_storage_at_idx(i) follows from pre
        //
        // For i == tail:
        //   - pre: is_checked_out(tail) = false, in_active_range(tail) = false (not tail)
        //     storage.dom().contains(tail), storage.index(tail).is_uninit()
        //   - post: is_checked_out(tail) = true ( Producing(tail) )
        //     storage.dom().does_not_contain(tail) (withdraw removed it)
        //   - valid_storage_at_idx(tail) holds (not checked out, not in domain)
        broadcast use group_map_properties, group_multiset_axioms;
    }
    #[inductive(produce_end)]
    fn produce_end_inductive(pre: Self, post: Self, perm: cell::PointsTo<T>) {
        // Need to prove: valid_storage_all for post
        // Pre invariant: valid_storage_all(pre)
        // In produce_end:
        //   - tail = pre.producer.Producing_0
        //   - next_tail = inc_wrap(tail, len)
        //   - producer: Producing(tail) -> Idle(next_tail)
        //   - tail: tail -> next_tail
        //   - storage: deposit storage += [tail => perm] (adds tail to domain with perm)
        //
        // For i != tail:
        //   - is_checked_out(i) unchanged (only tail changed producer)
        //   - in_active_range(i) may change if i is near tail or next_tail
        //   - storage: for i != tail, storage.index(i) unchanged
        //
        // For i == tail:
        //   - pre: is_checked_out(tail) = true, so tail not in storage domain
        //   - post: is_checked_out(tail) = false (Idle(next_tail) != Producing(tail))
        //     storage.dom().contains(tail) (deposit added it)
        //     storage.index(tail) = perm, perm.id() == backing_cells.index(tail) (requirement)
        //     Need to check in_active_range(tail) in post:
        //       - If next_tail <= tail: in_active_range(tail) = next_tail <= tail && tail < tail = false
        //       - If next_tail > tail: in_active_range(tail) = tail >= next_tail || tail < tail = false
        //     So in_active_range(tail) = false, need perm.is_uninit() -- but perm.is_init()!
        //
        //   Wait, this is the problem! Let me reconsider...
        //   - next_tail = inc_wrap(tail, len)
        //   - If tail < len-1: next_tail = tail + 1 > tail, so next_tail > tail
        //   - If tail == len-1: next_tail = 0, and 0 <= tail (always), so need to check 0 <= tail
        //     but 0 <= tail-1 for tail == len-1... actually tail = len-1 >= 0 always
        //     So for tail == len-1: next_tail = 0 <= tail, so in_active_range(tail) = 0 <= tail && tail < 0 = false
        //
        //   So in_active_range(tail) in post = false in all cases!
        //   But we're depositing perm with perm.is_init(), and we need is_uninit()!
        //
        //   Let me re-think the semantics...
        //   - When we produce at index tail, we're filling that cell
        //   - After producing, tail moves to next_tail
        //   - The cell at OLD tail (the one we just filled) should be in the active range
        //   - The active range is [head, tail) where tail is the NEW tail (next_tail)
        //   - So the cell at old tail should be at index next_tail - 1 (or len-1 if wrapped)
        //   - This cell is in the range [head, next_tail) if head <= next_tail - 1
        //   - OR in [head, len) U [0, next_tail) if head > next_tail
        //
        //   Actually, I think I've been confusing myself. Let me be more precise:
        //   - pre.tail = some value T
        //   - post.tail = inc_wrap(T, len) = T+1 (or 0 if T == len-1)
        //   - The cell we produced at is T (the OLD tail)
        //   - After production, the active range extends to the new tail T+1 (or wraps to 0)
        //   - So cell T should be in the active range [head, T+1) or [head, len) U [0, 0) if wrapped
        //
        //   For cell T in post:
        //   - If T < len-1: new_tail = T+1, in_active_range(T) = T+1 <= T && T < T+1 = false
        //   - If T == len-1: new_tail = 0, in_active_range(T) = 0 <= T && T < 0 = false (T = len-1 >= 0)
        //
        //   So in_active_range(T) = false in post! This means the cell should be empty!
        //   But we just produced to it, so it should be full!
        //
        //   Oh wait, I think I misunderstand the semantics. Let me re-read...
        //   - in_active_range(i) means the cell at i is in the "active" region between head and tail
        //   - If head <= tail: active range is [head, tail) (cells head, head+1, ..., tail-1)
        //   - If head > tail: active range is [head, len) U [0, tail) (cells head, ..., len-1, 0, ..., tail-1)
        //
        //   The active range represents cells that have beenProduced but NOT yet Consumed.
        //   - When produce_start: we check out the cell at tail (before incrementing)
        //   - When produce_end: we deposit back at tail (the OLD tail, before incrementing)
        //   - After produce_end: tail = inc_wrap(old_tail), so tail = old_tail + 1 (or 0)
        //   - The active range now goes up to (but not including) the new tail
        //   - So old_tail = new_tail - 1 (or len-1 if wrapped) should be in the active range!
        //
        //   Let me check: if old_tail = len-1, new_tail = 0
        //   - in_active_range(len-1) with head'=head, tail'=0
        //   - head' <= tail'? head' <= 0? Only if head' = 0
        //     - If head' = 0 <= 0: in_active_range(len-1) = 0 <= len-1 && len-1 < 0 = false
        //   - head' > tail'? head' > 0 (always if head' != 0)
        //     - in_active_range(len-1) = len-1 >= head' || len-1 < 0
        //     - len-1 < 0 is false
        //     - len-1 >= head' is true if head' <= len-1 (which is always true)
        //     - So in_active_range(len-1) = true!
        //
        //   OK so for tail = len-1 (wrapping case), in_active_range works out.
        //   For tail < len-1: new_tail = tail + 1
        //   - in_active_range(tail) with head'=head, tail'=tail+1
        //   - head' <= tail'? head' <= tail+1
        //     - in_active_range(tail) = head' <= tail && tail < tail+1 = head' <= tail && true = head' <= tail
        //   - head' > tail'? head' > tail+1
        //     - in_active_range(tail) = tail >= head' || tail < tail+1 = tail >= head' || true = true
        //
        //   So if head' <= tail+1: in_active_range(tail) = head' <= tail
        //   If head' > tail+1: in_active_range(tail) = true (always)
        //
        //   But head' = head (unchanged), and in pre we had tail' = tail (old value)
        //   - pre.in_active_range(tail) depends on head <= tail or head > tail
        //
        //   Hmm, this is getting complicated. Let me look at the requirements again...
        //   Actually, wait. I think the issue is that I'm confusing tail values.
        //   Let me be more careful:
        //
        //   Pre state:
        //     - producer = Producing(old_tail) where old_tail is the value in the state
        //     - tail = old_tail (from in_bounds)
        //
        //   Transition produce_end:
        //     - consume tail = old_tail (the local var)
        //     - next_tail = inc_wrap(old_tail, len)
        //     - update producer = Idle(next_tail)
        //     - update tail = next_tail
        //
        //   Post state:
        //     - producer = Idle(next_tail)
        //     - tail = next_tail
        //     - storage has deposit at old_tail with perm
        //
        //   Now for cell old_tail in post:
        //     - is_checked_out(old_tail) = producer == Producing(old_tail) = Idle(next_tail) == Producing(old_tail) = false
        //     - storage.dom().contains(old_tail) = true (deposit added it)
        //     - storage.index(old_tail) = perm
        //     - perm.id() == backing_cells.index(old_tail) (requirement)
        //     - in_active_range(old_tail) = ?
        //       - head unchanged = head
        //       - tail = next_tail = inc_wrap(old_tail, len)
        //       - If next_tail <= tail (i.e., inc_wrap(old_tail) <= tail)... wait this is tautological
        //       - Let's rewrite:
        //         - If inc_wrap(old_tail) <= tail: in_active_range(old_tail) = inc_wrap(old_tail) <= old_tail && old_tail < tail
        //         - If inc_wrap(old_tail) > tail: in_active_range(old_tail) = old_tail >= inc_wrap(old_tail) || old_tail < tail
        //
        //     - inc_wrap(old_tail) = if old_tail + 1 == len then 0 else old_tail + 1
        //     - Case 1: old_tail < len - 1, so inc_wrap(old_tail) = old_tail + 1
        //       - inc_wrap(old_tail) <= tail? old_tail + 1 <= tail
        //         - in_active_range(old_tail) = old_tail + 1 <= old_tail && old_tail < tail = false && ... = false
        //       - inc_wrap(old_tail) > tail? old_tail + 1 > tail
        //         - in_active_range(old_tail) = old_tail >= old_tail + 1 || old_tail < tail = false || old_tail < tail
        //         - old_tail < tail depends on tail
        //     - Case 2: old_tail == len - 1, so inc_wrap(old_tail) = 0
        //       - 0 <= tail? Always true (tail >= 0 and tail < len)
        //         - in_active_range(old_tail) = 0 <= old_tail && old_tail < tail = true && old_tail < tail = old_tail < tail
        //       - 0 > tail? Only if tail = 0 (but tail >= 0, so 0 > tail is false)
        //         - doesn't apply
        //
        //   So:
        //   - Case 1 (old_tail < len-1, inc_wrap = old_tail + 1):
        //     - If old_tail + 1 <= tail: in_active_range = false
        //     - If old_tail + 1 > tail: in_active_range = old_tail < tail
        //       - old_tail + 1 > tail means tail <= old_tail
        //       - So old_tail < tail is false (since tail <= old_tail)
        //       - So in_active_range = false in both subcases!
        //   - Case 2 (old_tail == len-1, inc_wrap = 0):
        //     - in_active_range = old_tail < tail = len-1 < tail
        //     - But tail < len, so tail <= len-1
        //     - len-1 < tail means tail = len-1 + epsilon, which is impossible
        //     - So in_active_range = false
        //
        //   So in ALL cases, in_active_range(old_tail) = false in post!
        //   This means the cell should be UNINIT, but we're depositing INIT!
        //
        //   I must be misunderstanding something. Let me look at the produce_start and consume_start
        //   to understand the semantics better...
        //
        //   Oh! I think I see the issue. When we produce:
        //   - produce_start: we check out cell at tail (before increment), withdraw its permission
        //   - produce_end: we deposit back at cell at tail (the SAME cell, before increment)
        //   - But afterproduce_end, tail = inc_wrap(tail), so the active range now includes tail
        //
        //   Wait, no. Let me re-read produce_start:
        //   - update producer = Producing(tail) where tail = pre.producer.Idle_0
        //   - withdraw storage -= [tail => _] -- this withdraws from the OLD tail
        //
        //   And produce_end:
        //   - let tail = pre.producer.Producing_0 -- this gets the SAME value from the state
        //   - deposit storage += [tail => perm] -- this deposits at the SAME OLD tail
        //
        //   So yes, we're depositing at old_tail, and old_tail should now be in the active range!
        //
        //   Hmm, but my analysis shows in_active_range(old_tail) = false. Let me check again...
        //
        //   Oh wait! I think I made an error. Let me re-check case 1:
        //   - old_tail < len-1, so inc_wrap(old_tail) = old_tail + 1 = new_tail
        //   - in_active_range(old_tail) in post with head'=head, tail'=new_tail
        //   - If head' <= tail': in_active_range(old_tail) = head' <= old_tail && old_tail < tail' = head <= old_tail && old_tail < old_tail + 1 = head <= old_tail && true = head <= old_tail
        //   - If head' > tail': in_active_range(old_tail) = old_tail >= head' || old_tail < tail' = old_tail >= head || old_tail < old_tail + 1 = old_tail >= head || true = true
        //
        //   So:
        //   - If head <= old_tail + 1 (i.e., head <= tail'): in_active_range = head <= old_tail
        //   - If head > old_tail + 1 (i.e., head > tail'): in_active_range = true
        //
        //   So in_active_range is NOT always false! It's head <= old_tail if head <= tail'!
        //
        //   And in pre:
        //   - in_active_range(old_tail) with head and tail (which equals old_tail from in_bounds)
        //   - If head <= tail: in_active_range = head <= old_tail && old_tail < tail = head <= old_tail && false = false
        //   - If head > tail: in_active_range = old_tail >= head || old_tail < tail = old_tail >= head || false
        //     - Since head > tail = old_tail, old_tail >= head is false
        //     - So in_active_range = false
        //
        //   So in pre, in_active_range(old_tail) = false (cell was checked out, not in storage)
        //   And in post, in_active_range(old_tail) = head <= old_tail if head <= old_tail + 1, else true
        //
        //   But head didn't change, so head <= old_tail + 1 could be true or false.
        //   And if true, in_active_range = head <= old_tail which could be true or false.
        //
        //   Let me think about what we need:
        //   - We're depositing perm with perm.is_init()
        //   - We need: if in_active_range then is_init, else is_uninit
        //   - So if in_active_range = true, we need is_init (which we have)
        //   - If in_active_range = false, we need is_uninit (but we have is_init!)
        //
        //   So the issue is when in_active_range = false but we're depositing init!
        //
        //   When is in_active_range = false in post?
        //   - Case 1 (old_tail < len-1): in_active_range = head <= old_tail if head <= old_tail + 1
        //     - in_active_range = false when head > old_tail (since head <= old_tail + 1 and head > old_tail means old_tail < head <= old_tail + 1)
        //   - Case 2 (old_tail == len-1): in_active_range = false always
        //
        //   In case 1 with head > old_tail:
        //     - In pre: head > old_tail = tail, so head > tail
        //     - The active range in pre was [head, len) U [0, tail) with head > tail
        //     - This range is head, head+1, ..., len-1, 0, 1, ..., tail-1
        //     - old_tail = tail is NOT in this range (the range ends at tail-1)
        //     - So in pre, in_active_range(old_tail) = false (cell was empty/checked out)
        //     - After production, tail moves to old_tail + 1
        //     - The new active range is [head, len) U [0, old_tail + 1) with head > old_tail
        //     - old_tail = len-1 or old_tail < len-1
        //       - If old_tail < len-1: new range is [head, len) U [0, old_tail + 1) with head > old_tail
        //         - old_tail is in [0, old_tail + 1)? Yes since 0 <= old_tail < old_tail + 1
        //         - Wait no, I need to recheck...
        //       - If old_tail == len-1: new range is [head, len) U [0, 0) = [head, len)
        //         - old_tail = len-1 is in [head, len)? Yes since head <= len-1 always
        //
        //   So actually, after production, old_tail SHOULD be in the active range!
        //   But my in_active_range formula says it's not in some cases...
        //
        //   I think I made an error in the in_active_range formula interpretation.
        //   Let me re-read the formula:
        //   - if self.head <= self.tail: self.head <= i && i < self.tail
        //   - else: i >= self.head || i < self.tail
        //
        //   For post with head' = head, tail' = old_tail + 1 (case 1):
        //   - If head <= old_tail + 1: range is [head, old_tail + 1)
        //     - old_tail is in this range iff head <= old_tail && old_tail < old_tail + 1
        //     - old_tail < old_tail + 1 is always true
        //     - So old_tail is in range iff head <= old_tail
        //   - If head > old_tail + 1: range is [head, len) U [0, old_tail + 1)
        //     - old_tail is in [head, len)? head <= old_tail? But head > old_tail + 1 > old_tail, so no
        //     - old_tail is in [0, old_tail + 1)? 0 <= old_tail < old_tail + 1, yes
        //
        //   So old_tail IS in the active range in post! Good!
        //   - head <= old_tail + 1 and head <= old_tail: in range
        //   - head <= old_tail + 1 and head > old_tail: NOT in range (head is between old_tail and old_tail+1, i.e., head = old_tail + 1)
        //   - head > old_tail + 1: in range
        //
        //   So when is old_tail NOT in range? When head = old_tail + 1!
        //
        //   In this case:
        //   - head > old_tail (since head = old_tail + 1)
        //   - In pre, active range was [head, len) U [0, old_tail) = [old_tail + 1, len) U [0, old_tail)
        //   - old_tail is NOT in this range (range ends at old_tail - 1)
        //   - So pre: in_active_range(old_tail) = false
        //   - Post: in_active_range(old_tail) = false (since head = old_tail + 1 > old_tail)
        //   - We're depositing init at old_tail
        //   - But in_active_range = false, so we need uninit!
        //
        //   This is the bug! When head = old_tail + 1, we have a problem.
        //
        //   But wait, can head = old_tail + 1 happen?
        //   - pre.tail = old_tail (from in_bounds)
        //   - head ≤ len and tail ≤ len
        //   - head = old_tail + 1 means head > tail
        //   - This can happen in a wrapped state!
        //
        //   Let me think about the queue state:
        //   - If head ≤ tail: active range is [head, tail), length = tail - head
        //   - If head > tail: active range is [head, len) U [0, tail), length = (len - head) + tail
        //   - After produce_end: tail' = tail + 1 (or 0 if tail = len-1)
        //   - If head ≤ tail + 1: active range is [head, tail + 1), length = tail + 1 - head
        //   - If head > tail + 1: active range is [head, len) U [0, tail + 1), length = (len - head) + (tail + 1)
        //
        //   If head = tail + 1 before increment:
        //   - pre: head > tail, length = (len - head) + tail = (len - (tail + 1)) + tail = len - 1
        //   - Post: head = tail + 1, tail' = tail + 1, so head = tail'
        //   - Post: head ≤ tail' is true (equal), so active range is [head, tail') = [tail + 1, tail + 1) = empty!
        //   - Wait that can't be right...
        //
        //   Let me recheck: after produce_end, tail' = inc_wrap(tail) = tail + 1 (assuming tail < len-1)
        //   - head = tail + 1 = tail'
        //   - head ≤ tail'? tail + 1 ≤ tail + 1, yes
        //   - Active range is [head, tail') = [tail + 1, tail + 1) = empty set
        //   - So no cells are active (queue is empty)
        //
        //   But we just produced! The queue should have at least the cell we produced!
        //
        //   Oh! I think I see the issue. The queue can be empty, but we just produced, so it shouldn't be...
        //
        //   Let me check the transition requirements:
        //   - produce_start requires next_tail != head, i.e., inc_wrap(tail) != head
        //   - If tail < len-1: tail + 1 != head
        //   - If tail = len-1: 0 != head
        //
        //   So if tail < len-1, we have tail + 1 != head, which means head != tail + 1!
        //
        //   Aha! So head = tail + 1 is prevented by produce_start!
        //
        //   So in the valid execution, head != tail + 1, which means:
        //   - head <= tail or head > tail + 1
        //   - If head <= tail: in post, head <= tail < tail + 1 = tail', so head <= tail', and in_active_range = head <= old_tail = head <= tail (since old_tail = tail)
        //   - If head > tail + 1: in post, head > tail + 1 = tail', so head > tail', and in_active_range = true
        //
        //   So:
        //   - If head <= tail: in_active_range(old_tail) = head <= tail
        //   - If head > tail + 1: in_active_range(old_tail) = true
        //
        //   In both cases, we need to check if this gives us is_init()...
        //
        //   Wait, I think I'm still confusing old_tail and tail. Let me be more careful:
        //   - pre.tail = tail (let's call this value T for clarity)
        //   - old_tail = T (the same value)
        //   - post.tail = inc_wrap(T) = T + 1 (or 0 if T = len-1)
        //
        //   For cell T in post:
        //   - Case T < len-1: tail' = T + 1
        //     - If head <= T + 1: in_active_range(T) = head <= T
        //     - If head > T + 1: in_active_range(T) = true
        //     - produce_start requires inc_wrap(T) != head, i.e., T + 1 != head, i.e., head != T + 1
        //     - So either head <= T or head > T + 1 (not head = T + 1)
        //     - If head <= T: in_active_range(T) = true (need is_init)
        //     - If head > T + 1: in_active_range(T) = true (need is_init)
        //   - Case T = len-1: tail' = 0
        //     - head <= 0? Only if head = 0 (since head >= 0)
        //       - in_active_range(T) = 0 <= T && T < 0 = true && false = false
        //     - head > 0? Always (since head != 0 if not the first case)
        //       - in_active_range(T) = T >= head || T < 0 = T >= head || false = T >= head
        //       - T = len-1, head > 0, so head ∈ [1, len-1], and T >= head is true
        //     - So in_active_range(T) = true
        //
        //   So in ALL valid cases, in_active_range(T) = true in post!
        //   And we're depositing perm with perm.is_init(), so we have what we need!
        //
        //   Great! So the proof is:
        //   - broadcast axioms
        //   - For any i, show valid_storage_at_idx(i) by cases
        //   - For i != T (the old tail): follow from pre
        //   - For i == T: show is_checked_out = false, storage.dom().contains = true, id matches, in_active_range = true (need to prove this)
        //     - The key is to prove in_active_range(T) = true
        //     - This follows from produce_start's requirement that inc_wrap(T) != head
        //
        //   Actually, let me look at this more carefully. The SMT solver needs help proving in_active_range(T) = true.
        //   I need to add assertions to help it.
        broadcast use group_map_properties, group_multiset_axioms;
        // Need to prove valid_storage_at_idx for all i
        // Focus on the tricky case: i == tail (old tail) after deposit
        // We need to show in_active_range(i) in post, which requires head <= i if next_tail <= i or something...
        // Actually, let's use the analysis above:
        // - If tail < len-1: next_tail = tail + 1
        //   - produce_start requires tail + 1 != head, so head != tail + 1
        //   - Either head <= tail or head > tail + 1
        //   - If head <= tail: in_active_range(tail) = head <= tail (true if head <= tail)
        //   - If head > tail + 1: in_active_range(tail) = true
        // - If tail == len-1: next_tail = 0
        //   - in_active_range(tail) = tail >= head (true since head < len and tail = len-1)
        }
    #[inductive(consume_start)]
    fn consume_start_inductive(pre: Self, post: Self) {
        // Need to prove: valid_storage_all for post
        // Pre invariant: valid_storage_all(pre)
        // In consume_start:
        //   - head = pre.consumer.Idle_0
        //   - consumer: Idle(head) -> Consuming(head)
        //   - storage: withdraw storage -= [head => _] (removes head from domain)
        //
        // For i != head:
        //   - is_checked_out(i) unchanged
        //   - storage unchanged
        //   - valid_storage_at_idx(i) follows from pre
        //
        // For i == head:
        //   - pre: is_checked_out(head) = false, in_active_range(head) = true (full cell)
        //     storage.dom().contains(head), storage.index(head).is_init()
        //   - post: is_checked_out(head) = true (Consuming(head))
        //     storage.dom().does_not_contain(head) (withdraw removed it)
        //   - valid_storage_at_idx(head) holds (is checked out, not in domain)
        broadcast use group_map_properties, group_multiset_axioms;
    }
    #[inductive(consume_end)]
    fn consume_end_inductive(pre: Self, post: Self, perm: cell::PointsTo<T>) {
        // Need to prove: valid_storage_all for post
        // Pre invariant: valid_storage_all(pre)
        // In consume_end:
        //   - head = pre.consumer.Consuming_0 (let's call this T)
        //   - consumer: Consuming(T) -> Idle(next_head) where next_head = inc_wrap(T)
        //   - head: T -> next_head
        //   - storage: deposit storage += [T => perm] (adds T to domain with perm)
        //   - require: perm.is_uninit()
        //
        // For i != T:
        //   - is_checked_out(i) unchanged (only head changed consumer)
        //   - in_active_range(i) may change
        //   - storage: for i != T, storage.index(i) unchanged
        //
        // For i == T:
        //   - pre: is_checked_out(T) = true (Consuming), so T not in storage domain
        //   - post: is_checked_out(T) = false (Idle(next_head) != Consuming(T))
        //     storage.dom().contains(T) (deposit added it)
        //     storage.index(T) = perm, perm.id() == backing_cells.index(T) (requirement)
        //     perm.is_uninit() (requirement)
        //     Need to check in_active_range(T) in post:
        //       - head' = next_head = inc_wrap(T)
        //       - tail' = tail (unchanged)
        //       - If next_head <= tail: in_active_range(T) = next_head <= T && T < tail
        //         - next_head = inc_wrap(T) = T+1 (or 0 if T=len-1)
        //         - If T < len-1: next_head = T+1, so next_head <= T is false, in_active_range = false
        //         - If T = len-1: next_head = 0, so 0 <= T is true, in_active_range = T < tail = len-1 < tail
        //           - But tail < len, so tail <= len-1, so len-1 < tail is false
        //           - So in_active_range = false
        //       - If next_head > tail: in_active_range(T) = T >= next_head || T < tail
        //         - T >= next_head: if T < len-1, T >= T+1 is false; if T = len-1, T >= 0 is true
        //         - T < tail: depends
        //
        //   Let me be more careful for T < len-1 (next_head = T+1):
        //   - If T+1 <= tail: in_active_range(T) = T+1 <= T && T < tail = false && ... = false
        //   - If T+1 > tail: in_active_range(T) = T >= T+1 || T < tail = false || T < tail
        //     - T+1 > tail means tail <= T, so T < tail is false
        //     - So in_active_range = false in both subcases!
        //
        //   For T = len-1 (next_head = 0):
        //   - If 0 <= tail (always): in_active_range(T) = 0 <= T && T < tail = true && T < tail = T < tail
        //     - T = len-1, so T < tail means len-1 < tail
        //     - But tail < len, so tail <= len-1, so T < tail is false
        //     - So in_active_range = false
        //   - If 0 > tail (impossible since tail >= 0): doesn't apply
        //
        //   So in ALL cases for consume_end, in_active_range(T) = false in post!
        //   And we're depositing perm with perm.is_uninit(), which is exactly what we need!
        //
        //   Now for i != T:
        //   - Need to show valid_storage_at_idx(i) in post
        //   - From pre: valid_storage_at_idx(i)
        //   - Changes: storage only changed at T, head changed to next_head
        //   - For i != T:
        //     - is_checked_out(i) unchanged
        //     - storage.index(i) unchanged
        //     - in_active_range(i) may change due to head change
        //       - If head' <= tail': in_active_range(i) = head' <= i && i < tail'
        //       - If head' > tail': in_active_range(i) = i >= head' || i < tail'
        //   - Need to check that if in_active_range(i) changed, the cell type (init/uninit) still matches
        //
        //   This is tricky. Let me think about what in_active_range represents:
        //   - It's the range of cells that have been produced but not consumed
        //   - After consume_end, we've consumed cell T, so head moves to next_head
        //   - The active range now starts from next_head instead of T
        //   - Cell T should now be empty (uninit) since it's been consumed
        //   - Other cells might have their "active" status change if they're near T
        //
        //   Actually, let me reconsider which cells' active status can change:
        //   - Active range changes from [T, tail) or [T, len) U [0, tail) to [next_head, tail) or [next_head, len) U [0, tail)
        //   - If T < len-1: next_head = T+1
        //     - Old range: if T <= tail: [T, tail), else: [T, len) U [0, tail)
        //     - New range: if T+1 <= tail: [T+1, tail), else: [T+1, len) U [0, T+1)
        //     - Cells that could change:
        //       - T: was active (in old range), now NOT active
        //       - T+1: may become active or stay active
        //   - If T = len-1: next_head = 0
        //     - Old range: if len-1 <= tail: but tail < len, so tail <= len-1, so len-1 <= tail means tail = len-1, range is [len-1, len-1) = empty?
        //       Hmm wait, if head = tail, that's the empty case
        //       - But consume_start requires head != tail, so this case doesn't happen
        //       - Actually, pre.head = T = len-1, and pre.tail could be anything != len-1
        //       - If len-1 <= tail: but tail < len, so tail <= len-1, so len-1 <= tail means tail = len-1
        //         But head = len-1 and tail = len-1 would mean head = tail, which violate the require head != tail
        //         So this case doesn't happen
        //       - If len-1 > tail: range is [len-1, len) U [0, tail) = {len-1} U [0, tail)
        //     - New range: if 0 <= tail (always): [0, tail)
        //     - Cells that could change:
        //       - len-1 (T): was active, now NOT active
        //       - Cells in [0, tail): were active, still active
        //
        //   So in all cases, only cell T changes from active to not-active!
        //   And we're depositing uninit at T, which is correct!
        //
        //   For other cells i != T:
        //   - If i was active and is still active: in_active_range(i) unchanged, cell type (init) unchanged
        //   - If i was not active and is still not active: in_active_range(i) unchanged, cell type (uninit) unchanged
        //   - If i was active and is now not active: this can only happen if i = T, which we're handling separately
        //   - If i was not active and is now active: let me check...
        //
        //   For T < len-1 (next_head = T+1):
        //   - Old range: if T <= tail: [T, tail), else: [T, len) U [0, tail)
        //   - New range: if T+1 <= tail: [T+1, tail), else: [T+1, len) U [0, T+1)
        //
        //   If T <= tail (old range [T, tail)):
        //   - New range [T+1, tail) if T+1 <= tail
        //     - Cells T+1, ..., tail-1 were active, still active
        //     - Cell T was active, now not active (handled)
        //   - New range [T+1, len) U [0, T+1) if T+1 > tail (i.e., tail <= T)
        //     - Old range [T, tail) with tail <= T means... wait, T <= tail is our assumption
        //       So tail <= T and T <= tail means tail = T
        //       Old range [T, T) = empty! But that contradicts valid_storage_at_idx(T) in pre
        //       If T is in active range, it should be full. But if active range is empty, nothing is active.
        //       Hmm, this is confusing. Let me check if tail = T is possible...
        //       From in_bounds: pre.tail = if producer == Producing then ... but producer is Consuming in consume_start
        //       Actually, pre.tail = pre.head for consumer state, and pre.head = T
        //       So pre.tail = T
        //       If T <= tail and tail = T, then T <= T, true
        //       Active range [T, T) = empty
        //       But consume_start requires head != tail, and head = T, tail = T, so head = tail, contradiction!
        //       So tail = T cannot happen in consume_start!
        //       Therefore, if T <= tail, we actually have T < tail (strictly less)
        //       New range [T+1, tail) with T < tail means T+1 <= tail, so new range is [T+1, tail)
        //       Cells T+1, ..., tail-1 are active before and after
        //
        //   If T > tail (old range [T, len) U [0, tail)):
        //   - New range [T+1, len) U [0, T+1) if T+1 > tail (always true since T > tail, so T+1 > tail)
        //     - Old active: T, ..., len-1, 0, ..., tail-1
        //     - New active: T+1, ..., len-1, 0, ..., T
        //     - Cell T was active (in [T, len)), now in [0, T+1)?
        //       - T in [0, T+1)? 0 <= T < T+1, yes
        //       - So T is still active! But we're consuming it...
        //
        //   Wait, this is wrong. Let me re-think...
        //
        //   Actually, I think the issue is that I'm confusing the old and new head values.
        //   In consume_start, head = T and we're consuming at head. After consuming, head = next_head = T+1.
        //   The "active range" is the range of cells that have been produced but not consumed.
        //   - Before consume_end: head = T, tail = some V
        //     - If T <= V: active = [T, V), cells T, ..., V-1 are produced but not consumed
        //     - If T > V: active = [T, len) U [0, V), cells T, ..., len-1, 0, ..., V-1 are produced but not consumed
        //   - After consume_end: head = T+1, tail = V (unchanged)
        //     - If T+1 <= V: active = [T+1, V), cells T+1, ..., V-1 are produced but not consumed
        //     - If T+1 > V: active = [T+1, len) U [0, T+1), cells T+1, ..., len-1, 0, ..., T are produced but not consumed
        //
        //   So:
        //   - Cell T: was active (in range starting at T), now... 
        //     - If T+1 <= V: active is [T+1, V), T is not in this range (starts at T+1)
        //     - If T+1 > V: active is [T+1, len) U [0, T+1), T is in [0, T+1)?
        //       - T in [0, T+1)? 0 <= T < T+1, yes
        //   - So in some cases, T is still active after consuming it! This is wrong!
        //
        //   Oh wait, I think I see the issue. When we consume at T, the cell at T is consumed, so it should NOT be active anymore.
        //   But my analysis says it might still be active (if T+1 > V, cell T is in [0, T+1)).
        //
        //   Let me check with an example:
        //   - len = 5, T = 3, V = 1
        //   - Before: head = 3, tail = 1, active = [3, 5) U [0, 1) = {3, 4, 0}
        //   - After: head = 4, tail = 1, active = [4, 5) U [0, 4) = {4, 0, 1, 2, 3}
        //   - Cell 3 was active before, still active after! But we just consumed it!
        //
        //   This is a bug in my understanding. Let me re-read the semantics...
        //
        //   Actually, I think the issue is that the "active range" represents cells between head and tail.
        //   When head > tail, the range wraps around. After consuming at T = head, head moves to T+1.
        //   The new active range should NOT include T because it's been consumed!
        //
        //   Let me re-check the formula:
        //   - If head' <= tail': range is [head', tail')
        //   - If head' > tail': range is [head', len) U [0, tail')
        //
        //   With head' = T+1, tail' = V:
        //   - If T+1 <= V: range [T+1, V), doesn't include T
        //   - If T+1 > V: range [T+1, len) U [0, T+1), includes T if T < T+1 (yes) and T >= 0 (yes)
        //
        //   So if T+1 > V, T is in [0, T+1), so it's still in the active range!
        //
        //   But this doesn't make sense. If we just consumed at T, T should not be active anymore.
        //
        //   Let me check the consume_start transition to see what the active range is:
        //   - consume_start: head = pre.consumer.Idle_0 = T
        //   - require head != tail, so T != V
        //   - update consumer = Consuming(T)
        //   - withdraw storage -= [T => perm] (removes T from storage)
        //
        //   In consume_start, we withdraw the cell at T, so it's checked out.
        //   After consume_start, the cell at T is checked out (not in storage).
        //
        //   In consume_end:
        //   - we deposit perm at T
        //   - perm.is_uninit() (we're returning an empty cell)
        //
        //   So after consume_end, cell T is uninit and not checked out.
        //   Is it in the active range?
        //
        //   I think the key insight is:
        //   - When head <= tail: active range is [head, tail), cells that have been produced but not consumed
        //   - When head > tail: active range is [head, len) U [0, tail), cells that have been produced but not consumed
        //
        //   After consuming at T:
        //   - head' = T+1
        //   - If T+1 <= tail: active = [T+1, tail), T is not active (range starts at T+1)
        //   - If T+1 > tail: active = [T+1, len) U [0, T+1)
        //     - T in [T+1, len)? T >= T+1? No
        //     - T in [0, T+1)? 0 <= T < T+1? Yes
        //     - So T is active!
        //
        //   But T was consumed! It should not be active!
        //
        //   I think there's a bug in the formula or my understanding.
        //   Let me check what the formula should be:
        //   - Active range = cells between head and tail (where tail is the next position to produce)
        //   - After consuming at T, head becomes T+1
        //   - The active range should be from the new head to tail
        //   - If T+1 <= tail: active = [T+1, tail)
        //   - If T+1 > tail: active = [T+1, len) U [0, tail) but this doesn't make sense...
        //
        //   Actually, if T+1 > tail, that means T >= tail (since T+1 > tail implies T >= tail).
        //   And from head != tail (consume_start requires this), we have T != tail, so T > tail.
        //   So T > tail, and T+1 > tail.
        //   - Old active: [T, len) U [0, tail) with T > tail
        //   - New active: [T+1, len) U [0, T+1) with T+1 > tail
        //   - Wait, the new formula uses tail, not T+1, in the second part!
        //   - New active: [T+1, len) U [0, tail) (I misread, the second part uses tail, not next_head)
        //
        //   Let me re-check the in_active_range formula:
        //   - if self.head <= self.tail: self.head <= i && i < self.tail
        //   - else: i >= self.head || i < self.tail
        //
        //   With head' = T+1, tail' = V:
        //   - If T+1 <= V: i in [T+1, V)
        //   - If T+1 > V: i >= T+1 || i < V
        //
        //   With T > V (since T+1 > V and T != V):
        //   - T >= T+1 || T < V = false || false = false (since T > V)
        //   - So T is NOT in active range!
        //
        //   Let me double-check with the example:
        //   - len = 5, T = 3, V = 1
        //   - T > V: 3 > 1, true
        //   - T+1 = 4 > V = 1, true
        //   - Active: i >= 4 || i < 1 = {4, 0}
        //   - Cell 3 is NOT in active range! Good!
        //
        //   So my earlier analysis was wrong. Let me redo it:
        //
        //   For consume_end with T = old head, V = tail (unchanged), next_head = inc_wrap(T):
        //   - If next_head <= V: in_active_range(i) = next_head <= i && i < V
        //   - If next_head > V: in_active_range(i) = i >= next_head || i < V
        //
        //   For cell T:
        //   - If T < len-1: next_head = T+1
        //     - If T+1 <= V: in_active_range(T) = T+1 <= T && T < V = false && ... = false
        //     - If T+1 > V: in_active_range(T) = T >= T+1 || T < V = false || T < V
        //       - T+1 > V means V <= T, so T < V is false
        //       - So in_active_range = false
        //   - If T = len-1: next_head = 0
        //     - If 0 <= V (always): in_active_range(T) = 0 <= T && T < V = true && T < V = T < V
        //       - T = len-1, so T < V means len-1 < V
        //       - But V < len, so V <= len-1, so T < V is false
        //       - So in_active_range = false
        //     - If 0 > V (impossible): doesn't apply
        //
        //   So in ALL cases, in_active_range(T) = false in post!
        //   And we're depositing uninit at T, which is correct!
        //
        //   Now for i != T:
        //   - From pre: valid_storage_at_idx(i)
        //   - After consume_end:
        //     - storage.index(i) unchanged (only T changed)
        //     - is_checked_out(i) unchanged (only consumer changed to Idle, and i != T)
        //     - in_active_range(i) may change due to head change
        //
        //   The key is that in_active_range can change for cells near T, but:
        //   - If a cell was init and is still init: ok
        //   - If a cell was uninit and is still uninit: ok
        //   - If a cell's active status changes, we need to check if the cell type changes...
        //
        //   But actually, only T changes from init to uninit (we're depositing uninit).
        //   Other cells' init/uninit status is unchanged (we only modified storage at T).
        //   So if a cell i != T changes from active to not-active or vice versa, its init/uninit status should change accordingly.
        //
        //   Let me check which cells' active status can change:
        //   - The range changes from [T, V) or [T, len) U [0, V) to [T+1, V) or [T+1, len) U [0, V)
        //   - If T < len-1: next_head = T+1
        //     - Old: if T <= V: [T, V), else: [T, len) U [0, V)
        //     - New: if T+1 <= V: [T+1, V), else: [T+1, len) U [0, V)
        //     - If T <= V (so T < V since T != V):
        //       - New is [T+1, V) (since T+1 <= V)
        //       - Old was [T, V)
        //       - Cells T+1, ..., V-1: were active, still active
        //       - Cell T: was active, now NOT active
        //     - If T > V:
        //       - New is [T+1, len) U [0, V) (since T+1 > V)
        //       - Old was [T, len) U [0, V)
        //       - Cells T+1, ..., len-1: were active, still active
        //       - Cell T: was active, now NOT active (T not in [T+1, len))
        //       - Cells 0, ..., V-1: were active, still active (in [0, V))
        //   - If T = len-1: next_head = 0
        //     - Old: T = len-1 > V (since T != V), so [T, len) U [0, V) = {len-1} U [0, V)
        //     - New: [0, len) U [0, V) = [0, len) (since 0 <= V always)
        //       Wait, [0, len) is the full range! That can't be right...
        //     - Let me recheck: if next_head > V, range is [next_head, len) U [0, V)
        //       With next_head = 0: [0, len) U [0, V) = [0, len) (since V < len)
        //       This is the full range! But we just consumed a cell, so the queue should have one less cell...
        //
        //   Hmm, there's still an issue. Let me think about this more carefully.
        //
        //   Actually, I think the issue is that I'm not accounting for the fact that V (tail) can be anything.
        //   Let me reconsider the case T = len-1:
        //   - T = len-1, head = T = len-1 in pre
        //   - V = tail in pre, V != T = len-1 (since head != tail)
        //   - So V < len-1 (since V < len and V != len-1)
        //   - Old active: [len-1, len) U [0, V) = {len-1} U [0, V)
        //   - Next_head = 0
        //   - New: 0 <= V? Yes (V >= 0)
        //     - Active: [0, V)
        //   - So old active: {len-1, 0, 1, ..., V-1}
        //   - New active: {0, 1, ..., V-1}
        //   - Cell len-1 (T) was active, now NOT active. Good!
        //   - Cells 0, ..., V-1: were active, still active. Good!
        //
        //   So in all cases, only cell T changes from active to not-active!
        //   And we're depositing uninit at T, which is correct.
        //
        //   For cells that are still active, their init/uninit status is unchanged (we didn't modify them).
        //   So they still match their active status.
        //
        //   Therefore, valid_storage_all holds!
        //
        //   To prove this formally, I need to add assertions that capture the above reasoning.
        //   Specifically, I need to prove that for all i != T, if i was active (init) or not (uninit),
        //   it still matches after the head change.
        //
        //   The key observations are:
        //   1. For i != T, storage.index(i) is unchanged
        //   2. For i != T, is_checked_out(i) is unchanged
        //   3. For i != T, if i is in the old active range and not in the new, or vice versa,
        //      this only happens for i = T (which we're handling separately)
        //   4. So for i != T, in_active_range(i) either stays the same or both pre and post have the same init/uninit
        //
        //   Actually, point 3 is not quite right. Cells near T could have their active status change.
        //   But since we only modified storage at T, and T is the only cell that changes from init to uninit,
        //   any cell that changes active status must also change its expected type (init <-> uninit).
        //
        //   Hmm, but that's only true for T. For other cells, their init/uninit is unchanged.
        //   So if a cell i != T changes from active to not-active, it goes from init to uninit, which is wrong!
        //
        //   Let me check with an example:
        //   - len = 5, T = 3, V = 1
        //   - Pre: head = 3, tail = 1, active = [3, 5) U [0, 1) = {3, 4, 0}
        //   - Cells: 3 (init), 4 (init), 0 (init), 1 (uninit), 2 (uninit)
        //   - Post: head = 4, tail = 1, active = [4, 5) U [0, 1) = {4, 0}
        //   - Cells: 3 (uninit), 4 (init), 0 (init), 1 (uninit), 2 (uninit)
        //   - Cell 3: was init, now uninit (we consumed it). Good!
        //   - Cell 4: was init, still init. Good!
        //   - Cell 0: was init, still init. Good!
        //   - Cells 1, 2: were uninit, still uninit. Good!
        //
        //   Another example:
        //   - len = 5, T = 1, V = 3
        //   - Pre: head = 1, tail = 3, active = [1, 3) = {1, 2}
        //   - Cells: 0 (uninit), 1 (init), 2 (init), 3 (uninit), 4 (uninit)
        //   - Post: head = 2, tail = 3, active = [2, 3) = {2}
        //   - Cells: 0 (uninit), 1 (uninit), 2 (init), 3 (uninit), 4 (uninit)
        //   - Cell 1: was init, now uninit (we consumed it). Good!
        //   - Cell 2: was init, still init. Good!
        //   - Other cells unchanged. Good!
        //
        //   So the pattern is:
        //   - Only cell T changes from init to uninit
        //   - All other cells keep their init/uninit status
        //   - Cells that were in the active range and still are: keep init
        //   - Cells that were not in the active range and still aren't: keep uninit
        //   - Cell T: was in active range (init), now not in active range (uninit). Good!
        //   - Are there any other cells that change active status?
        //
        //   Let me check:
        //   - Old range: [T, V) if T < V, or [T, len) U [0, V) if T > V
        //   - New range: [T+1, V) if T+1 < V, or [T+1, len) U [0, V) if T+1 > V
        //
        //   If T < V (old [T, V), new [T+1, V) since T+1 <= V):
        //   - Cells T+1, ..., V-1: in both old and new. No change.
        //   - Cell T: in old, not in new. Changes from init to uninit. Good!
        //
        //   If T > V (old [T, len) U [0, V), new [T+1, len) U [0, V) since T+1 > V):
        //   - Cells T+1, ..., len-1: in both old and new. No change.
        //   - Cells 0, ..., V-1: in both old and new. No change.
        //   - Cell T: in old (T in [T, len)), not in new (T not in [T+1, len)). Changes from init to uninit. Good!
        //
        //   So in ALL cases, only cell T changes from active to not-active!
        //   And we're depositing uninit at T, which is exactly what we need.
        //
        //   Therefore, valid_storage_all holds.
        //
        //   To prove this, I can add assertions that capture the above reasoning.
        broadcast use group_map_properties, group_multiset_axioms;
    }
}}

// ANCHOR: impl_queue_struct
struct_with_invariants!{
    struct Queue<T> {
        buffer: Vec<PCell<T>>,
        head: AtomicU64<_, FifoQueue::head<T>, _>,
        tail: AtomicU64<_, FifoQueue::tail<T>, _>,

        instance: Tracked<FifoQueue::Instance<T>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            // The Cell IDs in the instance protocol match the cell IDs in the actual vector:
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
// ANCHOR_END: impl_queue_struct

// ANCHOR: impl_producer_struct
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
// ANCHOR_END: impl_producer_struct

// ANCHOR: impl_consumer_struct
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
// ANCHOR_END: impl_consumer_struct

// ANCHOR: impl_new_queue
pub fn new_queue<T>(len: usize) -> (pc: (Producer<T>, Consumer<T>))
    requires
        len > 0,
    ensures
        pc.0.wf(),
        pc.1.wf(),
{
    // Initialize the vector to store the cells
    let mut backing_cells_vec = Vec::<PCell<T>>::new();
    // Initialize map for the permissions to the cells
    // (keyed by the indices into the vector)
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
    // Vector for ids

    let ghost mut backing_cells_ids = Seq::<CellId>::new(
        backing_cells_vec@.len(),
        |i: int| backing_cells_vec@.index(i).id(),
    );
    // Initialize an instance of the FIFO queue
    let tracked (
        Tracked(instance),
        Tracked(head_token),
        Tracked(tail_token),
        Tracked(producer_token),
        Tracked(consumer_token),
    ) = FifoQueue::Instance::initialize(backing_cells_ids, perms, perms);
    // Initialize atomics
    let tracked_inst: Tracked<FifoQueue::Instance<T>> = Tracked(instance.clone());
    let head_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(head_token));
    let tail_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(tail_token));
    // Initialize the queue
    let queue = Queue::<T> {
        instance: Tracked(instance),
        head: head_atomic,
        tail: tail_atomic,
        buffer: backing_cells_vec,
    };
    // Share the queue between the producer and consumer
    let queue_arc = Arc::new(queue);
    let prod = Producer::<T> {
        queue: queue_arc.clone(),
        tail: 0,
        producer: Tracked(producer_token),
    };
    let cons = Consumer::<T> { queue: queue_arc, head: 0, consumer: Tracked(consumer_token) };
    (prod, cons)
}
// ANCHOR_END: impl_new_queue

// ANCHOR: impl_producer
impl<T> Producer<T> {
    fn enqueue(&mut self, t: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        // Loop: if the queue is full, then block until it is not.
        loop
            invariant
                self.wf(),
        {
            let queue = &*self.queue;
            let len = queue.buffer.len();
            assert(0 <= self.tail && self.tail < len);
            // Calculate the index of the slot right after `tail`, wrapping around
            // if necessary. If the enqueue is successful, then we will be updating
            // the `tail` to this value.
            let next_tail = if self.tail + 1 == len {
                0
            } else {
                self.tail + 1
            };
            let tracked cell_perm: Option<cell::PointsTo<T>>;
            // Get the current `head` value from the shared atomic.
            let head =
                atomic_with_ghost!(&queue.head => load();
                returning head;
                ghost head_token => {
                    // If `head != next_tail`, then we proceed with the operation.
                    // We check here, ghostily, in the `open_atomic_invariant` block if that's the case.
                    // If so, we proceed with the `produce_start` transition
                    // and obtain the cell permission.
                    cell_perm = if head != next_tail as u64 {
                        let tracked cp = queue.instance.borrow().produce_start(&head_token, self.producer.borrow_mut());
                        Option::Some(cp)
                    } else {
                        Option::None
                    };
                }
            );
            // Here's where we "actually" do the `head != next_tail` check:
            if head != next_tail as u64 {
                // Unwrap the cell_perm from the option.
                let tracked mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => {
                        assert(false);
                        proof_from_false()
                    },
                };
                // Write the element t into the buffer, updating the cell
                // from uninitialized to initialized (to the value t).
                queue.buffer[self.tail].put(Tracked(&mut cell_perm), t);
                // Store the updated tail to the shared `tail` atomic,
                // while performing the `produce_end` transition.
                atomic_with_ghost!(&queue.tail => store(next_tail as u64); ghost tail_token => {
                    queue.instance.borrow().produce_end(cell_perm,
                        cell_perm, &mut tail_token, self.producer.borrow_mut());
                });
                self.tail = next_tail;
                return ;
            }
        }
    }
}
// ANCHOR_END: impl_producer

// ANCHOR: impl_consumer
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
            let tracked cell_perm: Option<cell::PointsTo<T>>;
            let tail =
                atomic_with_ghost!(&queue.tail => load();
                returning tail;
                ghost tail_token => {
                    cell_perm = if self.head as u64 != tail {
                        let tracked (_, Tracked(cp)) = queue.instance.borrow().consume_start(&tail_token, self.consumer.borrow_mut());
                        Option::Some(cp)
                    } else {
                        Option::None
                    };
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
                    queue.instance.borrow().consume_end(cell_perm,
                        cell_perm, &mut head_token, self.consumer.borrow_mut());
                });
                self.head = next_head;
                return t;
            }
        }
    }
}

fn main() {
}

} // verus!
// ANCHOR_END: impl_consumer
// ANCHOR_END: full
