// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Self-contained adaptation of verified-node-replication/src/spec/cyclicbuffer.rs.
// All dependencies required by the cyclic-buffer specification are inlined below.

fn main() {}

#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::*;
use vstd::cell::{CellId, PointsTo};
use vstd::prelude::*;

verus! {

pub type NodeId = nat;
pub type LogIdx = nat;

#[verus::trusted]
pub trait Dispatch: Sized {
    type WriteOperation: Sized + Send;
}

pub tracked struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
}

pub struct ConcreteLogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: u64,
}

pub open const LOG_SIZE: usize = 512 * 1024;

pub open spec fn map_contains_value<K, V>(map: Map<K, V>, val: V) -> bool {
    exists|i: K| #[trigger] map.contains_key(i) && map.index(i) == val
}

#[verifier(nonlinear)]
#[verifier::external_body]
pub proof fn int_mod_less_than_same(i: int, len: int)
    requires 0 <= i < len, len > 0,
    ensures (i % len) == i,
{ unimplemented!() }

}

// Minimal interface inlined from spec/unbounded_log.rs. CyclicBuffer only uses
// UnboundedLog::Instance and the sharded log entry projection.
tokenized_state_machine! {
UnboundedLog<DT: Dispatch> {
    fields {
        #[sharding(map)]
        pub log: Map<LogIdx, LogEntry<DT>>,
    }

    init! {
        initialize() {
            init log = Map::empty();
        }
    }
}
}

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Cyclic Buffer
// =============
//
// The cyclic buffer is a bounded log with multiple readers and writers. A writer will check whether
// there's enough space in the log and the reserve space to place its update operations into the log.
// Log space can be reclaimed once all readers have advanced their read pointers accordingly.
//
////////////////////////////////////////////////////////////////////////////////////////////////////

verus! {

/// Logical Log Index
///
/// In contrast to the unbounded log, the log entries can be "negative". This is used for the
/// initialization where all entries are initialized with the range [-LOG_SIZE, 0)
pub type LogicalLogIdx = int;

/// The size of the log. XXX: can we get rid of this?

/// An entry in the log
///
///
pub tracked struct StoredType<DT: Dispatch> {
    pub cell_perms: PointsTo<Option<ConcreteLogEntry<DT>>>,
    pub log_entry: Option<UnboundedLog::log<DT>>,
}

pub open spec fn stored_type_inv<DT: Dispatch>(
    st: StoredType<DT>,
    idx: int,
    cell_id: CellId,
    unbounded_log_instance: UnboundedLog::Instance<DT>,
) -> bool {
    // also match the cell id
    &&& st.cell_perms.mem_contents().is_init()
    &&& st.cell_perms@.pcell == cell_id
    &&& idx >= 0 ==> {
        &&& st.log_entry matches Some(log_entry)
        &&& log_entry.key() == idx
        &&& log_entry.instance_id() == unbounded_log_instance.id()
        &&& st.cell_perms.mem_contents().value() matches Some(cell_perms_value)
        &&& cell_perms_value.node_id as NodeId
            == log_entry.value().node_id
        &&& cell_perms_value.op == log_entry.value().op
    }
    &&& idx < 0 ==> {
        &&& true
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Read Only Operations
////////////////////////////////////////////////////////////////////////////////////////////////////
///
#[is_variant]
pub tracked enum ReaderState<DT: Dispatch> {
    ///
    Starting {
        ///
        start: LogIdx,
    },
    /// reader in the range
    Range { start: LogIdx, end: LogIdx, cur: LogIdx },
    /// Guard
    Guard { start: LogIdx, end: LogIdx, cur: LogIdx, val: StoredType<DT> },
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Combiner
////////////////////////////////////////////////////////////////////////////////////////////////////
/// represents the combiner
#[is_variant]
pub tracked enum CombinerState<DT: Dispatch> {
    Idle,
    Reading(ReaderState<DT>),
    AdvancingHead { idx: LogIdx, min_local_version: LogIdx },
    AdvancingTail { observed_head: LogIdx },
    Appending { cur_idx: LogIdx, tail: LogIdx },
}

impl<DT: Dispatch> CombinerState<DT> {
    pub open spec fn no_overlap_with(self, other: Self) -> bool {
        match self {
            CombinerState::Appending { cur_idx, tail } => {
                match other {
                    CombinerState::Reading(ReaderState::Guard { start, end, cur, val }) => {
                        (cur_idx > cur)  // self is after the other
                         || (tail <= cur)  // self is before the other

                    },
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        (cur_idx >= tail2)  // self is after the other
                         || (tail <= cur_idx2)  // self is before the other

                    },
                    _ => { true },
                }
            },
            _ => { true },
        }
    }
}

tokenized_state_machine! { CyclicBuffer<DT: Dispatch> {
    fields {
        #[sharding(constant)]
        pub unbounded_log_instance: UnboundedLog::Instance::<DT>,

        #[sharding(constant)]
        pub cell_ids: Seq<CellId>,

        /// the size of the buffer
        #[sharding(constant)]
        pub buffer_size: LogIdx,

        /// the number of replicas
        #[sharding(constant)]
        pub num_replicas: nat,

        // Logical index into the above slice at which the log starts.
        // Note: the head does _not_ necessarily advance monotonically.
        // (It could go backwards in the event of two threads overlapping
        // in their AdvancingHead cycles.)
        // It's only guaranteed to be <= all the local heads.

        #[sharding(variable)]
        pub head: LogIdx,

        // Logical index into the above slice at which the log ends.
        // New appends go here.

        #[sharding(variable)]
        pub tail: LogIdx,

        // Array consisting of the local head of each replica registered with the log.
        // Required for garbage collection; since replicas make progress over the log
        // independently, we want to make sure that we don't garbage collect operations
        // that haven't been executed by all replicas.

        #[sharding(map)]
        pub local_versions: Map<NodeId, LogIdx>,    // previously called local_tails

        /// the contents of the buffer/log.
        #[sharding(storage_map)]
        pub contents: Map<LogicalLogIdx, StoredType<DT>>,

        // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
        // and sometimes 'false' means 'alive'.
        // entry is an index into the buffer (0 <= entry < LOG_SIZE)

        #[sharding(map)]
        pub alive_bits: Map</* entry: */ LogIdx, /* bit: */ bool>,

        #[sharding(map)]
        pub combiner: Map<NodeId, CombinerState<DT>>
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant
    ////////////////////////////////////////////////////////////////////////////////////////////


    #[invariant]
    pub spec fn log_size(&self) -> bool {
        self.buffer_size == LOG_SIZE
    }

    #[invariant]
    pub spec fn cell_ids(&self) -> bool {
        self.cell_ids.len() == self.buffer_size
    }

    #[invariant]
    pub spec fn complete(&self) -> bool {
        &&& (forall |i| 0 <= i < self.num_replicas <==> self.local_versions.contains_key(i))
        &&& (forall |i| 0 <= i < self.buffer_size  <==> self.alive_bits.contains_key(i))
        &&& (forall |i| 0 <= i < self.num_replicas <==> self.combiner.contains_key(i))
        &&& (forall |i| self.contents.contains_key(i) ==> -self.buffer_size <= i < self.tail)
    }

    #[invariant]
    pub spec fn pointer_ordering(&self) -> bool {
        &&& self.head <= self.tail
        &&& (forall |i| #[trigger] self.local_versions.contains_key(i) ==>
            self.head <= self.local_versions[i] <= self.tail)
        &&& (forall |i| #[trigger] self.local_versions.contains_key(i) ==>
            self.tail <= self.local_versions[i] +  self.buffer_size)
    }

    #[invariant]
    pub spec fn pointer_differences(&self) -> bool {
        forall |i| self.local_versions.contains_key(i) ==>
            self.local_versions[i] <= self.tail <= self.local_versions[i] + self.buffer_size
    }

    #[invariant]
    pub spec fn ranges_no_overlap(&self) -> bool {
        (forall |i, j| self.combiner.contains_key(i) && self.combiner.contains_key(j) && i != j ==>
            self.combiner[i].no_overlap_with(self.combiner[j])
        )
    }

    #[invariant]
    pub spec fn upcoming_bits_are_not_alive(&self) -> bool {
        let min_local_head = map_min_value(self.local_versions, (self.num_replicas - 1) as nat);
        forall |i|
            self.tail <= i < min_local_head + self.buffer_size
            ==> !log_entry_is_alive(self.alive_bits, i, self.buffer_size)
    }

    #[invariant]
    pub spec fn inv_buffer_contents(&self) -> bool {
        &&& (forall |i: int| self.tail - self.buffer_size <= i < self.tail ==> (
            (log_entry_is_alive(self.alive_bits, i, self.buffer_size) ||
                i < map_min_value(self.local_versions, (self.num_replicas - 1) as nat))
            <==>
            #[trigger] self.contents.contains_key(i)
        ))
        &&& (forall |i: int| self.tail <= i ==> ! #[trigger] self.contents.contains_key(i))
    }

    #[invariant]
    pub spec fn contents_meet_inv(&self) -> bool {
        forall |i: int| #[trigger] self.contents.contains_key(i) ==>
            stored_type_inv(self.contents[i], i, self.cell_ids[log_entry_idx(i, self.buffer_size) as int], self.unbounded_log_instance)
    }

    #[invariant]
    pub spec fn all_reader_state_valid(&self) -> bool {
        forall |node_id| #![trigger self.combiner[node_id]] #[trigger] self.combiner.contains_key(node_id) && self.combiner[node_id].is_Reading() ==>
          self.reader_state_valid(node_id, self.combiner[node_id].get_Reading_0())
    }

    pub closed spec fn reader_state_valid(&self, node_id: NodeId, rs: ReaderState<DT>) -> bool {
        match rs {
            ReaderState::Starting{start} => {
                // the starting value should match the local tail
                &&& start == self.local_versions[node_id]
                &&& start <= self.tail
            }
            ReaderState::Range{start, end, cur} => {
                // the start must be our local tail
                &&& self.local_versions[node_id] == start
                // the start must be before the end, can be equial if ltail == tail
                &&& start <= end
                // we've read the tail, but the tail may have moved
                &&& (self.tail as int) - (self.buffer_size as int) <= end <= (self.tail as int)
                // current is between start and end
                &&& start <= cur <= end
                // the entries up to, and including  current must be alive
                &&& (forall |i| start <= i < cur ==> log_entry_is_alive(self.alive_bits, i, self.buffer_size))
                // the entries up to, and including current must have something in the log
                &&& (forall |i| start <= i < cur ==> self.contents.contains_key(i))
            }
            ReaderState::Guard{start, end, cur, val} => {
                // the start must be our local tail
                &&& self.local_versions[node_id] == start
                // the start must be before the end, can be equial if ltail == tail
                &&& start <= end
                // we've read the tail, but the tail may have moved
                &&& (self.tail as int) - (self.buffer_size as int) <= end <= (self.tail as int)
                // current is between start and end
                &&& start <= cur < end
                // the entries up to, and including  current must be alive
                &&& (forall |i| start <= i <= cur ==> log_entry_is_alive(self.alive_bits, i, self.buffer_size))
                // the entries up to, and including current must have something in the log
                &&& (forall |i| start <= i <= cur ==> self.contents.contains_key(i))
                // the thing we are ready should match the log content
                &&& self.contents.contains_key(cur as int)
                &&& self.contents[cur as int] === val
            }
        }
    }

    #[invariant]
    pub spec fn all_combiner_valid(&self) -> bool {
        forall |node_id| #[trigger] self.combiner.contains_key(node_id) ==>
          self.combiner_valid(node_id, self.combiner[node_id])
    }

    pub closed spec fn combiner_valid(&self, node_id: NodeId, cs: CombinerState<DT>) -> bool {
        match cs {
            CombinerState::Idle => true,
            CombinerState::Reading(_) => true, // see reader_state_valid instead
            CombinerState::AdvancingHead{idx, min_local_version} => {
                // the index is always within the defined replicas
                &&& idx <= self.num_replicas as nat
                // forall replicas we'e seen, min_local_version is smaller than all localTails
                &&& (forall |n| 0 <= n < idx ==> min_local_version <= self.local_versions[n])
            }
            CombinerState::AdvancingTail{observed_head} => {
                // the observed head is smaller than all local tails
                &&& (forall |n| 0 <= n < self.num_replicas as nat ==> observed_head <= self.local_versions[n])
            }
            CombinerState::Appending{cur_idx, tail} => {
                // the current index is between local tails and tail.
                &&& self.local_versions[node_id] <= cur_idx <= tail
                // the read tail is smaller or equal to the current tail.
                &&& tail <= self.tail
                //
                &&& (self.tail as int) - (self.buffer_size as int) <= cur_idx <= (self.tail as int)
                // all the entries we're writing must not be alive.
                &&& (forall |i : nat| cur_idx <= i < tail ==> (
                  !(log_entry_is_alive(self.alive_bits, i as int, self.buffer_size))))
            }
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Initialization
    ////////////////////////////////////////////////////////////////////////////////////////////

    init!{
        initialize(buffer_size: nat, num_replicas: nat, contents: Map<int, StoredType<DT>>, cell_ids: Seq<CellId>, unbounded_log_instance: UnboundedLog::Instance<DT>, ) {
            require(num_replicas > 0);
            require(buffer_size == LOG_SIZE);
            require(cell_ids.len() == buffer_size);

            init unbounded_log_instance = unbounded_log_instance;
            init cell_ids = cell_ids;
            init buffer_size = buffer_size;
            init num_replicas = num_replicas;
            init head = 0;
            init tail = 0;
            init local_versions = Map::new(Set::range(0, num_replicas), |i: NodeId| 0);

            require(forall |i: int| (-buffer_size <= i < 0 <==> contents.contains_key(i)));
            require(forall |i: int| #[trigger] contents.contains_key(i) ==> stored_type_inv(contents[i], i, cell_ids[log_entry_idx(i, buffer_size) as int], unbounded_log_instance));
            init contents = contents;

            init alive_bits = Map::new(Set::range(0, buffer_size), |i: nat| !log_entry_alive_value(i as int, buffer_size));
            init combiner = Map::new(Set::range(0, num_replicas), |i: NodeId| CombinerState::Idle);
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Reader Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    //
    // The reader transitions traverse the log and read the entries in it.
    //

    /// start the reader on the provided node, the combiner must be in idle state.
    transition!{
        reader_start(node_id: NodeId) {
            have   local_versions    >= [ node_id => let local_head ];

            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [
                node_id => CombinerState::Reading(ReaderState::Starting { start: local_head })
            ];
        }
    }

    /// enter the reading phase
    transition!{
        reader_enter(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading(ReaderState::Starting { start })
            ];
            add combiner += [
                node_id => CombinerState::Reading(ReaderState::Range { start, end: pre.tail, cur: start })
            ];
            assert start <= pre.tail;
        }
    }

    /// read the value of the current entry to process it
    transition!{
        reader_guard(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading( ReaderState::Range{ start, end, cur })
            ];

            require(cur < end);

            have alive_bits >= [ log_entry_idx(cur as int, pre.buffer_size) => log_entry_alive_value(cur as int, pre.buffer_size) ];

            birds_eye let val = pre.contents.index(cur as int);

            add combiner += [
                node_id => CombinerState::Reading( ReaderState::Guard{ start, end, cur, val })
            ];

            // assert(stored_type_inv(val, cur as int));
        }
    }

    /// the value of the log must not change while we're processing it
    property!{
        guard_guards(node_id: NodeId) {
            have combiner >= [
                node_id => let CombinerState::Reading( ReaderState::Guard{ start, end, cur, val })
            ];
            guard contents >= [ cur as int => val ];

            assert(stored_type_inv(val, cur as int, pre.cell_ids[log_entry_idx(cur as int, pre.buffer_size) as int],  pre.unbounded_log_instance));
        }
    }

    /// finish processing the entry, increase current pointer
    transition!{
        reader_unguard(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading(ReaderState::Guard{ start, end, cur, val })
            ];
            add combiner += [
                node_id => CombinerState::Reading(ReaderState::Range{ start, end, cur: cur + 1 })
            ];
        }
    }

    /// finish the reading whith, place the combiner into the idle state
    transition!{
        reader_finish(node_id: NodeId) {
            remove combiner -= [
                node_id => let CombinerState::Reading(ReaderState::Range{ start, end, cur })
            ];
            add    combiner += [ node_id => CombinerState::Idle ];

            remove local_versions -= [ node_id => let _ ];
            add    local_versions += [ node_id => end ];

            require(cur == end);
        }
    }

    /// abort reading, place the combiner back into the idle state
    transition!{
        reader_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Reading(r) ];
            add    combiner += [ node_id => CombinerState::Idle ];

            require(r.is_Starting() || r.is_Range());
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Advance Head Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    //
    // The advance head transitions update the global head of the log with the minimum value
    // of all local heads.

    /// start the advancing of the head by reading the local head of node 0
    transition!{
        advance_head_start(node_id: NodeId) {
            have   local_versions >= [ 0 => let local_head_0 ];
            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [ node_id => CombinerState::AdvancingHead { idx: 1, min_local_version: local_head_0,} ];
        }
    }

    /// read the next local head
    transition!{
        advance_head_next(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { idx, min_local_version } ];

            have   local_versions    >= [ idx => let local_head_at_idx ];
            require(idx < pre.num_replicas);

            let new_min = min(min_local_version, local_head_at_idx);
            add combiner += [ node_id => CombinerState::AdvancingHead { idx: idx + 1, min_local_version: new_min } ];
        }
    }

    /// update the head value with the current collected miniumu
    transition!{
        advance_head_finish(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { idx, min_local_version } ];
            add    combiner += [ node_id => CombinerState::Idle ];
            update head      = min_local_version;

            require(idx == pre.num_replicas);
        }
    }

    /// stop the advancing head transition without uppdating the head
    transition!{
        advance_head_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { .. } ];
            add    combiner += [ node_id => CombinerState::Idle ];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Advance Tail Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    //
    // The advance tail transition bump the tail of the log to make space for new entries.
    // We first read the current head as this defines the maximum value the tail can be advanced to
    // as we need to ensure that we do not overrun existing entries.

    /// start the advancing of the head tail by reading the head value
    transition!{
        advance_tail_start(node_id: NodeId) {
            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [ node_id => CombinerState::AdvancingTail { observed_head: pre.head } ];
        }
    }

    /// advance the tail to the new value
    transition!{
        advance_tail_finish(node_id: NodeId, new_tail: nat) {
            remove combiner -= [ node_id => let CombinerState::AdvancingTail { observed_head } ];
            add    combiner += [ node_id => CombinerState::Appending { cur_idx: pre.tail, tail: new_tail } ];
            update tail      = new_tail;

            // only allow advances and must not overwrite still active entries
            require(pre.tail <= new_tail <= observed_head + pre.buffer_size);

            // construct the entries in the log we withdraw
            birds_eye let withdrawn = Map::new(
                Set::range(pre.tail - pre.buffer_size, new_tail - pre.buffer_size),
                |i: int| pre.contents[i],
            );

            withdraw contents -= (withdrawn) by {
                assert forall |i: int| pre.tail - pre.buffer_size <= i < new_tail - pre.buffer_size implies pre.contents.contains_key(i) by {
                    let min_local_head = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
                    map_min_value_smallest(pre.local_versions,  (pre.num_replicas - 1) as nat);
                }
            };

            assert forall
              |i: int| pre.tail - pre.buffer_size <= i < new_tail - pre.buffer_size
                ==> stored_type_inv(#[trigger] withdrawn[i], i, pre.cell_ids[log_entry_idx(i, pre.buffer_size) as int], pre.unbounded_log_instance) by {

                assert forall
                  |i: int| pre.tail - pre.buffer_size <= i < new_tail - pre.buffer_size
                    implies stored_type_inv(#[trigger] withdrawn[i], i, pre.cell_ids[log_entry_idx(i, pre.buffer_size) as int], pre.unbounded_log_instance) by {
                        assert(pre.contents.contains_key(i) && #[trigger] withdrawn.contains_key(i)) by {
                            let min_local_head = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
                            map_min_value_smallest(pre.local_versions,  (pre.num_replicas - 1) as nat);
                        };
                    };
                };
        }
    }

    /// aborts the advancing tail transitions
    transition!{
        advance_tail_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingTail { .. } ];
            add    combiner += [ node_id => CombinerState::Idle ];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Advance Tail Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////


    transition!{
        append_flip_bit(node_id: NodeId, deposited: StoredType<DT>) {
            remove combiner -= [ node_id => let CombinerState::Appending { cur_idx, tail } ];
            add    combiner += [ node_id => CombinerState::Appending { cur_idx: cur_idx + 1, tail } ];

            remove alive_bits -= [ log_entry_idx(cur_idx as int, pre.buffer_size) => let bit ];
            add    alive_bits += [ log_entry_idx(cur_idx as int, pre.buffer_size) => log_entry_alive_value(cur_idx  as int, pre.buffer_size) ];

            require(cur_idx < tail);
            require(stored_type_inv(deposited, cur_idx as int, pre.cell_ids[log_entry_idx(cur_idx as int, pre.buffer_size) as int],  pre.unbounded_log_instance));

            deposit contents += [ cur_idx as int => deposited ] by {
                map_min_value_smallest(pre.local_versions,  (pre.num_replicas - 1) as nat);
            };
        }
    }

    /// finish the appending parts
    transition!{
        append_finish(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Appending { cur_idx, tail } ];
            add    combiner += [ node_id => CombinerState::Idle ];

            require(cur_idx == tail);
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Proofs
    ////////////////////////////////////////////////////////////////////////////////////////////////

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, buffer_size: nat, num_replicas: nat, contents: Map<int, StoredType<DT>>, cell_ids: Seq<CellId>,  unbounded_log_instance: UnboundedLog::Instance<DT>, ) {
        assert forall |i| post.tail <= i < post.buffer_size implies !log_entry_is_alive(post.alive_bits, i, post.buffer_size) by {
            int_mod_less_than_same(i, post.buffer_size as int);
        }
    }

    #[inductive(advance_head_start)]
    fn advance_head_start_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(advance_head_next)]
    fn advance_head_next_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(advance_head_abort)]
    fn advance_head_abort_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(advance_head_finish)]
    fn advance_head_finish_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(advance_tail_start)]
    fn advance_tail_start_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(advance_tail_abort)]
    fn advance_tail_abort_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(advance_tail_finish)]
    fn advance_tail_finish_inductive(pre: Self, post: Self, node_id: NodeId, new_tail: nat) {
        let buffer_size = pre.buffer_size;
        let num_replicas = pre.num_replicas;
        let observed_head = pre.combiner[node_id].get_AdvancingTail_observed_head();
        let min_local = map_min_value(pre.local_versions, (num_replicas - 1) as nat);

        // Establish key properties of min_local
        map_min_value_smallest(pre.local_versions, (num_replicas - 1) as nat);

        // observed_head <= min_local: since observed_head <= all local_versions and min_local is one of them
        assert(observed_head <= min_local) by {
            assert(map_contains_value(pre.local_versions, min_local));
            let k = choose |k: NodeId| pre.local_versions.contains_key(k) && pre.local_versions[k] == min_local;
            assert(0 <= k < num_replicas) by {
                assert(forall |i| 0 <= i < num_replicas <==> pre.local_versions.contains_key(i));
            };
            assert(pre.combiner_valid(node_id, pre.combiner[node_id]));
            assert(observed_head <= pre.local_versions[k]);
        };

        // min_local <= pre.tail: since all local_versions <= tail
        assert(min_local <= pre.tail) by {
            assert(map_contains_value(pre.local_versions, min_local));
            let k = choose |k: NodeId| pre.local_versions.contains_key(k) && pre.local_versions[k] == min_local;
            assert(0 <= k < num_replicas) by {
                assert(forall |i| 0 <= i < num_replicas <==> pre.local_versions.contains_key(i));
            };
            assert(pre.local_versions.contains_key(k));
            assert(pre.local_versions[k] <= pre.tail);
        };

        // new_tail <= min_local + buffer_size
        assert(new_tail <= min_local + buffer_size);

        // new_tail <= pre.tail + buffer_size (so new_tail - buffer_size <= pre.tail)
        assert(new_tail <= pre.tail + buffer_size);

        // === Prove all_combiner_valid ===
        assert(post.all_combiner_valid()) by {
            assert forall |nid: NodeId| #[trigger] post.combiner.contains_key(nid) implies
                post.combiner_valid(nid, post.combiner[nid]) by {
                if nid == node_id {
                    // post.combiner[nid] = Appending{cur_idx: pre.tail, tail: new_tail}
                    // (1) local_versions[node_id] <= pre.tail
                    assert(post.local_versions[node_id] <= pre.tail) by {
                        assert(pre.local_versions.contains_key(node_id));
                        assert(pre.local_versions[node_id] <= pre.tail);
                    };
                    // (2) pre.tail <= new_tail: from require
                    // (3) new_tail <= post.tail = new_tail: trivial
                    // (4) post.tail - buffer_size <= pre.tail <= post.tail
                    assert((post.tail as int) - (buffer_size as int) <= (pre.tail as int)) by {
                        assert(new_tail <= pre.tail + buffer_size);
                    };
                    // (5) forall i: pre.tail <= i < new_tail => !alive(i)
                    assert forall |i: nat| pre.tail <= i < new_tail implies
                        !log_entry_is_alive(post.alive_bits, i as int, post.buffer_size) by {
                        assert(pre.tail <= i < min_local + buffer_size);
                    };
                } else {
                    assert(pre.combiner.contains_key(nid));
                    assert(pre.combiner_valid(nid, pre.combiner[nid]));

                    match pre.combiner[nid] {
                        CombinerState::Appending{cur_idx: cur_idx2, tail: tail2} => {
                            // (post.tail as int) - buffer_size <= cur_idx2:
                            // new_tail <= observed_head + buffer_size
                            // observed_head <= local_versions[nid] (from combiner_valid for AdvancingTail)
                            // local_versions[nid] <= cur_idx2 (from combiner_valid for Appending)
                            assert(post.local_versions.contains_key(nid));
                            assert(post.local_versions[nid] <= cur_idx2);
                            assert(observed_head <= post.local_versions[nid]) by {
                                assert(0 <= nid < num_replicas) by {
                                    assert(forall |i| 0 <= i < num_replicas <==> pre.local_versions.contains_key(i));
                                };
                                assert(pre.combiner_valid(node_id, pre.combiner[node_id]));
                            };
                            assert((post.tail as int) - (buffer_size as int) <= cur_idx2 as int) by {
                                assert(new_tail <= observed_head + buffer_size);
                            };
                        },
                        _ => {},
                    };
                }
            };
        };

        // === Prove inv_buffer_contents ===
        assert(post.inv_buffer_contents()) by {
            // Key relationship: post.contents = pre.contents.remove_keys(Set::range(pre.tail - buffer_size, new_tail - buffer_size))
            // For i not in withdrawn range, post.contents.contains_key(i) = pre.contents.contains_key(i)
            // For i in withdrawn range [pre.tail - B, new_tail - B), !post.contents.contains_key(i)

            // Part 1: forall i in [new_tail - B, new_tail): (alive || i < min_local) <==> post.contents.contains_key(i)
            assert forall |i: int| (post.tail as int) - (post.buffer_size as int) <= i < post.tail as int implies
                ((log_entry_is_alive(post.alive_bits, i, post.buffer_size) ||
                  i < map_min_value(post.local_versions, (post.num_replicas - 1) as nat) as int)
                 <==> #[trigger] post.contents.contains_key(i)) by {

                if i < pre.tail as int {
                    // i in [new_tail - B, pre.tail)
                    // i is NOT in withdrawn range [pre.tail - B, new_tail - B):
                    //   withdrawn range requires i < new_tail - B,
                    //   but i >= new_tail - B (since i >= post.tail - B = new_tail - B)
                    // So post.contents.contains_key(i) = pre.contents.contains_key(i)
                    // i is in pre range [pre.tail - B, pre.tail): yes since i >= new_tail - B >= pre.tail - B
                    assert((pre.tail as int) - (buffer_size as int) <= i < pre.tail as int);
                    // From pre.inv_buffer_contents:
                    assert((log_entry_is_alive(pre.alive_bits, i, buffer_size) ||
                            i < map_min_value(pre.local_versions, (num_replicas - 1) as nat) as int)
                           <==> pre.contents.contains_key(i));
                    // post.contents.contains_key(i) = pre.contents.contains_key(i)
                    // (i is not in withdrawn domain [pre.tail-B, new_tail-B) since i >= new_tail-B)
                    assert(post.contents.contains_key(i) == pre.contents.contains_key(i));
                } else {
                    // i in [pre.tail, new_tail)
                    // pre.contents doesn't contain i (i >= pre.tail)
                    assert(!pre.contents.contains_key(i));
                    // post.contents also doesn't contain i
                    assert(!post.contents.contains_key(i));
                    // Need: !(alive(i) || i < min_local)
                    // !alive(i): from upcoming_bits_are_not_alive: pre.tail <= i < min_local + B
                    assert(!log_entry_is_alive(pre.alive_bits, i, buffer_size)) by {
                        assert(pre.tail as int <= i < (min_local + buffer_size) as int);
                    };
                    // i >= min_local: min_local <= pre.tail <= i
                    assert(i >= min_local as int);
                }
            };

            // Part 2: forall i >= new_tail: !post.contents.contains_key(i)
            assert forall |i: int| post.tail as int <= i implies !#[trigger] post.contents.contains_key(i) by {
                // i >= new_tail >= pre.tail, so pre.contents doesn't have it
                assert(i >= pre.tail as int);
                assert(!pre.contents.contains_key(i));
                // post.contents is a submap of pre.contents
                assert(!post.contents.contains_key(i));
            };
        };
    }

    #[inductive(append_flip_bit)]
    fn append_flip_bit_inductive(pre: Self, post: Self, node_id: NodeId, deposited: StoredType<DT>) { admit(); }

    #[inductive(append_finish)]
    fn append_finish_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(reader_start)]
    fn reader_start_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(reader_enter)]
    fn reader_enter_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(reader_guard)]
    fn reader_guard_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(reader_unguard)]
    fn reader_unguard_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(reader_finish)]
    fn reader_finish_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(reader_abort)]
    fn reader_abort_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }
}}

pub open spec fn min(x: nat, y: nat) -> nat {
    if x < y {
        x
    } else {
        y
    }
}

pub open spec fn map_min_value(m: Map<NodeId, nat>, idx: nat) -> nat
    decreases idx,
{
    if idx === 0 {
        m.index(0)
    } else {
        min(map_min_value(m, (idx - 1) as nat), m.index(idx))
    }
}

proof fn map_min_value_smallest(m: Map<NodeId, nat>, idx: nat)
    requires
        forall|i| 0 <= i <= idx ==> m.contains_key(i),
    ensures
        forall|n| 0 <= n <= idx as nat ==> map_min_value(m, idx) <= m.index(n),
        map_contains_value(m, map_min_value(m, idx)),
    decreases idx,
{
    if idx == 0 {
        assert(m.contains_key(0));
    } else {
        map_min_value_smallest(m, (idx - 1) as nat);
        if m.index(idx) < map_min_value(m, (idx - 1) as nat) {
            assert(m.contains_key(idx));
        }
    }
}

/// converts the logical to the physical log index
pub open spec fn log_entry_idx(logical: LogicalLogIdx, buffer_size: nat) -> LogIdx
    recommends
        buffer_size == LOG_SIZE,
{
    (logical % (buffer_size as int)) as nat
}

// a % b == 0 to a == b * (a / b)
pub proof fn log_entry_idx_wrap_around(start: nat, buffer_size: nat, idx: nat)
    requires
        buffer_size == LOG_SIZE,
        start <= idx < start + buffer_size,
    ensures
        forall|i|
            start <= i < start + buffer_size && i != idx ==> log_entry_idx(i, buffer_size)
                != log_entry_idx(idx as int, buffer_size),
{
}

/// predicate to check whether a log entry is alive
pub open spec fn log_entry_is_alive(
    alive_bits: Map<LogIdx, bool>,
    logical: LogicalLogIdx,
    buffer_size: nat,
) -> bool
    recommends
        buffer_size == LOG_SIZE,
{
    let phys_id = log_entry_idx(logical, buffer_size);
    alive_bits[phys_id as nat] == log_entry_alive_value(logical, buffer_size)
}

/// the value the alive but must have for the entry to be alive, this flips on wrap around
pub open spec fn log_entry_alive_value(logical: LogicalLogIdx, buffer_size: nat) -> bool
    recommends
        buffer_size == LOG_SIZE,
{
    ((logical / buffer_size as int) % 2) == 0
}

spec fn add_buffersize(i: int, buffer_size: nat) -> int {
    i + buffer_size
}

proof fn log_entry_alive_wrap_around(
    alive_bits: Map<LogIdx, bool>,
    buffer_size: nat,
    low: nat,
    high: nat,
)
    requires
        buffer_size == LOG_SIZE,
        forall|i: nat| i < buffer_size <==> alive_bits.contains_key(i),
        low <= high <= low + buffer_size,
    ensures
        forall|i: int|
            low <= i < high ==> log_entry_is_alive(alive_bits, i, buffer_size)
                == !#[trigger] log_entry_is_alive(
                alive_bits,
                add_buffersize(i, buffer_size),
                buffer_size,
            ),
{
}

proof fn log_entry_alive_wrap_around_helper(
    alive_bits: Map<LogIdx, bool>,
    buffer_size: nat,
    low: nat,
    high: nat,
)
    requires
        buffer_size == LOG_SIZE,
        forall|i: nat| i < buffer_size <==> alive_bits.contains_key(i),
        low <= high <= low + buffer_size,
        forall|i: int|
            low <= i < high ==> !#[trigger] log_entry_is_alive(
                alive_bits,
                add_buffersize(i, buffer_size),
                buffer_size,
            ),
    ensures
        forall|i: int|
            low + buffer_size <= i < high + buffer_size ==> !#[trigger] log_entry_is_alive(
                alive_bits,
                i,
                buffer_size,
            ),
{
    assert forall|i: int|
        low + buffer_size <= i < high + buffer_size implies !#[trigger] log_entry_is_alive(
        alive_bits,
        i,
        buffer_size,
    ) by {
        let j = i - buffer_size;
        assert(low <= j < high);
        assert(!log_entry_is_alive(alive_bits, add_buffersize(j, buffer_size), buffer_size));
    }
}

#[verifier(nonlinear)]
pub proof fn log_entry_alive_value_wrap_around(i: LogicalLogIdx, buffer_size: nat)
    requires
        buffer_size > 0,
    ensures
        log_entry_alive_value(i, buffer_size) != log_entry_alive_value(
            i + (buffer_size as int),
            buffer_size,
        ),
{
    assert(((i + (buffer_size as int)) / buffer_size as int) == ((i / buffer_size as int) + 1));
}

} // verus!
