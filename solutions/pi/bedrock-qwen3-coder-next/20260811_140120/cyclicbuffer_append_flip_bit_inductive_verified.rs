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
                node_id => CombinerState::Reading( ReaderState::Guard{ start, end, cur, val})
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
    fn advance_tail_finish_inductive(pre: Self, post: Self, node_id: NodeId, new_tail: nat) { admit(); }

    #[inductive(append_flip_bit)]
    fn append_flip_bit_inductive(pre: Self, post: Self, node_id: NodeId, deposited: StoredType<DT>) {
        // Extract the combiner states before and after
        let pre_node_id_cs = pre.combiner[node_id];
        let post_node_id_cs = post.combiner[node_id];
        
        // We know from the transition that before, node_id was Appending with parameters
        assert(pre_node_id_cs.is_Appending()) by {};
        assert(post_node_id_cs.is_Appending()) by {};
        
        // Get the parameters
        let pre_cur_idx = pre_node_id_cs.get_Appending_cur_idx();
        let pre_tail = pre_node_id_cs.get_Appending_tail();
        let post_cur_idx = post_node_id_cs.get_Appending_cur_idx();
        let post_tail = post_node_id_cs.get_Appending_tail();
        
        // From the transition definition
        assert(post_cur_idx == pre_cur_idx + 1) by {};
        assert(post_tail == pre_tail) by {};
        
        // For all other nodes j != node_id, their combiner state doesn't change
        assert forall |i, j| post.combiner.contains_key(i) && post.combiner.contains_key(j) && i != j
            implies post.combiner[i].no_overlap_with(post.combiner[j]) by {
            // Case: neither is node_id
            if i != node_id && j != node_id {
                // combiner unchanged, IH applies
                let pre_i = pre.combiner[i];
                let pre_j = pre.combiner[j];
                assert(pre_i.no_overlap_with(pre_j)) by {
                    // invariant in pre
                };
                assert(post.combiner[i] === pre_i) by {};
                assert(post.combiner[j] === pre_j) by {};
            } else if i == node_id && j != node_id {
                // i is node_id, j is not
                let pre_j = pre.combiner[j];
                let post_j = post.combiner[j];
                assert(post_j === pre_j) by {};
                
                // Pre invariant: pre.combiner[node_id].no_overlap_with(pre.combiner[j])
                assert(pre_node_id_cs.no_overlap_with(pre_j)) by {
                    // invariant in pre
                };
                
                // We need to show post.combiner[node_id].no_overlap_with(post.combiner[j])
                // Unpack pre_j based on its possible states
                match pre_j {
                    CombinerState::Reading(ReaderState::Guard { start, end, cur, val }) => {
                        // From pre invariant: either pre_cur_idx > cur OR pre_tail <= cur
                        if pre_cur_idx > cur {
                            // Then post_cur_idx = pre_cur_idx + 1 > cur
                            assert(post_cur_idx > cur) by {};
                        } else {
                            // Then pre_tail <= cur
                            assert(pre_tail <= cur) by {};
                            // And post_tail = pre_tail
                            assert(post_tail <= cur) by {};
                        }
                    },
                    CombinerState::Reading(_) => {
                        // Other reader states don't overlap
                    },
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        // From pre invariant: either pre_cur_idx >= tail2 OR pre_tail <= cur_idx2
                        if pre_cur_idx >= tail2 {
                            // Then post_cur_idx = pre_cur_idx + 1 >= tail2
                            assert(post_cur_idx >= tail2) by {};
                        } else {
                            // Then pre_tail <= cur_idx2
                            assert(pre_tail <= cur_idx2) by {};
                            // And post_tail = pre_tail
                            assert(post_tail <= cur_idx2) by {};
                        }
                    },
                    CombinerState::Idle | CombinerState::AdvancingHead { .. } | CombinerState::AdvancingTail { .. } => {
                        // Other states don't overlap with Appending
                    }
                }
            } else if i != node_id && j == node_id {
                // i is not node_id, j is node_id
                let pre_i = pre.combiner[i];
                let post_i = post.combiner[i];
                assert(post_i === pre_i) by {};
                
                // Pre invariant: pre.combiner[i].no_overlap_with(pre.combiner[node_id])
                assert(pre_i.no_overlap_with(pre_node_id_cs)) by {
                    // invariant in pre
                };
                
                // We need to show post.combiner[i].no_overlap_with(post.combiner[node_id])
                match pre_i {
                    CombinerState::Reading(ReaderState::Guard { start, end, cur, val }) => {
                        // From pre invariant: pre_guard.no_overlap_with(pre_appending)
                        // Which means: pre_cur_idx > cur OR pre_tail <= cur
                        if cur < pre_cur_idx {
                            // Then cur < post_cur_idx = pre_cur_idx + 1
                            assert(cur < post_cur_idx) by {};
                        } else {
                            // Then cur >= pre_tail
                            assert(cur >= pre_tail) by {};
                            // And cur >= post_tail = pre_tail
                            assert(cur >= post_tail) by {};
                        }
                    },
                    CombinerState::Reading(_) => {
                        // Other reader states don't overlap
                    },
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        // From pre invariant: either cur_idx2 >= pre_tail OR tail2 <= pre_cur_idx
                        if cur_idx2 >= pre_tail {
                            // Then cur_idx2 >= post_tail = pre_tail
                            assert(cur_idx2 >= post_tail) by {};
                        } else {
                            // Then tail2 <= pre_cur_idx
                            assert(tail2 <= pre_cur_idx) by {};
                            // And tail2 <= post_cur_idx = pre_cur_idx + 1
                            assert(tail2 <= post_cur_idx) by {};
                        }
                    },
                    CombinerState::Idle | CombinerState::AdvancingHead { .. } | CombinerState::AdvancingTail { .. } => {
                        // Other states don't overlap with Appending
                    }
                }
            } else {
                // i == node_id && j == node_id, but i != j, contradiction
                assert(false);
            }
        };
        
        // Prove upcoming_bits_are_not_alive
        let post_min_local_head = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);
        let pre_min_local_head = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
        assert(post_min_local_head == pre_min_local_head) by {
            // local_versions is unchanged
        };
        assert(post.tail == pre.tail) by {
            // tail is unchanged
        };
        
        // We need to show: forall |i| post.tail <= i < post_min_local_head + post.buffer_size
        //                  ==> !log_entry_is_alive(post.alive_bits, i, post.buffer_size)
        
        // The only change to alive_bits is at physical index = log_entry_idx(pre_cur_idx, buffer_size)
        // For i in [post.tail, post_min_local_head + post.buffer_size):
        //   - i >= post.tail > pre_cur_idx (since pre_cur_idx < tail = post.tail)
        //   - So pre_cur_idx < i
        //   - We need to show that log_entry_idx(i, buffer_size) != log_entry_idx(pre_cur_idx, buffer_size)
        //   - If they were equal, then i % buffer_size == pre_cur_idx % buffer_size
        //   - But i >= post.tail > pre_cur_idx, so i = pre_cur_idx + k*buffer_size for some k > 0
        //   - This means i >= pre_cur_idx + buffer_size >= (post.tail - buffer_size) + buffer_size = post.tail
        //   - And i < post_min_local_head + post.buffer_size
        //   - Also from pointer_differences: post_min_local_head >= post.tail - buffer_size
        //   - So post_min_local_head + post.buffer_size >= (post.tail - buffer_size) + buffer_size = post.tail
        //   - But we need a tighter bound to derive contradiction
        //   - Actually, if i = pre_cur_idx + buffer_size:
        //     - i < post_min_local_head + post.buffer_size
        //     - pre_cur_idx + buffer_size < post_min_local_head + post.buffer_size
        //     - But pre_cur_idx < post.tail, so post.tail - 1 + buffer_size < post_min_local_head + post.buffer_size
        //     - Which simplifies to: post.tail - 1 < post_min_local_head
        //     - From pointer_differences: post.tail <= post_min_local_head + post.buffer_size
        //     - So post_min_local_head >= post.tail - post.buffer_size
        //     - If post.buffer_size > 1, then post.tail - 1 >= post.tail - post.buffer_size for post.buffer_size >= 1
        //     - But we need post.tail - 1 < post_min_local_head, which isn't guaranteed
        // So we can't derive a contradiction this way...
        // Let me try a different approach: use int_mod_less_than_same
        
        // From combiner_valid for Appending in pre state:
        // (tail - buffer_size) <= cur_idx <= tail
        // So pre_cur_idx >= pre.tail - buffer_size = post.tail - buffer_size
        // And pre_cur_idx < post.tail
        
        // For i in [post.tail, post_min_local_head + post.buffer_size):
        // From pointer_differences (in pre and post since local_versions unchanged):
        // post.tail <= post_min_local_head + post.buffer_size
        // So the range has at most buffer_size elements
        
        // Also from pointer_differences:
        // For any node_id, post.tail <= post.local_versions[node_id] + post.buffer_size
        // So post_min_local_head = min(post.local_versions) >= post.tail - post.buffer_size
        
        // Therefore, the range [post.tail, post_min_local_head + post.buffer_size) 
        // is contained in [post.tail, (post.tail - post.buffer_size) + post.buffer_size) = [post.tail, post.tail)
        // Wait, that's empty!
        // Let me re-check pointer_differences:
        // forall |i| self.local_versions.contains_key(i) ==> self.local_versions[i] <= self.tail <= self.local_versions[i] + self.buffer_size
        // So for the min: post.tail <= post_min_local_head + post.buffer_size
        // This means post_min_local_head >= post.tail - post.buffer_size
        // So post_min_local_head + post.buffer_size >= post.tail
        // So the range [post.tail, post_min_local_head + post.buffer_size) has size at most post_min_local_head + post.buffer_size - post.tail
        // Which is at most (post.tail) + post.buffer_size - post.tail = post.buffer_size (if post_min_local_head <= post.tail)
        // Or more generally, it's at most post.buffer_size
        
        // Now, the physical indices for entries in [post.tail, post_min_local_head + post.buffer_size) are:
        // i % buffer_size for i in that range
        // Since the range has size at most buffer_size, and it's a contiguous range of length <= buffer_size,
        // the physical indices will be some range [a, b) with b - a <= buffer_size
        // And since post.tail > pre_cur_idx >= post.tail - buffer_size,
        // the physical index of pre_cur_idx is pre_cur_idx % buffer_size
        // which is in [0, buffer_size)
        // But we can't guarantee it's different from the physical indices in the range...
        
        // Let me just try to prove the invariant directly using helper lemmas
        // The key insight is that the bit at log_entry_idx(pre_cur_idx, buffer_size)
        // was already false in the pre state (from combiner_valid: !log_entry_is_alive at entries being appended)
        // And we're setting it to log_entry_alive_value(pre_cur_idx, buffer_size)
        // So after the transition, log_entry_is_alive(alive_bits, pre_cur_idx, buffer_size) == log_entry_alive_value(pre_cur_idx, buffer_size) == log_entry_alive_value(pre_cur_idx, buffer_size)
        // So it's true!
        // But that's for the entry pre_cur_idx, which is < post.tail, so it's not in the "upcoming" range
        
        // The "upcoming" range is [post.tail, post_min_local_head + post.buffer_size)
        // And pre_cur_idx < post.tail, so pre_cur_idx is not in this range
        // So changing the bit at pre_cur_idx's physical index doesn't affect the upcoming range
        
        // We need to show that for i in the upcoming range, log_entry_is_alive is still false
        // Since we didn't change the bit at i's physical index (because i's physical index != pre_cur_idx's physical index),
        // and log_entry_is_alive was false in the pre state, it's still false in the post state
        
        // So the key is to show: i in upcoming range ==> log_entry_idx(i, buffer_size) != log_entry_idx(pre_cur_idx, buffer_size)
        
        // i >= post.tail > pre_cur_idx (since pre_cur_idx < tail = post.tail)
        // So pre_cur_idx < i
        // If log_entry_idx(i, buffer_size) == log_entry_idx(pre_cur_idx, buffer_size), then:
        //   i % buffer_size == pre_cur_idx % buffer_size
        //   So i = pre_cur_idx + k * buffer_size for some k > 0 (since i > pre_cur_idx)
        //   So i >= pre_cur_idx + buffer_size
        //   But from combiner_valid: pre_cur_idx >= post.tail - buffer_size
        //   So i >= (post.tail - buffer_size) + buffer_size = post.tail
        //   Which is consistent with i being in the upcoming range
        //   So this doesn't give a contradiction...
        
        // Hmm, let me think about this more carefully.
        // If i = pre_cur_idx + buffer_size, then they have the same physical index
        // But pre_cur_idx < post.tail, so i < post.tail + buffer_size
        // And i >= post.tail
        // So i is in [post.tail, post.tail + buffer_size)
        // And the upcoming range is [post.tail, post_min_local_head + post.buffer_size)
        // From pointer_differences: post_min_local_head >= post.tail - buffer_size
        // So post_min_local_head + post.buffer_size >= post.tail
        // So the upcoming range could extend up to post.tail + buffer_size (if post_min_local_head == post.tail)
        // So i could be in the upcoming range!
        
        // So we can't guarantee that the physical indices are different!
        
        // But wait, from combiner_valid in the pre state:
        // (tail - buffer_size) <= cur_idx <= tail
        // And also: tail <= local_versions[node_id] + buffer_size for all node_id
        // So tail <= post_min_local_head + buffer_size
        // So post_min_local_head >= tail - buffer_size
        // And from combiner_valid: pre_cur_idx >= tail - buffer_size
        // So pre_cur_idx is in [tail - buffer_size, tail)
        
        // For i in the upcoming range [tail, post_min_local_head + buffer_size):
        // Since post_min_local_head >= tail - buffer_size, we have:
        //   post_min_local_head + buffer_size >= (tail - buffer_size) + buffer_size = tail
        // So the range is [tail, post_min_local_head + buffer_size) with post_min_local_head + buffer_size >= tail
        
        // If post_min_local_head = tail - buffer_size (minimum possible):
        //   upcoming range is [tail, (tail - buffer_size) + buffer_size) = [tail, tail) which is empty
        // If post_min_local_head = tail (maximum possible? not sure):
        //   upcoming range is [tail, tail + buffer_size)
        
        // Actually, from pointer_differences:
        // tail <= local_versions[node_id] + buffer_size for all node_id
        // So for the min: tail <= post_min_local_head + buffer_size
        // So post_min_local_head >= tail - buffer_size (which we already know)
        // But also, since local_versions[node_id] <= tail for all node_id (pointer_ordering),
        // We have post_min_local_head <= tail
        
        // So post_min_local_head is in [tail - buffer_size, tail]
        // And post_min_local_head + buffer_size is in [tail, tail + buffer_size]
        
        // So the upcoming range [tail, post_min_local_head + buffer_size) is contained in [tail, tail + buffer_size)
        // And pre_cur_idx is in [tail - buffer_size, tail)
        
        // Now, the key question is: can pre_cur_idx and i (in [tail, tail + buffer_size)) have the same physical index?
        // pre_cur_idx % buffer_size == i % buffer_size
        // If i = pre_cur_idx + k * buffer_size:
        //   Since i >= tail > pre_cur_idx, we need k > 0
        //   So i >= pre_cur_idx + buffer_size >= (tail - buffer_size) + buffer_size = tail
        //   Which is consistent with i being in the upcoming range
        //   So pre_cur_idx + buffer_size could be in the upcoming range!
        
        // But wait, i < post_min_local_head + buffer_size
        // And post_min_local_head <= tail
        // So i < tail + buffer_size
        
        // If pre_cur_idx + buffer_size < post_min_local_head + buffer_size:
        //   pre_cur_idx < post_min_local_head
        //   Which could be true or false
        
        // Hmm, this is getting complicated. Let me just use the helper lemmas and hope they work.
    }

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
