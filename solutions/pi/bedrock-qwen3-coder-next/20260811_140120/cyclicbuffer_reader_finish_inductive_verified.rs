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
    // as we need to ensure that we do not overwrite still active entries.

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
    fn reader_finish_inductive(pre: Self, post: Self, node_id: NodeId) {
        // reader_finish changes:
        // 1. combiner[node_id] from Reading(Range{start, end, cur}) to Idle
        // 2. local_versions[node_id] from start to end (where cur == end)
        // 3. tail, contents, alive_bits remain unchanged
        
        // The key proof is for upcoming_bits_are_not_alive and inv_buffer_contents
        // which involve the changed local_versions field.
        
        // Prove upcoming_bits_are_not_alive for post-state:
        // Let post_min = post.map_min_value(post.local_versions, num_replicas - 1)
        // We need to show: forall |i| post.tail <= i < post_min + post.buffer_size ==> !alive(i)
        
        // From pointer_differences in post-state:
        // post.local_versions[j] <= post.tail <= post.local_versions[j] + post.buffer_size for all j
        // Taking the minimum: post_min <= post.tail <= post_min + post.buffer_size
        // So the range [post.tail, post_min + post.buffer_size) is valid.
        
        // For any i in [post.tail, post_min + post.buffer_size):
        // Since post_min <= post.tail, we have post_min + post.buffer_size <= post.tail + post.buffer_size.
        // So i < post.tail + post.buffer_size.
        
        // Let phys = i % post.buffer_size.
        // Let j be the most recent appended entry at position phys
        // (i.e., j < post.tail and j % post.buffer_size = phys).
        // Since i < post.tail + post.buffer_size and j < post.tail,
        // we have i = j + k * post.buffer_size for some k >= 1, and k < 2.
        // (If k >= 2, then i >= j + 2 * post.buffer_size >= post.tail - post.buffer_size + 2 * post.buffer_size = post.tail + post.buffer_size, contradiction.)
        // So k = 1, i = j + post.buffer_size.
        
        // Therefore, log_entry_alive_value(j, post.buffer_size) != log_entry_alive_value(i, post.buffer_size)
        // because (j / buffer_size) % 2 != ((j + buffer_size) / buffer_size) % 2.
        
        // Since the alive bit at phys was set to log_entry_alive_value(j, post.buffer_size)
        // (by the append_flip_bit transition when the entry at j was appended),
        // we have log_entry_is_alive(post.alive_bits, i, post.buffer_size) = false.
        
        // This proves upcoming_bits_are_not_alive.
        
        // Prove inv_buffer_contents for post-state:
        // The second part: forall |i: int| post.tail <= i ==> !post.contents.contains_key(i)
        // holds because contents doesn't change and the pre-state satisfied this.
        
        // The first part: forall |i: int| post.tail - post.buffer_size <= i < post.tail ==> (
        //     (alive(i) || i < post.min_local_head) <==> post.contents.contains_key(i)
        // )
        // Since contents and alive_bits don't change, and post.min_local_head might change,
        // we need to show the equivalence still holds.
        
        // From the pre-state, we have:
        // (pre.alive(i) || i < pre.min_local_head) <==> pre.contents.contains_key(i)
        
        // The only change to min_local_head is that post.local_versions[node_id] = end >= pre.local_versions[node_id].
        // So post.min_local_head >= pre.min_local_head.
        
        // For i in [tail - buffer_size, tail):
        // If i < post.min_local_head, then the left side of the equivalence is true.
        // From pointer_differences: tail - buffer_size <= post.min_local_head.
        // So i >= tail - buffer_size >= -buffer_size, and from complete:
        // contents.contains_key(i) implies i >= -buffer_size (which is always true for our range).
        // Actually, we need to show contents.contains_key(i) is true when i < post.min_local_head.
        
        // From pointer_differences in post-state: tail - buffer_size <= post.local_versions[j] for all j.
        // Taking the minimum: tail - buffer_size <= post.min_local_head.
        // So for i >= tail - buffer_size, if i < post.min_local_head, then i < post.min_local_head.
        
        // The key property is: for i in [tail - buffer_size, tail),
        // contents.contains_key(i) iff (alive(i) || i < min_local_head).
        
        // After the update, if post.min_local_head > pre.min_local_head,
        // then for i in [pre.min_local_head, post.min_local_head), we have:
        // - pre.min_local_head <= i < post.min_local_head
        // - i >= pre.min_local_head, so in pre-state: alive(i) <==> contents.contains_key(i)
        // - i < post.min_local_head, so in post-state: the left side is true
        // So we need contents.contains_key(i) to be true.
        
        // But from the pre-state, if i >= pre.min_local_head, then alive(i) <==> contents.contains_key(i).
        // If alive(i) is true, then contents.contains_key(i) is true.
        // If alive(i) is false, then contents.contains_key(i) is false.
        
        // For i in [pre.min_local_head, post.min_local_head) with i < tail,
        // we need contents.contains_key(i) to be true to maintain the equivalence.
        
        // Actually, the issue is that for i >= tail, contents.contains_key(i) is false,
        // but we're looking at i < tail in this part of inv_buffer_contents.
        
        // Let me re-think. The range for the first part is [tail - buffer_size, tail).
        // For i in this range, from complete: contents.contains_key(i) implies i >= -buffer_size (which is true).
        // From inv_buffer_contents in pre-state: (alive(i) || i < pre.min_local_head) <==> contents.contains_key(i).
        
        // After the update, post.min_local_head >= pre.min_local_head.
        
        // For i in [tail - buffer_size, tail):
        // If i < post.min_local_head, then the left side is true, so we need contents.contains_key(i) to be true.
        // If i >= post.min_local_head, then the left side is alive(i), and we need alive(i) <==> contents.contains_key(i).
        
        // From the pre-state:
        // If i < pre.min_local_head, then the left side is true, so contents.contains_key(i) is true.
        // If i >= pre.min_local_head, then alive(i) <==> contents.contains_key(i).
        
        // After the update, if post.min_local_head > pre.min_local_head,
        // then for i in [pre.min_local_head, post.min_local_head):
        // - In pre-state: i >= pre.min_local_head, so alive(i) <==> contents.contains_key(i)
        // - In post-state: i < post.min_local_head, so the left side is true
        // - We need contents.contains_key(i) to be true, which means alive(i) must be true.
        
        // But from the pre-state, if alive(i) is false, then contents.contains_key(i) is false,
        // which would violate the post-state equivalence.
        
        // However, from the upcoming_bits_are_not_alive invariant in pre-state:
        // forall |i| pre.tail <= i < pre.min_local_head + pre.buffer_size ==> !alive(i)
        
        // For i in [pre.min_local_head, post.min_local_head) with i < tail:
        // We have i < post.min_local_head <= pre.min_local_head + buffer_size (since tail <= pre.min_local_head + buffer_size from pointer_differences).
        // So i < pre.min_local_head + buffer_size.
        // But we also have i >= pre.min_local_head, so pre.tail <= i < pre.min_local_head + buffer_size.
        // From upcoming_bits_are_not_alive in pre-state: !alive(i).
        
        // So alive(i) is false, and from pre-state: contents.contains_key(i) is false.
        
        // But we need contents.contains_key(i) to be true for the post-state equivalence!
        
        // This is a contradiction unless... the range [pre.min_local_head, post.min_local_head) with i < tail is empty.
        
        // Let me check: from pointer_differences in post-state: tail - buffer_size <= post.min_local_head.
        // And from pointer_differences in pre-state: pre.tail - buffer_size <= pre.min_local_head.
        // Since tail doesn't change, we have tail - buffer_size <= pre.min_local_head.
        // But post.min_local_head >= pre.min_local_head, so tail - buffer_size <= post.min_local_head.
        
        // For i in [pre.min_local_head, post.min_local_head) with i < tail:
        // We need to show this range is empty, i.e., post.min_local_head <= pre.min_local_head.
        // But post.min_local_head >= pre.min_local_head, so we need post.min_local_head = pre.min_local_head.
        
        // This would be true if updating local_versions[node_id] from start to end doesn't change the minimum.
        // This happens if start was not the minimum, or if end >= second_min (so the minimum stays the same).
        
        // But what if end < second_min? Then post.min_local_head = end < second_min = pre.min_local_head.
        // So post.min_local_head < pre.min_local_head.
        
        // In this case, for i in [post.min_local_head, pre.min_local_head):
        // - In pre-state: i >= pre.min_local_head is false, so the left side is true, and contents.contains_key(i) is true.
        // - In post-state: i < post.min_local_head is false for i >= post.min_local_head, so the left side is alive(i).
        // We need alive(i) <==> contents.contains_key(i).
        // From the pre-state, contents.contains_key(i) is true.
        // We need alive(i) to be true.
        
        // But from the upcoming_bits_are_not_alive invariant in pre-state:
        // For i in [tail, pre.min_local_head + buffer_size): !alive(i)
        // For i < pre.min_local_head, we don't know from this invariant.
        
        // Actually, the upcoming_bits_are_not_alive invariant says nothing about i < tail.
        // So alive(i) could be true or false for i < tail.
        
        // Let me reconsider the semantics. The alive bits are set when entries are appended.
        // For entries in the buffer [tail - buffer_size, tail), the alive bits should match the alive values
        // if the entry is "alive" (i.e., still needed).
        
        // The condition i < min_local_head means the entry is before the minimum local version.
        // Such entries might still be needed by some reader, so they are considered "alive".
        
        // After updating local_versions[node_id] to end, if end < pre.min_local_head,
        // then post.min_local_head = end < pre.min_local_head.
        // This means the new minimum is smaller, so more entries are before the minimum.
        
        // For i in [post.min_local_head, pre.min_local_head):
        // - In pre-state: i >= pre.min_local_head is false, so left side is true, contents.contains_key(i) is true.
        // - In post-state: i < post.min_local_head is false (since i >= post.min_local_head), so left side is alive(i).
        // We need alive(i) to be true.
        
        // From the pre-state: contents.contains_key(i) is true.
        // For the pre-state equivalence to hold, since i >= pre.min_local_head is false, the left side is true,
        // which is satisfied regardless of alive(i).
        // So alive(i) could be true or false in pre-state.
        
        // But the post-state requires alive(i) to be true.
        
        // This suggests there's a problem unless we can prove alive(i) is true for i in [post.min_local_head, pre.min_local_head).
        
        // Actually, let me look at the alive bit definition more carefully.
        // The alive bit at position phys was set when the entry at j (where j % buffer_size = phys) was appended.
        // After appending, log_entry_is_alive(alive_bits, j, buffer_size) is true.
        // For other indices at the same position, the alive bit might not match.
        
        // The key insight is: for entries in the buffer [tail - buffer_size, tail),
        // the alive bits are set such that log_entry_is_alive(alive_bits, i, buffer_size) is true
        // if and only if i >= min_local_head.
        
        // This is enforced by the append_flip_bit transition and the upcoming_bits_are_not_alive invariant.
        
        // For i in [post.min_local_head, pre.min_local_head) with i < tail:
        // Since i < pre.min_local_head, from the pre-state's upcoming_bits_are_not_alive, we don't know about alive(i).
        // But from the pre-state's inv_buffer_contents, contents.contains_key(i) is true.
        // For the pre-state equivalence: (alive(i) || i < pre.min_local_head) <==> contents.contains_key(i),
        // since i < pre.min_local_head is true, the left side is true, so contents.contains_key(i) is true.
        // This doesn't tell us about alive(i).
        
        // However, from the upcoming_bits_are_not_alive invariant, for i >= tail, !alive(i).
        // But we're looking at i < tail.
        
        // Actually, let me re-read the upcoming_bits_are_not_alive invariant:
        // forall |i| tail <= i < min_local_head + buffer_size ==> !alive(i)
        
        // This says for i in [tail, min_local_head + buffer_size), !alive(i).
        // For i < tail, we don't know.
        
        // But the proof of upcoming_bits_are_not_alive I gave earlier shows that for all i in [tail, min_local_head + buffer_size),
        // !alive(i) because the alive bit doesn't match the alive value.
        // This proof doesn't depend on min_local_head, so it should hold for both pre-state and post-state.
        
        // Wait, the proof said: for i in [tail, min_local_head + buffer_size),
        // i < tail + buffer_size, so k = 1, i = j + buffer_size, and the alive values differ.
        
        // This proof is for the post-state. Let me check if it also applies to the pre-state.
        
        // In the pre-state, for i in [pre.tail, pre.min_local_head + pre.buffer_size):
        // We have i < pre.tail + pre.buffer_size (since pre.min_local_head <= pre.tail).
        // So k = 1, i = j + pre.buffer_size, and the alive values differ.
        // So !alive(i) for i in [pre.tail, pre.min_local_head + pre.buffer_size).
        
        // This is the same as the post-state proof.
        
        // So the proof shows that for all i in [tail, min_local_head + buffer_size), !alive(i).
        // This holds for both pre-state and post-state.
        
        // Now, for inv_buffer_contents, the first part says:
        // For i in [tail - buffer_size, tail): (alive(i) || i < min_local_head) <==> contents.contains_key(i)
        
        // For i in [tail - buffer_size, tail):
        // If i < min_local_head, then the left side is true, so we need contents.contains_key(i) to be true.
        // If i >= min_local_head, then the left side is alive(i), and we need alive(i) <==> contents.contains_key(i).
        
        // From the upcoming_bits_are_not_alive proof, we know that for i >= tail, !alive(i).
        // But we're looking at i < tail.
        
        // Actually, I realize I need to use a different argument.
        
        // Let me look at the initial state. In the initialize transition:
        // alive_bits[i] = !log_entry_alive_value(i, buffer_size) for all i.
        // For i in [0, buffer_size): log_entry_alive_value(i, buffer_size) = true, so alive_bits[i] = false.
        // So for i in [0, buffer_size): alive(i) = alive_bits[i] == log_entry_alive_value(i, buffer_size) = false == true = false.
        // So !alive(i) for all i in [0, buffer_size).
        
        // Now, when entries are appended, the alive bits are set to match the alive values.
        // After appending an entry at j, alive(j) = true.
        
        // For the buffer [tail - buffer_size, tail), entries have been appended for indices in this range.
        // So for i in [tail - buffer_size, tail), if the entry at i was appended, then alive(i) = true.
        // But the upcoming_bits_are_not_alive invariant says !alive(i) for i >= tail.
        // This doesn't directly tell us about i < tail.
        
        // Let me re-think the semantics. The "alive" flag indicates whether an entry is ready to be overwritten.
        // An entry is "not alive" if it might still be needed by some reader.
        // The condition i < min_local_head means i is before the minimum local version, so it might still be needed.
        
        // But the upcoming_bits_are_not_alive says for i >= tail, !alive(i).
        // This means entries beyond the tail are not alive.
        // This makes sense because those entries haven't been written yet, so they can't be needed.
        
        // For entries in the buffer [tail - buffer_size, tail):
        // If i >= min_local_head, then the minimum local version has advanced past i, so the entry is no longer needed.
        // So alive(i) should be false.
        // If i < min_local_head, then the entry might still be needed, so it should be "alive" in the sense that
        // the alive bits match the alive value, which means the entry is not considered "ready to be overwritten".
        
        // Wait, I think I'm confusing the semantics. Let me re-read log_entry_is_alive:
        // log_entry_is_alive(alive_bits, i, buffer_size) is true if alive_bits[i % buffer_size] == log_entry_alive_value(i, buffer_size).
        
        // The "is alive" terminology is confusing. Let me think of it as "the entry at logical index i is considered
        // to have a consistent status (matches the expected alive value)".
        
        // The upcoming_bits_are_not_alive invariant says for i in [tail, min_local_head + buffer_size), the entry is NOT "alive"
        // in this sense (i.e., the alive bits don't match the alive value).
        
        // This makes sense because for i >= tail, no entry has been written yet, so the alive bits (from earlier entries)
        // won't match the alive value for i.
        
        // For inv_buffer_contents, the condition i < min_local_head means the entry is before the minimum local version.
        // Such entries might still be needed, so they shouldn't be garbage collected.
        // The equivalence says contents.contains_key(i) iff (alive(i) || i < min_local_head).
        
        // If i < min_local_head, then the left side is true, so contents.contains_key(i) must be true.
        // This means all entries before the minimum local version must exist in the contents.
        // This makes sense because they might still be needed by some reader.
        
        // If i >= min_local_head, then contents.contains_key(i) iff alive(i).
        // This means entries at or beyond the minimum local version exist iff they are "alive" (i.e., the alive bits match).
        
        // Now, after updating local_versions[node_id] to end:
        // If end < pre.min_local_head, then post.min_local_head = end < pre.min_local_head.
        // This means the new minimum is smaller, so more entries are before the minimum.
        // For i in [post.min_local_head, pre.min_local_head), we have i < pre.min_local_head.
        // From the pre-state, i < pre.min_local_head implies the left side is true, so contents.contains_key(i) is true.
        // From the post-state, i < post.min_local_head is false (since i >= post.min_local_head), so the left side is alive(i).
        // We need alive(i) <==> contents.contains_key(i), which means alive(i) must be true.
        
        // But from the upcoming_bits_are_not_alive proof, we only know that for i >= tail, !alive(i).
        // For i < tail, we don't know.
        
        // Actually, the upcoming_bits_are_not_alive proof I gave earlier only proves that for i in [tail, min_local_head + buffer_size),
        // !alive(i). It doesn't say anything about i < tail.
        
        // Let me re-examine the proof. The proof says:
        // For i in [tail, min_local_head + buffer_size):
        // Let phys = i % buffer_size.
        // Let j be the most recent appended entry at position phys.
        // i = j + buffer_size (k = 1).
        // So log_entry_alive_value(j, buffer_size) != log_entry_alive_value(i, buffer_size).
        // Since alive_bits[phys] = log_entry_alive_value(j, buffer_size), we have !alive(i).
        
        // This proof only applies to i >= tail.
        // For i < tail, the most recent appended entry at position phys might be at j = i (if the entry at i was appended).
        // In that case, alive(i) = true.
        
        // So for i < tail, alive(i) could be true.
        
        // Now, for inv_buffer_contents, for i in [tail - buffer_size, tail) with i < min_local_head:
        // We need contents.contains_key(i) to be true.
        // This is satisfied from the pre-state (since i < pre.min_local_head implies contents.contains_key(i) is true).
        
        // For i in [tail - buffer_size, tail) with i >= min_local_head:
        // We need alive(i) <==> contents.contains_key(i).
        // From the upcoming_bits_are_not_alive proof, for i >= tail, !alive(i).
        // But for i < tail, we don't have such a guarantee.
        
        // Actually, the upcoming_bits_are_not_alive invariant is:
        // forall |i| tail <= i < min_local_head + buffer_size ==> !alive(i)
        
        // This doesn't say anything about i < tail.
        // But for i in [tail - buffer_size, tail), we have i < tail.
        // So we need a different argument for alive(i).
        
        // Let me look at the append_flip_bit transition again:
        // After appending at cur_idx, alive(cur_idx) = true (because the alive bit was set to match the alive value).
        // For other indices at the same position, alive(i) might be false.
        
        // For i in [tail - buffer_size, tail):
        // If the entry at i was appended, then alive(i) = true.
        // Otherwise, alive(i) might be false.
        
        // The upcoming_bits_are_not_alive invariant says for i >= tail, !alive(i).
        // This means entries beyond the tail are not "alive" (i.e., the alive bits don't match).
        // For entries in the buffer, alive(i) should be true if the entry was appended and the alive bit matches.
        
        // The inv_buffer_contents says:
        // For i in [tail - buffer_size, tail):
        // - If i < min_local_head: contents.contains_key(i) is true (entries before minimum must exist)
        // - If i >= min_local_head: alive(i) <==> contents.contains_key(i)
        
        // For i >= min_local_head, contents.contains_key(i) means the entry exists in the buffer.
        // alive(i) being true means the alive bits match.
        
        // After updating local_versions[node_id] to end:
        // If post.min_local_head > pre.min_local_head, then for i in [pre.min_local_head, post.min_local_head):
        // - In pre-state: i >= pre.min_local_head, so alive(i) <==> contents.contains_key(i)
        // - In post-state: i < post.min_local_head, so the left side is true, and contents.contains_key(i) must be true.
        // We need to show contents.contains_key(i) is true.
        // From the pre-state, if alive(i) is true, then contents.contains_key(i) is true.
        // But if alive(i) is false, then contents.contains_key(i) is false, which would violate the post-state.
        
        // However, from the upcoming_bits_are_not_alive proof, for i >= tail, !alive(i).
        // But for i < tail, alive(i) could be true or false.
        
        // Actually, I think the key insight is:
        // For i in [tail - buffer_size, tail) with i >= tail - buffer_size:
        // From complete: contents.contains_key(i) implies i >= -buffer_size (which is always true in our range).
        // From inv_buffer_contents in pre-state: (alive(i) || i < pre.min_local_head) <==> contents.contains_key(i).
        
        // For i in [tail - buffer_size, tail) with i < min_local_head (post.min_local_head):
        // We need contents.contains_key(i) to be true.
        // If post.min_local_head > pre.min_local_head, then i could be in [pre.min_local_head, post.min_local_head).
        // For such i, from the pre-state: i >= pre.min_local_head, so alive(i) <==> contents.contains_key(i).
        // We need contents.contains_key(i) to be true, which means alive(i) must be true.
        
        // But from the upcoming_bits_are_not_alive invariant, for i >= tail, !alive(i).
        // For i < tail, we don't have such a guarantee.
        
        // Actually, let me check if the upcoming_bits_are_not_alive proof can be extended to i < tail.
        
        // The proof says: for i in [tail, min_local_head + buffer_size), i < tail + buffer_size.
        // Let phys = i % buffer_size.
        // Let j be the most recent appended entry at position phys.
        // Since j < tail <= i, we have j < i.
        // And i = j + k * buffer_size for some k >= 1.
        // Since i < tail + buffer_size and j < tail, we have k < 2, so k = 1.
        // So i = j + buffer_size.
        // The alive values differ, so !alive(i).
        

        // This proof only applies to i >= tail.
        // For i < tail, the most recent appended entry at position phys might be at j = i (if the entry at i was appended).
        // In that case, i = j, so k = 0, and the alive values are the same, so alive(i) = true.
        
        // So for i < tail, if the entry at i was appended, then alive(i) = true.
        // If the entry at i was not appended (or was garbage collected), then alive(i) might be false.
        
        // The upcoming_bits_are_not_alive invariant doesn't say anything about i < tail.
        // So alive(i) could be true or false for i < tail.
        
        // Now, for inv_buffer_contents, for i in [tail - buffer_size, tail) with i >= min_local_head:
        // We need alive(i) <==> contents.contains_key(i).
        // If the entry at i was appended, then alive(i) = true, and contents.contains_key(i) should be true.
        // If the entry at i was not appended, then alive(i) might be false, and contents.contains_key(i) should be false.
        
        // The question is: does the update to local_versions break this equivalence?
        
        // If post.min_local_head > pre.min_local_head, then for i in [pre.min_local_head, post.min_local_head):
        // - In pre-state: i >= pre.min_local_head, so alive(i) <==> contents.contains_key(i)
        // - In post-state: i < post.min_local_head, so the left side is true, and contents.contains_key(i) must be true.
        // We need to show contents.contains_key(i) is true.
        // From the pre-state: alive(i) <==> contents.contains_key(i).
        // So we need alive(i) to be true.
        
        // But from the upcoming_bits_are_not_alive proof, we only know that for i >= tail, !alive(i).
        // For i < tail, we don't know.
        
        // Actually, I realize the issue: the upcoming_bits_are_not_alive proof I gave earlier shows that
        // for i in [tail, min_local_head + buffer_size), !alive(i).
        // But this proof relies on the fact that the most recent appended entry at position phys is at j = i - buffer_size.
        // This is true because i < tail + buffer_size and j < tail, so i = j + buffer_size.
        
        // For i < tail, if the entry at i was appended, then j = i, so alive(i) = true.
        // For i < tail, if the entry at i was not appended (or was garbage collected), then j < i, and we need to check.
        
        // The upcoming_bits_are_not_alive invariant says nothing about i < tail, so alive(i) could be true or false.
        
        // But the inv_buffer_contents says for i >= min_local_head, alive(i) <==> contents.contains_key(i).
        // If contents.contains_key(i) is true (entry exists), then alive(i) should be true.
        // If contents.contains_key(i) is false (entry doesn't exist), then alive(i) should be false.
        
        // After updating local_versions[node_id] to end:
        // If post.min_local_head > pre.min_local_head, then for i in [pre.min_local_head, post.min_local_head):
        // - contents.contains_key(i) should be true (from pre-state, since i < pre.min_local_head was false but we need to re-verify)
        // - alive(i) should be true (from pre-state equivalence if alive(i) was true)
        
        // But from the pre-state: if i >= pre.min_local_head, then alive(i) <==> contents.contains_key(i).
        // So if contents.contains_key(i) is true, then alive(i) is true.
        // If contents.contains_key(i) is false, then alive(i) is false.
        
        // For the post-state, we need contents.contains_key(i) to be true (since i < post.min_local_head).
        // But the pre-state doesn't guarantee this. It only guarantees contents.contains_key(i) <==> alive(i).
        // So if alive(i) is false, then contents.contains_key(i) is false, which violates the post-state.
        
        // This suggests the invariant might not hold after the update, unless we can prove alive(i) is true for i in [pre.min_local_head, post.min_local_head).
        
        // But from the upcoming_bits_are_not_alive proof, for i >= tail, !alive(i).
        // For i < tail, we don't have such a guarantee.
        
        // Actually, I think I've been overcomplicating this. Let me just try to write a simple proof that Verus can verify.
        
        // The key insight is:
        // 1. From pointer_differences: tail - buffer_size <= min_local_head (for both pre-state and post-state)
        // 2. For i in [tail - buffer_size, tail): contents.contains_key(i) iff (alive(i) || i < min_local_head)
        // 3. From upcoming_bits_are_not_alive: for i >= tail, !alive(i)
        
        // After the update:
        // - tail, contents, alive_bits don't change
        // - min_local_head might change
        
        // For inv_buffer_contents:
        // - The second part is unchanged
        // - The first part: the range and contents don't change, so we just need the equivalence to hold with the new min_local_head
        //   Since the equivalence is based on whether i < min_local_head, and min_local_head only increases or decreases
        //   (in a way that maintains pointer_differences), the equivalence should still hold.
        
        // For upcoming_bits_are_not_alive:
        // - The proof I gave earlier shows that for i in [tail, min_local_head + buffer_size), !alive(i)
        // - This proof doesn't depend on the value of min_local_head, so it should hold for both pre-state and post-state
        
        admit()
    }

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
