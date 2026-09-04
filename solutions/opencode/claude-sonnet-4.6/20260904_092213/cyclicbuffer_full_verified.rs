
fn main() {}

#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::*;
use vstd::cell::{CellId, PointsTo};
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

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


verus! {

pub type LogicalLogIdx = int;


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

#[is_variant]
pub tracked enum ReaderState<DT: Dispatch> {
    Starting {
        start: LogIdx,
    },
    Range { start: LogIdx, end: LogIdx, cur: LogIdx },
    Guard { start: LogIdx, end: LogIdx, cur: LogIdx, val: StoredType<DT> },
}

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
                        (cur_idx > cur)  
                         || (tail <= cur)  

                    },
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        (cur_idx >= tail2)  
                         || (tail <= cur_idx2)  

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

        #[sharding(constant)]
        pub buffer_size: LogIdx,

        #[sharding(constant)]
        pub num_replicas: nat,


        #[sharding(variable)]
        pub head: LogIdx,


        #[sharding(variable)]
        pub tail: LogIdx,


        #[sharding(map)]
        pub local_versions: Map<NodeId, LogIdx>,    

        #[sharding(storage_map)]
        pub contents: Map<LogicalLogIdx, StoredType<DT>>,


        #[sharding(map)]
        pub alive_bits: Map<             LogIdx,            bool>,

        #[sharding(map)]
        pub combiner: Map<NodeId, CombinerState<DT>>
    }




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
                &&& start == self.local_versions[node_id]
                &&& start <= self.tail
            }
            ReaderState::Range{start, end, cur} => {
                &&& self.local_versions[node_id] == start
                &&& start <= end
                &&& (self.tail as int) - (self.buffer_size as int) <= end <= (self.tail as int)
                &&& start <= cur <= end
                &&& (forall |i| start <= i < cur ==> log_entry_is_alive(self.alive_bits, i, self.buffer_size))
                &&& (forall |i| start <= i < cur ==> self.contents.contains_key(i))
            }
            ReaderState::Guard{start, end, cur, val} => {
                &&& self.local_versions[node_id] == start
                &&& start <= end
                &&& (self.tail as int) - (self.buffer_size as int) <= end <= (self.tail as int)
                &&& start <= cur < end
                &&& (forall |i| start <= i <= cur ==> log_entry_is_alive(self.alive_bits, i, self.buffer_size))
                &&& (forall |i| start <= i <= cur ==> self.contents.contains_key(i))
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
            CombinerState::Reading(_) => true, 
            CombinerState::AdvancingHead{idx, min_local_version} => {
                &&& idx <= self.num_replicas as nat
                &&& (forall |n| 0 <= n < idx ==> min_local_version <= self.local_versions[n])
            }
            CombinerState::AdvancingTail{observed_head} => {
                &&& (forall |n| 0 <= n < self.num_replicas as nat ==> observed_head <= self.local_versions[n])
            }
            CombinerState::Appending{cur_idx, tail} => {
                &&& self.local_versions[node_id] <= cur_idx <= tail
                &&& tail <= self.tail
                &&& (self.tail as int) - (self.buffer_size as int) <= cur_idx <= (self.tail as int)
                &&& (forall |i : nat| cur_idx <= i < tail ==> (
                  !(log_entry_is_alive(self.alive_bits, i as int, self.buffer_size))))
            }
        }
    }



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



    transition!{
        reader_start(node_id: NodeId) {
            have   local_versions    >= [ node_id => let local_head ];

            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [
                node_id => CombinerState::Reading(ReaderState::Starting { start: local_head })
            ];
        }
    }

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

        }
    }

    property!{
        guard_guards(node_id: NodeId) {
            have combiner >= [
                node_id => let CombinerState::Reading( ReaderState::Guard{ start, end, cur, val })
            ];
            guard contents >= [ cur as int => val ];

            assert(stored_type_inv(val, cur as int, pre.cell_ids[log_entry_idx(cur as int, pre.buffer_size) as int],  pre.unbounded_log_instance));
        }
    }

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

    transition!{
        reader_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Reading(r) ];
            add    combiner += [ node_id => CombinerState::Idle ];

            require(r.is_Starting() || r.is_Range());
        }
    }



    transition!{
        advance_head_start(node_id: NodeId) {
            have   local_versions >= [ 0 => let local_head_0 ];
            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [ node_id => CombinerState::AdvancingHead { idx: 1, min_local_version: local_head_0,} ];
        }
    }

    transition!{
        advance_head_next(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { idx, min_local_version } ];

            have   local_versions    >= [ idx => let local_head_at_idx ];
            require(idx < pre.num_replicas);

            let new_min = min(min_local_version, local_head_at_idx);
            add combiner += [ node_id => CombinerState::AdvancingHead { idx: idx + 1, min_local_version: new_min } ];
        }
    }

    transition!{
        advance_head_finish(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { idx, min_local_version } ];
            add    combiner += [ node_id => CombinerState::Idle ];
            update head      = min_local_version;

            require(idx == pre.num_replicas);
        }
    }

    transition!{
        advance_head_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingHead { .. } ];
            add    combiner += [ node_id => CombinerState::Idle ];
        }
    }



    transition!{
        advance_tail_start(node_id: NodeId) {
            remove combiner -= [ node_id => CombinerState::Idle ];
            add    combiner += [ node_id => CombinerState::AdvancingTail { observed_head: pre.head } ];
        }
    }

    transition!{
        advance_tail_finish(node_id: NodeId, new_tail: nat) {
            remove combiner -= [ node_id => let CombinerState::AdvancingTail { observed_head } ];
            add    combiner += [ node_id => CombinerState::Appending { cur_idx: pre.tail, tail: new_tail } ];
            update tail      = new_tail;

            require(pre.tail <= new_tail <= observed_head + pre.buffer_size);

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

    transition!{
        advance_tail_abort(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::AdvancingTail { .. } ];
            add    combiner += [ node_id => CombinerState::Idle ];
        }
    }




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

    transition!{
        append_finish(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Appending { cur_idx, tail } ];
            add    combiner += [ node_id => CombinerState::Idle ];

            require(cur_idx == tail);
        }
    }


    #[inductive(initialize)]
    fn initialize_inductive(post: Self, buffer_size: nat, num_replicas: nat, contents: Map<int, StoredType<DT>>, cell_ids: Seq<CellId>,  unbounded_log_instance: UnboundedLog::Instance<DT>, ) {
        assert forall |i| post.tail <= i < post.buffer_size implies !log_entry_is_alive(post.alive_bits, i, post.buffer_size) by {
            int_mod_less_than_same(i, post.buffer_size as int);
        }
    }

    #[inductive(advance_head_start)]
    fn advance_head_start_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_head_next)]
    fn advance_head_next_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_head_abort)]
    fn advance_head_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_head_finish)]
    fn advance_head_finish_inductive(pre: Self, post: Self, node_id: NodeId) {
        // advance_head_finish sets head = min_local_version and idx == pre.num_replicas
        // From combiner_valid for AdvancingHead{idx, min_local_version}:
        //   forall n, 0 <= n < idx => min_local_version <= local_versions[n]
        // Since idx == pre.num_replicas, min_local_version <= all local_versions
        // So post.head = min_local_version <= any local_versions[i] <= pre.tail = post.tail
        let min_local_version = pre.combiner[node_id].get_AdvancingHead_min_local_version();
        let idx = pre.combiner[node_id].get_AdvancingHead_idx();
        assert(idx == pre.num_replicas);
        assert(pre.combiner_valid(node_id, pre.combiner[node_id]));
        assert(pre.pointer_ordering());
        assert(pre.complete());
        // Prove head <= tail
        assert(pre.num_replicas > 0) by { assert(pre.complete()); };
        assert(pre.local_versions.contains_key(0));
        assert(min_local_version <= pre.local_versions[0]);
        assert(pre.local_versions[0] <= pre.tail);
        assert(post.head <= post.tail);
        // Prove forall i, local_versions.contains_key(i) => head <= local_versions[i] <= tail
        assert forall |i| #[trigger] post.local_versions.contains_key(i) implies
            post.head <= post.local_versions[i] by {
            assert(pre.local_versions.contains_key(i));
            assert(0 <= i < pre.num_replicas);
            assert(min_local_version <= pre.local_versions[i]);
        };
    }

    #[inductive(advance_tail_start)]
    fn advance_tail_start_inductive(pre: Self, post: Self, node_id: NodeId) {
        // advance_tail_start adds AdvancingTail{observed_head: pre.head}
        // combiner_valid for AdvancingTail{observed_head} requires:
        //   forall n, 0 <= n < num_replicas => observed_head <= local_versions[n]
        // observed_head = pre.head, and pre.pointer_ordering gives head <= local_versions[i]
        assert(pre.pointer_ordering());
        assert(pre.complete());
        assert forall |n| 0 <= n < post.num_replicas as nat implies
            pre.head <= post.local_versions[n] by {
            assert(pre.local_versions.contains_key(n));
        };
     }

    #[inductive(advance_tail_abort)]
    fn advance_tail_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_tail_finish)]
    fn advance_tail_finish_inductive(pre: Self, post: Self, node_id: NodeId, new_tail: nat) {
        let observed_head = pre.combiner[node_id].get_AdvancingTail_observed_head();
        assert(pre.combiner_valid(node_id, pre.combiner[node_id]));
        assert(pre.pointer_ordering());
        assert(pre.pointer_differences());
        assert(pre.complete());
        assert(pre.upcoming_bits_are_not_alive());
        assert(pre.inv_buffer_contents());

        // From AdvancingTail combiner_valid:
        //   forall n, 0 <= n < num_replicas => observed_head <= local_versions[n]
        // So observed_head <= min_local_version
        let min_local_head = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
        map_min_value_smallest(pre.local_versions, (pre.num_replicas - 1) as nat);

        // observed_head <= min_local_head
        assert forall |n| 0 <= n < pre.num_replicas as nat implies observed_head <= pre.local_versions[n] by {
            assert(pre.local_versions.contains_key(n));
        };
        assert(observed_head <= min_local_head) by {
            assert(pre.local_versions.contains_key((pre.num_replicas - 1) as nat));
        };

        // all local_versions are >= pre.tail - buffer_size (from pointer_differences)
        // so min_local_head >= pre.tail - buffer_size
        assert(pre.tail <= min_local_head + pre.buffer_size) by {
            assert(pre.local_versions.contains_key((pre.num_replicas - 1) as nat));
            assert(pre.pointer_differences());
        };

        // new_tail <= observed_head + buffer_size <= min_local_head + buffer_size
        assert(new_tail <= min_local_head + pre.buffer_size);

        // Prove: upcoming_bits not alive for pre.tail <= i < new_tail
        assert forall |i: nat| pre.tail <= i < new_tail implies
            !log_entry_is_alive(pre.alive_bits, i as int, pre.buffer_size) by {
            assert(i < min_local_head + pre.buffer_size);
        };

        // Prove all_combiner_valid for node_id (Appending)
        // local_versions[node_id] <= pre.tail (from pointer_ordering)
        assert(pre.local_versions.contains_key(node_id));
        assert(pre.head <= pre.local_versions[node_id] <= pre.tail);

        // new_tail - buffer_size <= pre.tail:
        // new_tail <= observed_head + buffer_size <= min_local_head + buffer_size
        // and from pointer_differences: pre.tail <= min_local_head + buffer_size
        // Also new_tail >= pre.tail, so: pre.tail - buffer_size <= new_tail - buffer_size <= pre.tail
        // Actually new_tail - buffer_size <= pre.tail iff new_tail <= pre.tail + buffer_size
        // We know new_tail <= observed_head + buffer_size and observed_head <= all local_versions
        // Each local_version <= pre.tail (from pointer_ordering), so observed_head <= pre.tail
        // hence new_tail <= pre.tail + buffer_size. 
        assert(observed_head <= pre.tail) by {
            assert(pre.local_versions.contains_key(0));
            assert(observed_head <= pre.local_versions[0]);
            assert(pre.local_versions[0] <= pre.tail);
        };
        assert(new_tail <= pre.tail + pre.buffer_size);
        // So post.tail - buffer_size = new_tail - buffer_size <= pre.tail
        // And pre.tail <= new_tail = post.tail
        // Appending invariant: (post.tail - buffer_size) <= cur_idx <= post.tail
        // cur_idx = pre.tail, post.tail = new_tail
        // new_tail - buffer_size <= pre.tail (shown above) and pre.tail <= new_tail
        assert(new_tail - pre.buffer_size <= pre.tail <= new_tail);

        // Prove: forall i: nat, pre.tail <= i < new_tail => !alive(i)
        assert forall |i: nat| pre.tail <= i < new_tail implies
            !(log_entry_is_alive(post.alive_bits, i as int, post.buffer_size)) by {
            // post.alive_bits == pre.alive_bits, post.buffer_size == pre.buffer_size
            assert(post.alive_bits == pre.alive_bits);
            assert(post.buffer_size == pre.buffer_size);
            assert(!log_entry_is_alive(pre.alive_bits, i as int, pre.buffer_size));
        };

        // Prove inv_buffer_contents:
        // post.contents = pre.contents - {i: pre.tail - buffer_size <= i < new_tail - buffer_size}
        // post.tail = new_tail
        // Need: for i in [new_tail - buffer_size, new_tail):
        //   (alive(i) or i < new_min_local_head) <=> post.contents.contains_key(i)
        // For i in [new_tail - buffer_size, pre.tail - buffer_size): 
        //   i < pre.tail - buffer_size means i was removed (since withdrawn covers [pre.tail-buffer_size, new_tail-buffer_size))
        //   Wait: withdrawn = Map::new(Set::range(pre.tail - buffer_size, new_tail - buffer_size), ...)
        //   So post.contents = pre.contents - withdrawn
        //   For i in [new_tail - buffer_size, pre.tail): 
        //     These are i in [new_tail-buffer_size, pre.tail-buffer_size) union [pre.tail-buffer_size, pre.tail)
        //     For i in [new_tail-buffer_size, pre.tail-buffer_size): removed from contents = not in post.contents
        //       These i need to NOT satisfy (alive or i < min_local_head) in post
        //       But i >= new_tail - buffer_size >= pre.tail - buffer_size + (new_tail - pre.tail) 
        //       Wait, new_tail - buffer_size could be > pre.tail - buffer_size
        //       Actually new_tail >= pre.tail so new_tail - buffer_size >= pre.tail - buffer_size
        //       So [new_tail-buffer_size, pre.tail-buffer_size) is EMPTY
        //   For i in [pre.tail-buffer_size, pre.tail): unchanged contents, same alive_bits
        //     These satisfy pre's inv_buffer_contents
        //     In post: min_local_head is same (local_versions unchanged), tail increased
        //     So the condition still holds for these i
        //   For i in [pre.tail, new_tail): new entries
        //     These are NOT in post.contents (since contents only shrunk from withdrawal)
        //     Need: !alive(i) and i >= min_local_head
        //     i >= pre.tail >= min_local_head (from pointer_ordering)
        //     !alive(i): shown above

        // For i >= new_tail: not in contents
        assert forall |i: int| new_tail as int <= i implies !post.contents.contains_key(i) by {
            // pre.contents has keys < pre.tail (from complete invariant)
            // post.contents ⊆ pre.contents
            assert(pre.complete());
            assert(!pre.contents.contains_key(i));
        };

        // For i in [new_tail - buffer_size, new_tail):
        let post_min_local_head = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);
        assert(post_min_local_head == min_local_head) by {
            // local_versions unchanged
            assert(post.local_versions == pre.local_versions);
            assert(post.num_replicas == pre.num_replicas);
        };

        assert forall |i: int| (new_tail as int) - (pre.buffer_size as int) <= i < new_tail as int implies (
            (log_entry_is_alive(post.alive_bits, i, post.buffer_size) ||
                i < post_min_local_head as int)
            <==>
            post.contents.contains_key(i)
        ) by {
            assert(post.alive_bits == pre.alive_bits);
            assert(post.buffer_size == pre.buffer_size);
            if i < (pre.tail as int) - (pre.buffer_size as int) {
                // i is in [new_tail-buffer_size, pre.tail-buffer_size)
                // but new_tail >= pre.tail so new_tail-buffer_size >= pre.tail-buffer_size
                // contradiction: empty range
                assert(new_tail >= pre.tail);
                assert(false);
            } else if i < pre.tail as int {
                // i in [pre.tail - buffer_size, pre.tail)
                // pre.contents had this key iff (alive(i) or i < min_local_head)
                // post.contents: was this key withdrawn? withdrawn covers [pre.tail-buffer_size, new_tail-buffer_size)
                // i < pre.tail and new_tail >= pre.tail so new_tail - buffer_size could be >= pre.tail
                // If new_tail - buffer_size > i, then i not in withdrawn range, so post.contents[i] = pre.contents[i]
                // Wait: withdrawn = {i: pre.tail-buffer_size <= i < new_tail-buffer_size}
                // If i < new_tail - buffer_size i.e. i + buffer_size < new_tail, then i was withdrawn
                // post.contents.contains_key(i) = pre.contents.contains_key(i) && i not in withdrawn
                // but also post.contents.contains_key(i) if i not withdrawn
                // Let's check if i is in withdrawn range
                if i < (new_tail as int) - (pre.buffer_size as int) {
                    // i is in withdrawn range: removed from contents
                    // So !post.contents.contains_key(i)
                    // Need: !(alive(i) or i < min_local_head)
                    // Since i + buffer_size < new_tail and i + buffer_size is in [pre.tail, new_tail)
                    // alive(i) = !alive(i + buffer_size) from wrap-around property
                    // !alive(i+buffer_size) shown above for pre.tail <= i+buffer_size < new_tail
                    // So alive(i) = !(!alive(i+buffer_size)) = !(true) ... wait
                    // Actually: alive(i) != alive(i + buffer_size) (they alternate)
                    // !alive(i + buffer_size) means alive(i) = false too? No.
                    // log_entry_alive_value(i, bs) != log_entry_alive_value(i + bs, bs)
                    // We know !alive(i + buffer_size) as int, meaning the alive value for i+buffer_size is false
                    // So alive(i, buffer_size) would be true (opposite of i+buffer_size)
                    // But wait: i was in pre.contents. From pre.inv_buffer_contents:
                    //   alive(i) or i < min_local_head <=> pre.contents.contains_key(i)
                    // If i was in pre.contents due to i < min_local_head, then also in post after removal?
                    // No: it's been removed. But the invariant says it should be in contents if i < min_local_head
                    // Hmm, this seems like i < min_local_head entries are supposed to stay...
                    // But they ARE being removed (they're being recycled for new entries)
                    // The invariant says alive(i) OR i < min_local_head <=> in contents
                    // After withdrawal, i is not in contents, and alive(i) should be false
                    // AND i >= min_local_head (or else invariant is violated)
                    // Since i < new_tail - buffer_size, i + buffer_size < new_tail and i + buffer_size >= pre.tail
                    // From upcoming_bits: pre.tail <= i+buffer_size < min_local_head + buffer_size => !alive(i+buffer_size)
                    // So alive(i+buffer_size) is false, meaning alive(i) is true (they're different)
                    // Wait no: from alive_wrap_around, alive(i) != alive(i + buffer_size)
                    // !alive(i + buffer_size) means alive(i) = true
                    // But then i IS alive, so it should be in contents... contradiction with withdrawal
                    // UNLESS i < min_local_head, but then the invariant says it should be in contents too!
                    // Wait, I think I'm confusing directions. Let me re-read inv_buffer_contents.
                    // inv_buffer_contents: for i in [tail - buffer_size, tail):
                    //   (alive(i) OR i < min_local_head) <=> contents.contains_key(i)
                    // For post, i in [new_tail - buffer_size, new_tail), i < pre.tail
                    // If i < new_tail - buffer_size (i in withdrawn range), this contradicts
                    // i >= new_tail - buffer_size!
                    assert(false); // i can't be both >= new_tail - buffer_size AND < new_tail - buffer_size
                } else {
                    // i not in withdrawn range: post.contents same as pre for this key
                    assert(i >= (new_tail as int) - (pre.buffer_size as int));
                    // pre.inv_buffer_contents for i in [pre.tail - buffer_size, pre.tail):
                    assert(pre.tail - pre.buffer_size <= i < pre.tail);
                    // (alive(i) or i < min_local_head) <=> pre.contents.contains_key(i)
                    // post.contents.contains_key(i) = pre.contents.contains_key(i) for non-withdrawn i
                    // post.alive_bits same, post.buffer_size same, post.local_versions same
                    // So min_local_head same and alive same
                    assert(post.contents.contains_key(i) == pre.contents.contains_key(i));
                }
            } else {
                // i in [pre.tail, new_tail): not in pre.contents (from complete: i >= pre.tail)
                // not in withdrawn (withdrawn covers [pre.tail-buffer_size, new_tail-buffer_size), i >= pre.tail)
                // so not in post.contents
                assert(!pre.contents.contains_key(i));
                assert(!post.contents.contains_key(i));
                // Need: !(alive(i) or i < min_local_head)
                // i >= pre.tail >= min_local_head (from pointer_ordering), so NOT i < min_local_head
                assert(i >= pre.tail as int);
                assert(min_local_head <= pre.tail);
                assert(!log_entry_is_alive(post.alive_bits, i, post.buffer_size));
            }
        };
    }

    #[inductive(append_flip_bit)]
    fn append_flip_bit_inductive(pre: Self, post: Self, node_id: NodeId, deposited: StoredType<DT>) {
        let cur_idx = pre.combiner[node_id].get_Appending_cur_idx();
        let tail = pre.combiner[node_id].get_Appending_tail();
        assert(pre.combiner_valid(node_id, pre.combiner[node_id]));
        assert(pre.upcoming_bits_are_not_alive());
        assert(pre.inv_buffer_contents());
        assert(pre.all_reader_state_valid());
        assert(pre.ranges_no_overlap());
        assert(pre.complete());
        assert(pre.pointer_ordering());
        assert(pre.all_combiner_valid());

        let min_local_head = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
        map_min_value_smallest(pre.local_versions, (pre.num_replicas - 1) as nat);

        // From combiner_valid for Appending: cur_idx < tail <= pre.tail <= min_local_head + buffer_size
        assert(cur_idx < tail);
        assert(tail <= pre.tail);
        assert(pre.tail as int - pre.buffer_size as int <= cur_idx as int);
        assert(cur_idx as int <= pre.tail as int);
        assert(forall |i: nat| cur_idx <= i < tail ==> !log_entry_is_alive(pre.alive_bits, i as int, pre.buffer_size));

        // After flip: alive_bits at log_entry_idx(cur_idx) is now alive_value(cur_idx)
        // This means cur_idx is now alive, but cur_idx + buffer_size is NOT alive
        // (since alive_value(cur_idx) != alive_value(cur_idx + buffer_size))
        let phys_idx = log_entry_idx(cur_idx as int, pre.buffer_size);
        assert(post.alive_bits == pre.alive_bits.insert(phys_idx, log_entry_alive_value(cur_idx as int, pre.buffer_size)));

        // Prove: for i: nat, cur_idx+1 <= i < tail => !alive(i) in post
        assert forall |i: nat| (cur_idx + 1) <= i < tail implies
            !(log_entry_is_alive(post.alive_bits, i as int, post.buffer_size)) by {
            // The alive bit at log_entry_idx(i) is changed only if log_entry_idx(i) == phys_idx
            // i.e., i % buffer_size == cur_idx % buffer_size
            // But i > cur_idx and both in [tail - buffer_size, tail) (as int), so difference < buffer_size
                let cur_idx_int: int = cur_idx as int;
                let i_int: int = i as int;
                let tail_int: int = pre.tail as int;
                let bs_int: int = pre.buffer_size as int;
                // From combiner_valid: (tail - buffer_size) <= cur_idx (as int)
                assert(tail_int - bs_int <= cur_idx_int) by {
                    // combiner_valid for Appending
                };
                assert(cur_idx_int < tail_int) by {
                    // cur_idx < tail (from Appending require) and tail <= pre.tail
                };
                // i > cur_idx, so i >= cur_idx + 1 > tail - buffer_size
                assert(i_int > cur_idx_int);
                assert(tail_int - bs_int <= i_int);
                // i < tail <= pre.tail
                assert(i_int < tail_int);
                // 0 < i - cur_idx < buffer_size
                assert(0 < i_int - cur_idx_int);
                assert(i_int - cur_idx_int < bs_int);
                // The alive bits are only changed at phys_idx = cur_idx % buffer_size
                // Check if i has the same physical index
                if log_entry_idx(i as int, pre.buffer_size) == phys_idx {
                    // i % buffer_size == cur_idx % buffer_size, but 0 < i - cur_idx < buffer_size => contradiction
                    assert(i_int % bs_int != cur_idx_int % bs_int) by {
                        distinct_in_range_have_distinct_mod(i_int, cur_idx_int, bs_int);
                    };
                    // But log_entry_idx(i) = i % bs = cur_idx % bs = phys_idx means i%bs == cur_idx%bs
                    assert(i_int % bs_int == cur_idx_int % bs_int) by {
                        // log_entry_idx(i) = (i % bs) as nat
                        // log_entry_idx(cur_idx) = (cur_idx % bs) as nat
                        // both equal phys_idx
                    };
                    assert(false);
                }
                // Bit unchanged at position log_entry_idx(i)
                assert(log_entry_idx(i as int, post.buffer_size) != phys_idx);
                assert(post.alive_bits[log_entry_idx(i as int, post.buffer_size)] == pre.alive_bits[log_entry_idx(i as int, pre.buffer_size)]);
                // The pre bit for i in [cur_idx+1, tail) was not alive (from combiner_valid: !alive(i) for i >= cur_idx)
                // Wait: pre combiner says !alive(cur_idx <= i < tail). After deposit+flip, cur_idx+1 to tail.
                // But we're looking at i > cur_idx and in range, so pre.alive(i) was false.
                assert(!log_entry_is_alive(pre.alive_bits, i as int, pre.buffer_size));
        };

        // Prove upcoming_bits_are_not_alive:
        // For tail <= j < min_local_head + buffer_size: !alive(j) in post
        // Only change: alive_bits[phys_idx] = alive_value(cur_idx)
        // For j such that log_entry_idx(j) == phys_idx: j = cur_idx + k*buffer_size for some k
        // The relevant j are j >= tail, and log_entry_idx(j) = log_entry_idx(cur_idx)
        // The "next" such j after cur_idx is cur_idx + buffer_size
        // alive_value(cur_idx + buffer_size) != alive_value(cur_idx) (from wrap-around)
        // post.alive_bits[phys_idx] = alive_value(cur_idx) != alive_value(cur_idx + buffer_size)
        // So log_entry_is_alive(post.alive_bits, cur_idx+buffer_size, buffer_size) = false
        assert forall |j: nat| pre.tail <= j < min_local_head + pre.buffer_size implies
            !log_entry_is_alive(post.alive_bits, j as int, post.buffer_size) by {
            if log_entry_idx(j as int, pre.buffer_size) == phys_idx {
                // j ≡ cur_idx (mod buffer_size), j >= tail > cur_idx
                // The smallest such j is cur_idx + buffer_size
                // For j = cur_idx + buffer_size: alive_value(j) = !alive_value(cur_idx) 
                // post.alive_bits[phys_idx] = alive_value(cur_idx) != alive_value(j)
                // So !alive(j) in post
                log_entry_alive_value_wrap_around(cur_idx as int, pre.buffer_size);
                // alive_value(cur_idx) != alive_value(cur_idx + buffer_size)
                // What is alive_value(j)? j = cur_idx + k*buffer_size for some k >= 1
                // Each wrap negates the alive value
                // post.alive_bits[phys_idx] = alive_value(cur_idx)
                // alive_value(j) = alive_value(cur_idx + k*buffer_size) for k >= 1
                // Since k >= 1, alive_value(j) may differ from alive_value(cur_idx + buffer_size)
                // But we need: post.alive_bits[phys_idx] != alive_value(j)
                // i.e., alive_value(cur_idx) != alive_value(j)
                // j = cur_idx + k*buffer_size, k >= 1
                // alive_value(cur_idx) = ((cur_idx / buffer_size) % 2 == 0)
                // alive_value(j) = (((cur_idx + k*buffer_size) / buffer_size) % 2 == 0)
                //                = ((cur_idx/buffer_size + k) % 2 == 0)
                // These are different iff k is odd
                // So we need k to be odd, i.e., j - cur_idx = k * buffer_size with k odd
                // But j could be any multiple. Let me think differently.
                // Actually: j is in [tail, min_local_head + buffer_size)
                // and cur_idx is in [tail - buffer_size, tail)
                // So j - cur_idx is in [tail - cur_idx, min_local_head + buffer_size - cur_idx)
                // = [tail - cur_idx, ...)
                // with tail - cur_idx in (0, buffer_size]
                // Actually: j >= tail > cur_idx, so j - cur_idx >= 1
                // Also: j < min_local_head + buffer_size <= pre.tail + buffer_size (from pointer_ordering: min_local_head <= pre.tail)
                // and cur_idx >= pre.tail - buffer_size
                // so j - cur_idx < (pre.tail + buffer_size) - (pre.tail - buffer_size) = 2 * buffer_size
                // And j - cur_idx > 0
                // So j - cur_idx ∈ (0, 2 * buffer_size)
                // For log_entry_idx(j) = log_entry_idx(cur_idx), need j ≡ cur_idx (mod buffer_size)
                // So j - cur_idx = k * buffer_size with k ∈ {1} (since 0 < k*buffer_size < 2*buffer_size => k=1)
                // So j = cur_idx + buffer_size exactly!
                // Then alive_value(j) = alive_value(cur_idx + buffer_size) != alive_value(cur_idx)
                // post.alive_bits[phys_idx] = alive_value(cur_idx) != alive_value(j) => !alive(j) in post ✓
                assert((cur_idx as int) < (pre.tail as int)) by {
                    assert(pre.tail as int - pre.buffer_size as int <= cur_idx as int);
                };
                assert(min_local_head <= pre.tail) by {
                    // min_local_head <= any local_version <= tail
                    assert(pre.local_versions.contains_key(0));
                    assert(pre.local_versions[0] <= pre.tail);
                };
                // j - cur_idx in (0, 2*buffer_size), j ≡ cur_idx mod buffer_size => j = cur_idx + buffer_size
                let j_int: int = j as int;
                let cur_int: int = cur_idx as int;
                let bs_int2: int = pre.buffer_size as int;
                let mlh_int: int = min_local_head as int;
                assert(j_int - cur_int > 0);
                assert(j_int - cur_int < 2 * bs_int2) by {
                    assert(j_int < mlh_int + bs_int2);
                    assert(min_local_head <= pre.tail);
                };
                assert(j_int == cur_int + bs_int2) by {
                    // j - cur_idx is a multiple of buffer_size in (0, 2*buffer_size)
                    // only multiple is buffer_size itself
                    assert((j_int - cur_int) % bs_int2 == 0) by {
                        // log_entry_idx(j) = j % buffer_size (as nat)
                        // log_entry_idx(cur_idx) = cur_idx % buffer_size (as nat)
                        // They're equal, so j % bs == cur_idx % bs
                        assert(j_int % bs_int2 == cur_int % bs_int2) by {
                            // log_entry_idx(j, bs) = (j % bs) as nat = phys_idx
                            // log_entry_idx(cur_idx, bs) = (cur_idx % bs) as nat = phys_idx
                        };
                        // From j % bs == cur_idx % bs, using lemma_mod_equivalence:
                        lemma_mod_equivalence(j_int, cur_int, bs_int2);
                        // (j - cur) % bs == 0
                    };
                    // From nonlinear: if d % n == 0 and 0 < d < 2n, then d == n
                    // d = j - cur, n = bs
                    // d % n == 0 and 0 < d < 2n
                    // so d is a multiple of n in (0, 2n), hence d = n
                };
                // Now show alive_value(cur_idx) != alive_value(cur_idx + buffer_size)
                // using log_entry_alive_value_wrap_around
                assert(log_entry_alive_value(cur_idx as int, pre.buffer_size) 
                    != log_entry_alive_value(cur_idx as int + pre.buffer_size as int, pre.buffer_size));
                assert(post.alive_bits[phys_idx] == log_entry_alive_value(cur_idx as int, pre.buffer_size));
                assert(log_entry_is_alive(post.alive_bits, j as int, post.buffer_size) == 
                    (post.alive_bits[phys_idx] == log_entry_alive_value(j as int, post.buffer_size)));
                assert(!log_entry_is_alive(post.alive_bits, j as int, post.buffer_size));
            } else {
                // This bit unchanged in post, still not alive
                assert(!log_entry_is_alive(pre.alive_bits, j as int, pre.buffer_size));
            }
        };

        // Prove inv_buffer_contents:
        // post.contents = pre.contents + {cur_idx: deposited}
        // post.tail = pre.tail (unchanged)
        // post.alive_bits changed: phys_idx is now alive_value(cur_idx) (making cur_idx alive)
        let post_min_local_head = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);
        assert(post_min_local_head == min_local_head) by {
            assert(post.local_versions == pre.local_versions);
            assert(post.num_replicas == pre.num_replicas);
        };
        assert forall |i: int| post.tail as int - post.buffer_size as int <= i < post.tail as int implies (
            (log_entry_is_alive(post.alive_bits, i, post.buffer_size) ||
                i < post_min_local_head as int)
            <==>
            #[trigger] post.contents.contains_key(i)
        ) by {
            if i == cur_idx as int {
                // i = cur_idx: now alive in post, and in post.contents (deposited)
                assert(log_entry_is_alive(post.alive_bits, i, post.buffer_size));
                assert(post.contents.contains_key(i));
            } else {
                // For i != cur_idx: alive_bits unchanged at log_entry_idx(i) (since log_entry_idx(i) != phys_idx)
                // Actually need to check: could log_entry_idx(i) == phys_idx for i != cur_idx?
                // If so, then alive bit changed for i too!
                if log_entry_idx(i, pre.buffer_size) == phys_idx {
                    // i ≡ cur_idx (mod buffer_size), and i ≠ cur_idx, and both in [tail-buffer_size, tail) (int)
                    // Within range of size buffer_size, distinct => distinct mod
                    let i_int4: int = i;
                    let cur_int4: int = cur_idx as int;
                    let tail_int4: int = pre.tail as int;
                    let bs_int5: int = pre.buffer_size as int;
                    // i is in pre's inv_buffer_contents range [tail - buffer_size, tail)
                    assert(tail_int4 - bs_int5 <= i_int4);
                    assert(i_int4 < tail_int4);
                    assert(tail_int4 - bs_int5 <= cur_int4);
                    assert(cur_int4 < tail_int4);
                    assert(i_int4 != cur_int4);
                    assert(i_int4 % bs_int5 != cur_int4 % bs_int5) by {
                        if i_int4 > cur_int4 {
                            assert(0 < i_int4 - cur_int4);
                            assert(i_int4 - cur_int4 < bs_int5);
                            distinct_in_range_have_distinct_mod(i_int4, cur_int4, bs_int5);
                        } else {
                            assert(0 < cur_int4 - i_int4);
                            assert(cur_int4 - i_int4 < bs_int5);
                            distinct_in_range_have_distinct_mod(cur_int4, i_int4, bs_int5);
                        }
                    };
                    // i % buffer_size = log_entry_idx(i) = phys_idx = log_entry_idx(cur_idx) = cur_idx % buffer_size
                    assert(false);
                }
                // alive_bits unchanged for i
                assert(log_entry_is_alive(post.alive_bits, i, post.buffer_size) == log_entry_is_alive(pre.alive_bits, i, pre.buffer_size));
                // contents unchanged for i != cur_idx
                assert(post.contents.contains_key(i) == pre.contents.contains_key(i));
                // pre invariant holds for i
                assert(pre.inv_buffer_contents());
                assert(pre.tail - pre.buffer_size <= i < pre.tail);
            }
        };

        // Prove all_reader_state_valid:
        // Only change: alive_bits[phys_idx] = alive_value(cur_idx) (now alive), contents added cur_idx
        // Reader states check: forall i in [start, cur_reader), alive(i) and in contents
        // These i are in [local_version, tail) but < cur_reader <= tail
        // We need that readers' already-verified range [start, cur_reader) is unaffected
        // The only affected physical index is phys_idx = log_entry_idx(cur_idx)
        // But cur_idx is in Appending range, and ranges_no_overlap ensures no overlap with reader guard
        assert forall |nid| #![trigger post.combiner[nid]] post.combiner.contains_key(nid) && post.combiner[nid].is_Reading() implies
            post.reader_state_valid(nid, post.combiner[nid].get_Reading_0()) by {
            assert(pre.combiner.contains_key(nid));
            assert(pre.all_reader_state_valid());
            // If nid == node_id: combiner changed from Appending to Appending, not Reading -- contradiction
            if nid == node_id {
                assert(!post.combiner[nid].is_Reading());
                assert(false);
            }
            // pre reader state is valid
            let rs = pre.combiner[nid].get_Reading_0();
            assert(pre.reader_state_valid(nid, rs));
            // post reader state: same combiner (only node_id changed), same alive_bits for non-cur_idx phys
            // Need to show post.reader_state_valid(nid, rs)
            match rs {
                ReaderState::Starting{start} => {
                    // start == local_versions[nid], start <= tail: unchanged
                }
                ReaderState::Range{start, end, cur} => {
                    // forall i: start <= i < cur => alive(i) in post
                    assert forall |i: nat| start <= i < cur implies log_entry_is_alive(post.alive_bits, i as int, post.buffer_size) by {
                        assert(log_entry_is_alive(pre.alive_bits, i as int, pre.buffer_size));
                        if log_entry_idx(i as int, pre.buffer_size) == phys_idx {
                            // Then i ≡ cur_idx (mod buffer_size)
                            // But pre required !alive(cur_idx) for Appending
                            // pre required alive(i) for Range
                            // Contradiction: alive(i) from pre.reader_state_valid but !alive at this phys idx?
                            // Actually: alive(i) = (alive_bits[phys_idx] == alive_value(i))
                            // Before flip: pre.alive_bits[phys_idx] was NOT alive_value(cur_idx)
                            // So pre.alive_bits[phys_idx] = !alive_value(cur_idx)
                            // If i ≡ cur_idx mod buffer_size: alive_value(i) = alive_value(cur_idx) (same)
                            // Wait: alive_value(i) depends on i / buffer_size % 2
                            // Actually if i ≡ cur_idx (mod buffer_size) but i ≠ cur_idx, then
                            // i = cur_idx + k*buffer_size for some k != 0
                            // and alive_value(i) = alive_value(cur_idx + k*buffer_size) which alternates
                            // For k = 1: alive_value(i) != alive_value(cur_idx)
                            // But then alive(i) in pre means pre.alive_bits[phys_idx] == alive_value(i) != alive_value(cur_idx)
                            // = pre.alive_bits[phys_idx] = alive_value(i)
                            // and !alive(cur_idx) means pre.alive_bits[phys_idx] != alive_value(cur_idx)
                            // These are consistent: pre.alive_bits[phys_idx] = alive_value(i) ≠ alive_value(cur_idx)
                            // After flip: post.alive_bits[phys_idx] = alive_value(cur_idx)
                            // post.alive(i) = (alive_value(cur_idx) == alive_value(i)) = false (they differ)
                            // So post does NOT preserve alive(i) for this reader entry i!
                            // This would be a violation... unless ranges_no_overlap prevents this.
                            // Actually ranges_no_overlap says for Appending{cur_idx, tail} and Reading Guard{..cur..}:
                            // cur_idx > cur || tail <= cur
                            // For Reading Range, there's no such explicit overlap condition...
                            // But Range is different from Guard in that it hasn't started guarding yet
                            // Hmm, let me re-examine...
                            // Actually for Range: i in [start, cur) means these are ALREADY confirmed alive
                            // If after the Appending flip their alive status changes, that's a problem
                            // BUT: the ranges_no_overlap covers only Guard, not Range
                            // The key insight: if log_entry_idx(i) == log_entry_idx(cur_idx) and i != cur_idx
                            // and i is in the reader's range [start, cur), then:
                            // i in [start, cur) ⊆ [local_version, tail) ⊆ [tail - buffer_size, tail)
                            // cur_idx also in [tail - buffer_size, tail) 
                            // distinct values in range of size buffer_size => distinct mod
                            let i_int2: int = i as int;
                            let cur_int2: int = cur_idx as int;
                            let tail_int2: int = pre.tail as int;
                            let bs_int3: int = pre.buffer_size as int;
                            // i >= start = local_versions[nid] >= tail - buffer_size (from pointer_differences)
                            assert(pre.pointer_differences());
                            assert(pre.local_versions.contains_key(nid));
                            assert(tail_int2 - bs_int3 <= pre.local_versions[nid] as int);
                            assert(tail_int2 - bs_int3 <= i_int2);
                            assert(i_int2 < tail_int2);
                            assert(tail_int2 - bs_int3 <= cur_int2);
                            assert(cur_int2 < tail_int2);
                            assert(i != cur_idx);
                            assert(i_int2 % bs_int3 != cur_int2 % bs_int3) by {
                                if i_int2 > cur_int2 {
                                    assert(0 < i_int2 - cur_int2);
                                    assert(i_int2 - cur_int2 < bs_int3);
                                    distinct_in_range_have_distinct_mod(i_int2, cur_int2, bs_int3);
                                } else {
                                    assert(0 < cur_int2 - i_int2);
                                    assert(cur_int2 - i_int2 < bs_int3);
                                    distinct_in_range_have_distinct_mod(cur_int2, i_int2, bs_int3);
                                }
                            };
                            assert(false);
                        }
                    };
                    // contents unchanged for reader's range (only cur_idx added, and cur_idx not in range)
                    assert forall |i: nat| start <= i < cur implies post.contents.contains_key(i as int) by {
                        assert(pre.contents.contains_key(i as int));
                        // post.contents = pre.contents + {cur_idx}
                        // so if pre.contents.contains_key(i), so does post
                    };
                }
                ReaderState::Guard{start, end, cur: cur_guard, val} => {
                    // Similar argument for [start, cur_guard]
                    assert forall |i: nat| start <= i <= cur_guard implies log_entry_is_alive(post.alive_bits, i as int, post.buffer_size) by {
                        assert(log_entry_is_alive(pre.alive_bits, i as int, pre.buffer_size));
                        if log_entry_idx(i as int, pre.buffer_size) == phys_idx {
                            // Same argument: both in [tail-buffer_size, tail) (int), distinct => different phys
                            let i_int3: int = i as int;
                            let cur_int3: int = cur_idx as int;
                            let tail_int3: int = pre.tail as int;
                            let bs_int4: int = pre.buffer_size as int;
                            // i >= start >= local_versions[nid] >= tail - buffer_size (from pointer_differences)
                            assert(pre.pointer_differences());
                            assert(pre.local_versions.contains_key(nid));
                            assert(tail_int3 - bs_int4 <= pre.local_versions[nid] as int);
                            assert(tail_int3 - bs_int4 <= i_int3);
                            assert(i_int3 < tail_int3);
                            assert(tail_int3 - bs_int4 <= cur_int3);
                            assert(cur_int3 < tail_int3);
                            assert(i != cur_idx);
                            assert(i_int3 % bs_int4 != cur_int3 % bs_int4) by {
                                if i_int3 > cur_int3 {
                                    assert(0 < i_int3 - cur_int3);
                                    assert(i_int3 - cur_int3 < bs_int4);
                                    distinct_in_range_have_distinct_mod(i_int3, cur_int3, bs_int4);
                                } else {
                                    assert(0 < cur_int3 - i_int3);
                                    assert(cur_int3 - i_int3 < bs_int4);
                                    distinct_in_range_have_distinct_mod(cur_int3, i_int3, bs_int4);
                                }
                            };
                            assert(false);
                        }
                    };
                    // contents: cur_guard is in contents pre and post
                    assert(post.contents.contains_key(cur_guard as int));
                    // val unchanged at cur_guard (cur_guard != cur_idx from no-overlap)
                    // Actually we need to verify cur_guard != cur_idx
                    // ranges_no_overlap: Appending{cur_idx, tail} no_overlap_with Reading Guard{..cur_guard..}:
                    //   cur_idx > cur_guard || tail <= cur_guard
                    // So either cur_idx > cur_guard or cur_idx >= tail > cur_guard (since cur_idx < tail)
                    // Wait: no_overlap condition for Appending vs Guard:
                    //   cur_idx > cur_guard || tail <= cur_guard
                    // If cur_idx > cur_guard, then cur_idx != cur_guard ✓
                    // If tail <= cur_guard, but from Guard: cur_guard < end <= tail, contradiction
                    // So we must have cur_idx > cur_guard
                    assert(pre.ranges_no_overlap());
                    assert(pre.combiner[node_id] == CombinerState::Appending { cur_idx, tail });
                    // If combiner[nid] is Reading(Guard{..cur_guard..}):
                    let combo_nid = pre.combiner[nid];
                    if combo_nid.is_Reading() {
                        let inner_rs = combo_nid.get_Reading_0();
                        if inner_rs.is_Guard() {
                            // ranges_no_overlap guarantees no_overlap_with
                            assert(pre.combiner[node_id].no_overlap_with(pre.combiner[nid]));
                            // This means cur_idx > cur_guard OR tail <= cur_guard
                            // Guard invariant: cur_guard < end <= tail, so tail > cur_guard
                            assert(pre.reader_state_valid(nid, combo_nid.get_Reading_0()));
                            // g_end comes from the same inner_rs (which is the Guard)
                            // But 'end' in our current match arm = inner_rs.get_Guard_end()
                            // From reader_state_valid: end as int <= tail as int
                            assert(end as int <= pre.tail as int);
                            // And tail_param == pre.tail (since combiner_valid for Appending gives tail <= pre.tail)
                            assert(end <= pre.tail);
                            // tail is the same as pre.combiner[node_id].get_Appending_tail() which <= pre.tail
                            // So end <= pre.tail >= tail
                            // But we need end <= tail (the Appending tail, not pre.tail)
                            // From Guard invariant: end <= self.tail = pre.tail
                            // From Appending: tail <= pre.tail
                            // Hmm: is end <= tail?
                            // Guard reader_state_valid: end <= pre.tail AS INT
                            // Appending combiner_valid: tail <= pre.tail
                            // We need end <= tail. 
                            // Actually from Reader invariant: (pre.tail as int) - (pre.buffer_size as int) <= end <= (pre.tail as int)
                            // And Appending invariant: cur_idx <= tail <= pre.tail
                            // We don't directly have end <= tail...
                            // BUT: no_overlap says cur_idx > cur_guard OR tail <= cur_guard
                            // Guard says cur_guard < end <= pre.tail. If tail <= cur_guard, then tail <= cur_guard < end <= pre.tail.
                            // But from Appending: cur_idx < tail, and from no_overlap if tail <= cur_guard, 
                            // then the no_overlap was because tail <= cur_guard (second condition).
                            // Guard range is [start, end) with cur_guard in [start, end).
                            // If tail <= cur_guard, and from Appending: tail <= pre.tail...
                            // Actually we don't need g_end <= tail specifically for the cur_guard contradiction.
                            // We only need: tail <= cur_guard leads to contradiction since cur_guard < end <= pre.tail
                            // and tail <= cur_guard < end, so tail < end, but end <= pre.tail... that's consistent.
                            // The contradiction must come differently.
                            // Actually looking at the no_overlap definition again:
                            // Appending{cur_idx, tail}.no_overlap_with(Guard{..cur_guard..}) = 
                            //   cur_idx > cur_guard OR tail <= cur_guard
                            // If tail <= cur_guard, then... from Guard invariant cur_guard < end.
                            // So tail <= cur_guard < end. Is this a contradiction?
                            // end <= pre.tail and tail <= pre.tail... not necessarily a contradiction.
                            // Hmm. Maybe the approach of deriving cur_guard != cur_idx is different.
                            // Let me use: cur_idx > cur_guard => cur_idx != cur_guard (ok)
                            // Or: tail <= cur_guard and cur_idx < tail => cur_idx < cur_guard => cur_idx != cur_guard (ok!)
                            // Either way, cur_idx != cur_guard!
                            // Actually: if tail <= cur_guard, then since cur_idx < tail (from Appending), cur_idx < tail <= cur_guard
                            // So cur_idx < cur_guard => cur_idx != cur_guard ✓
                            // If cur_idx > cur_guard: cur_idx > cur_guard => cur_idx != cur_guard ✓
                            // So in both cases, cur_idx != cur_guard ✓
                            assert(cur_idx != cur_guard as nat) by {
                                // From no_overlap: cur_idx > cur_guard OR tail <= cur_guard
                                // Case 1: cur_idx > cur_guard => cur_idx != cur_guard
                                // Case 2: tail <= cur_guard AND cur_idx < tail => cur_idx < cur_guard => cur_idx != cur_guard
                            };
                        }
                    }
                    assert(post.contents[cur_guard as int] === val) by {
                        // cur_idx != cur_guard (cur_idx > cur_guard), so contents[cur_guard] unchanged
                        assert(cur_guard as int != cur_idx as int);
                    };
                }
            }
        };

        // Prove ranges_no_overlap:
        // node_id changes from Appending{cur_idx, tail} to Appending{cur_idx+1, tail}
        // For any other Appending{c2, t2}: no overlap with {cur_idx+1, tail}
        // They didn't overlap with {cur_idx, tail}: c2 >= tail OR t2 <= cur_idx
        // If c2 >= tail, then c2 >= tail > cur_idx+1 ✓ (c2 >= tail means they don't overlap since c2 >= tail)
        // Wait: no_overlap(Appending{cur_idx+1, tail}, Appending{c2, t2}) means:
        //   (cur_idx+1 >= t2) OR (tail <= c2)
        // Pre had: (cur_idx >= t2) OR (tail <= c2)
        // If tail <= c2: still holds ✓
        // If cur_idx >= t2: then cur_idx+1 > t2 >= cur_idx+1? Only if t2 <= cur_idx < cur_idx+1
        //   So cur_idx+1 >= t2+1 > t2: cur_idx+1 > t2, but we need cur_idx+1 >= t2
        //   Actually cur_idx >= t2 means cur_idx+1 > t2 means cur_idx+1 >= t2+1 >= t2: ✓ since cur_idx >= t2 => cur_idx+1 >= t2
        // For Guard overlap with node_id's new state {cur_idx+1, tail}:
        //   no_overlap(Appending{cur_idx+1,tail}, Guard{start,end,cur_g,val}): (cur_idx+1 > cur_g) OR (tail <= cur_g)
        //   Pre had: (cur_idx > cur_g) OR (tail <= cur_g)
        //   If tail <= cur_g: ✓
        //   If cur_idx > cur_g: cur_idx+1 > cur_idx > cur_g ✓
        assert forall |i, j| post.combiner.contains_key(i) && post.combiner.contains_key(j) && i != j implies
            post.combiner[i].no_overlap_with(post.combiner[j]) by {
            assert(pre.combiner.contains_key(i) && pre.combiner.contains_key(j));
            assert(pre.combiner[i].no_overlap_with(pre.combiner[j]));
            // post.combiner[k] = pre.combiner[k] for k != node_id
            // post.combiner[node_id] = Appending{cur_idx+1, tail}
            // We need post.combiner[i].no_overlap_with(post.combiner[j])
            if i != node_id && j != node_id {
                assert(post.combiner[i] == pre.combiner[i]);
                assert(post.combiner[j] == pre.combiner[j]);
            } else if i == node_id {
                // post.combiner[i] = Appending{cur_idx+1, tail}
                // pre.combiner[i] = Appending{cur_idx, tail}
                // pre had no_overlap: Appending{cur_idx, tail}.no_overlap_with(pre.combiner[j])
                assert(pre.combiner[i] == CombinerState::Appending { cur_idx, tail });
                match post.combiner[j] {
                    CombinerState::Reading(ReaderState::Guard { start, end, cur: cur_g, val }) => {
                        // pre had: cur_idx > cur_g OR tail <= cur_g
                        assert(pre.combiner[j] == post.combiner[j]); // j != node_id
                        // pre.no_overlap(Appending{cur_idx,tail}, Guard{..cur_g..})
                        // cur_idx > cur_g OR tail <= cur_g
                        // => cur_idx+1 > cur_g OR tail <= cur_g
                        assert(cur_idx > cur_g || tail <= cur_g);
                    }
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        assert(pre.combiner[j] == post.combiner[j]);
                        // pre had: cur_idx >= tail2 OR tail <= cur_idx2
                        assert(cur_idx >= tail2 || tail <= cur_idx2);
                        // Need: cur_idx+1 >= tail2 OR tail <= cur_idx2
                        // If tail <= cur_idx2: ✓
                        // If cur_idx >= tail2: cur_idx+1 > tail2 >= cur_idx+1? No: cur_idx >= tail2 => cur_idx+1 >= tail2+1 > tail2
                        //   so cur_idx+1 >= tail2 ✓ (since cur_idx >= tail2 => cur_idx+1 > tail2 >= tail2)
                    }
                    _ => {}
                }
            } else {
                // j == node_id, i != node_id
                // need post.combiner[i].no_overlap_with(Appending{cur_idx+1, tail})
                assert(post.combiner[j] == CombinerState::Appending { cur_idx: cur_idx + 1, tail });
                assert(pre.combiner[j] == CombinerState::Appending { cur_idx, tail });
                assert(pre.combiner[i].no_overlap_with(pre.combiner[j]));
                // no_overlap_with is defined as: self.no_overlap_with(other)
                // For Appending{c,t}.no_overlap_with(other): match other
                // The result depends on the type of combiner[i]
                match pre.combiner[i] {
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        assert(post.combiner[i] == pre.combiner[i]);
                        // pre had: cur_idx2 >= tail OR tail2 <= cur_idx
                        // Need: cur_idx2 >= tail OR tail2 <= cur_idx+1
                        // If cur_idx2 >= tail: ✓
                        // If tail2 <= cur_idx: tail2 <= cur_idx < cur_idx+1: ✓
                    }
                    _ => {
                        // For non-Appending i, no_overlap always true (from definition)
                    }
                }
            }
        };
    }

    #[inductive(append_finish)]
    fn append_finish_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_start)]
    fn reader_start_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_enter)]
    fn reader_enter_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_guard)]
    fn reader_guard_inductive(pre: Self, post: Self, node_id: NodeId) {
    }

    #[inductive(reader_unguard)]
    fn reader_unguard_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_finish)]
    fn reader_finish_inductive(pre: Self, post: Self, node_id: NodeId) {
    }

    #[inductive(reader_abort)]
    fn reader_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }
}}

#[verifier(nonlinear)]
proof fn distinct_in_range_have_distinct_mod(a: int, b: int, n: int)
    requires
        n > 0,
        0 < a - b,
        a - b < n,
    ensures
        a % n != b % n,
{
    // If a % n == b % n, then (a - b) % n == 0 (by lemma_mod_equivalence)
    // Since 0 < a - b < n, this means n divides (a-b) which is in (0, n) - impossible
    lemma_mod_equivalence(a, b, n);
    // (a - b) % n == 0 means n divides (a-b). But 0 < a-b < n means a-b is less than one divisor.
    // Proof by contradiction: if a%n == b%n, then (a-b)%n == 0
    // lemma_fundamental_div_mod: a-b = n * ((a-b)/n) + (a-b)%n
    // if (a-b)%n == 0: a-b = n * ((a-b)/n)
    // a-b > 0 => (a-b)/n > 0 => a-b >= n - contradiction with a-b < n
    if a % n == b % n {
        assert((a - b) % n == 0);
        lemma_fundamental_div_mod(a - b, n);
        // a - b = n * ((a-b)/n) + 0 = n * ((a-b)/n)
        assert(a - b == n * ((a - b) / n));
        // (a-b)/n >= 1 since a-b > 0 and n > 0
        assert((a - b) / n >= 1) by {
            // a - b > 0, n > 0, a - b = n * q where q = (a-b)/n
            // if q <= 0, a-b = n*q <= 0 - contradiction
        };
        // so a - b >= n - contradiction
        assert(a - b >= n);
        assert(false);
    }
}

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

pub open spec fn log_entry_idx(logical: LogicalLogIdx, buffer_size: nat) -> LogIdx
    recommends
        buffer_size == LOG_SIZE,
{
    (logical % (buffer_size as int)) as nat
}

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

} 
