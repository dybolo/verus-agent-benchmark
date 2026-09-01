
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
        assert forall |i, j| post.combiner.contains_key(i) && post.combiner.contains_key(j) && i != j implies
            post.combiner[i].no_overlap_with(post.combiner[j]) by {
            if i != node_id && j != node_id {
                assert(pre.combiner.contains_key(i) && pre.combiner.contains_key(j));
                assert(pre.combiner[i].no_overlap_with(pre.combiner[j]));
            } else if i == node_id {
                assert(post.combiner[i] === CombinerState::Appending { cur_idx: pre.combiner[node_id].get_Appending_cur_idx() + 1, tail: pre.combiner[node_id].get_Appending_tail() });
                assert(pre.combiner[node_id].no_overlap_with(pre.combiner[j]));
                match post.combiner[j] {
                    CombinerState::Reading(ReaderState::Guard { cur, .. }) => {
                        assert(pre.combiner[node_id].get_Appending_cur_idx() > cur || pre.combiner[node_id].get_Appending_tail() <= cur);
                    },
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        assert(pre.combiner[node_id].get_Appending_cur_idx() >= tail2 || pre.combiner[node_id].get_Appending_tail() <= cur_idx2);
                    },
                    _ => { }
                }
            } else {
                assert(post.combiner[j] === CombinerState::Appending { cur_idx: pre.combiner[node_id].get_Appending_cur_idx() + 1, tail: pre.combiner[node_id].get_Appending_tail() });
                assert(pre.combiner[i].no_overlap_with(pre.combiner[node_id]));
                match post.combiner[i] {
                    CombinerState::Appending { cur_idx: cur_idx2, tail: tail2 } => {
                        assert(cur_idx2 >= pre.combiner[node_id].get_Appending_tail() || tail2 <= pre.combiner[node_id].get_Appending_cur_idx());
                    },
                    _ => { }
                }
            }
        };
        assert forall |i| post.tail <= i < map_min_value(post.local_versions, (post.num_replicas - 1) as nat) + post.buffer_size implies
            !log_entry_is_alive(post.alive_bits, i, post.buffer_size) by {
            let cur = pre.combiner[node_id].get_Appending_cur_idx();
            assert(pre.tail <= i < map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat) + pre.buffer_size);
            assert(map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat) <= pre.tail);
            assert(i < pre.tail + pre.buffer_size);
            assert(pre.tail - pre.buffer_size <= cur < pre.tail);
            assert(cur <= i < cur + pre.buffer_size);
            assert(log_entry_idx(i, pre.buffer_size) != log_entry_idx(cur as int, pre.buffer_size)) by {
                log_entry_idx_wrap_around(cur, pre.buffer_size, i as nat);
            }
            assert(!log_entry_is_alive(pre.alive_bits, i, pre.buffer_size));
            assert(post.alive_bits[log_entry_idx(i, post.buffer_size)] == pre.alive_bits[log_entry_idx(i, pre.buffer_size)]);
        };

        let cur = pre.combiner[node_id].get_Appending_cur_idx();
        assert(!log_entry_is_alive(pre.alive_bits, cur as int, pre.buffer_size));
        assert(log_entry_is_alive(post.alive_bits, cur as int, post.buffer_size));
        assert(post.contents.contains_key(cur as int));
        assert forall |i: int| post.tail - post.buffer_size <= i < post.tail implies
            ((log_entry_is_alive(post.alive_bits, i, post.buffer_size) ||
                i < map_min_value(post.local_versions, (post.num_replicas - 1) as nat))
                <==> post.contents.contains_key(i)) by {
            if i == cur {
                assert(pre.tail - pre.buffer_size <= i < pre.tail);
            } else if log_entry_idx(i, pre.buffer_size) == log_entry_idx(cur as int, pre.buffer_size) {
                assert(log_entry_alive_value(i, pre.buffer_size) != log_entry_alive_value(cur as int, pre.buffer_size));
                assert(!log_entry_is_alive(post.alive_bits, i, post.buffer_size));
                assert(!pre.contents.contains_key(i) || i < map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat));
            } else {
                assert(post.contents.contains_key(i) == pre.contents.contains_key(i));
                assert(log_entry_is_alive(post.alive_bits, i, post.buffer_size) ==
                    log_entry_is_alive(pre.alive_bits, i, pre.buffer_size));
                assert(pre.tail - pre.buffer_size <= i < pre.tail);
                assert((log_entry_is_alive(pre.alive_bits, i, pre.buffer_size) ||
                    i < map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat))
                    <==> pre.contents.contains_key(i));
            }
        };
        assert forall |i: int| post.tail <= i implies !post.contents.contains_key(i) by {
            assert(pre.tail <= i);
            assert(post.contents.contains_key(i) == pre.contents.contains_key(i));
            assert(!pre.contents.contains_key(i));
        };
        assert(pre.combiner_valid(node_id, pre.combiner[node_id]));
        assert(pre.local_versions[node_id] <= cur);
        assert(cur < pre.combiner[node_id].get_Appending_tail());
        assert(cur + 1 <= pre.combiner[node_id].get_Appending_tail());
        assert(pre.tail - pre.buffer_size <= cur + 1 <= pre.tail);
        assert(post.combiner_valid(node_id, post.combiner[node_id]));
        assert forall |n| post.combiner.contains_key(n) implies post.combiner_valid(n, post.combiner[n]) by {
            if n == node_id {
                assert(post.combiner_valid(node_id, post.combiner[node_id]));
            } else {
                assert(pre.all_combiner_valid());
                assert(pre.combiner_valid(n, pre.combiner[n]));
                assert(post.combiner[n] === pre.combiner[n]);
            }
        };
        assert forall |n| post.combiner.contains_key(n) && post.combiner[n].is_Reading() implies
            post.reader_state_valid(n, post.combiner[n].get_Reading_0()) by {
            assert(n != node_id);
            assert(pre.all_reader_state_valid());
            assert(pre.reader_state_valid(n, pre.combiner[n].get_Reading_0()));
            assert(post.combiner[n] === pre.combiner[n]);
            assert(post.reader_state_valid(n, post.combiner[n].get_Reading_0())) by {
                match post.combiner[n].get_Reading_0() {
                    ReaderState::Starting { .. } => { }
                    ReaderState::Range { start, end, cur: reader_cur } => {
                        assert forall |k| start <= k < reader_cur implies
                            log_entry_is_alive(post.alive_bits, k, post.buffer_size) by {
                            assert(log_entry_is_alive(pre.alive_bits, k, pre.buffer_size));
                        };
                        assert forall |k| start <= k < reader_cur implies
                            post.contents.contains_key(k) by {
                            assert(pre.contents.contains_key(k));
                            assert(post.contents.contains_key(k));
                        };
                    }
                    ReaderState::Guard { start, end, cur: reader_cur, val } => {
                        assert(log_entry_is_alive(post.alive_bits, reader_cur as int, post.buffer_size));
                        assert(post.contents.contains_key(reader_cur as int));
                        assert(post.contents[reader_cur as int] === val);
                    }
                }
            };
        };
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
