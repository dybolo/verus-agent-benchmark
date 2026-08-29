#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::*;

use vstd::map::Map;
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::set::Set;

fn main() {}

verus! {


pub type NodeId = nat;
pub type LogIdx = nat;
pub type ReqId = nat;
pub type ThreadId = nat;

#[verus::trusted]
pub trait Dispatch: Sized {
    type ReadOperation: Sized;
    type WriteOperation: Sized + Send;
    type Response: Sized;
    type View;

    spec fn view(&self) -> Self::View;

    #[verifier(external_body)]
    fn init() -> (res: Self)
        ensures
            res@ == Self::init_spec(),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    fn clone_write_op(op: &Self::WriteOperation) -> (res: Self::WriteOperation)
        ensures
            op == res,
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    fn clone_response(op: &Self::Response) -> (res: Self::Response)
        ensures
            op == res,
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    fn dispatch(&self, op: Self::ReadOperation) -> (result: Self::Response)
        ensures
            Self::dispatch_spec(self@, op) == result,
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> (result: Self::Response)
        ensures
            Self::dispatch_mut_spec(old(self)@, op) == (final(self)@, result),
    {
        unimplemented!()
    }

    spec fn init_spec() -> Self::View;

    spec fn dispatch_spec(ds: Self::View, op: Self::ReadOperation) -> Self::Response;

    spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (
        Self::View,
        Self::Response,
    );
}

#[is_variant]
#[verus::trusted]
pub enum InputOperation<DT: Dispatch> {
    Read(DT::ReadOperation),
    Write(DT::WriteOperation),
}

#[is_variant]
#[verus::trusted]
pub enum OutputOperation<DT: Dispatch> {
    Read(DT::Response),
    Write(DT::Response),
}

#[verus::trusted]
pub open spec fn add_ticket<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    input: InputOperation<DT>,
    rid: ReqId,
) -> bool {
    !pre.local_reads.dom().contains(rid) && !pre.local_updates.dom().contains(rid) && (match input {
        InputOperation::Read(read_op) => {
            post == UnboundedLog::State::<DT> {
                local_reads: pre.local_reads.insert(
                    rid,
                    ReadonlyState::Init { op: read_op },
                ),
                ..pre
            }
        },
        InputOperation::Write(write_op) => {
            post == UnboundedLog::State::<DT> {
                local_updates: pre.local_updates.insert(
                    rid,
                    UpdateState::Init { op: write_op },
                ),
                ..pre
            }
        },
    })
}

#[verus::trusted]
pub open spec fn consume_stub<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    output: OutputOperation<DT>,
    rid: ReqId,
) -> bool {
    match output {
        OutputOperation::Read(response) => {
            pre.local_reads.dom().contains(rid) && pre.local_reads[rid].is_Done()
                && pre.local_reads[rid].get_Done_ret() == response && post == UnboundedLog::State::<
                DT,
            > { local_reads: pre.local_reads.remove(rid), ..pre }
        },
        OutputOperation::Write(response) => {
            pre.local_updates.dom().contains(rid) && pre.local_updates[rid].is_Done()
                && pre.local_updates[rid].get_Done_ret() == response && post
                == UnboundedLog::State::<DT> { local_updates: pre.local_updates.remove(rid), ..pre }
        },
    }
}


pub tracked struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
}

pub struct ConcreteLogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: u64,
}


pub open spec fn seq_unique<A>(seq: Seq<A>) -> bool {
    forall|i: int, j: int|
        (0 <= i < seq.len() && 0 <= j < seq.len() && i != j) ==> seq.index(i as int) !== seq.index(
            j as int,
        )
}

pub open spec fn seq_disjoint<A>(s: Seq<A>, t: Seq<A>) -> bool {
    forall|i, j| 0 <= i < s.len() && 0 <= j < t.len() ==> s.index(i) !== t.index(j)
}

pub open spec fn seq_to_set<A>(seq: Seq<A>) -> Set<A> {
    seq.to_set()
}

pub open spec fn map_new_rec<V>(dom: nat, val: V) -> Map<nat, V>
    decreases dom,
    when dom >= 0
{
    if dom == 0 {
        map![ dom => val]
    } else {
        map_new_rec((dom - 1) as nat, val).insert(dom, val)
    }
}

#[verifier::external_body]
pub proof fn map_new_rec_dom_finite<V>(dom: nat, val: V)
    ensures
        map_new_rec(dom, val).dom().finite(),
        forall|n: nat| 0 <= n <= dom <==> map_new_rec(dom, val).contains_key(n),
        forall|n|
            (#[trigger] map_new_rec(dom, val).contains_key(n)) ==> map_new_rec(dom, val)[n] == val,
{
}

pub open spec fn map_contains_value<K, V>(map: Map<K, V>, val: V) -> bool {
    exists|i: K| #[trigger] map.contains_key(i) && map.index(i) == val
}

pub open spec fn range(low: nat, mid: nat, high: nat) -> bool {
    low <= mid && mid < high
}

pub open spec fn rangeincl(low: nat, mid: nat, high: nat) -> bool {
    low <= mid && mid <= high
}

#[verifier(nonlinear)]
#[verifier::external_body]
pub proof fn int_mod_less_than_same(i: int, len: int)
    requires
        0 <= i < len,
        len > 0,
    ensures
        (i % len) == i,
{
}

#[is_variant]
pub ghost enum ReadonlyState<DT: Dispatch> {
    Init { op: DT::ReadOperation },
    VersionUpperBound { op: DT::ReadOperation, version_upper_bound: LogIdx },
    ReadyToRead { op: DT::ReadOperation, version_upper_bound: LogIdx, node_id: NodeId },
    Done { op: DT::ReadOperation, version_upper_bound: LogIdx, node_id: NodeId, ret: DT::Response },
}

impl<DT: Dispatch> ReadonlyState<DT> {
    pub open spec fn op(self) -> DT::ReadOperation {
        match self {
            ReadonlyState::Init { op, .. } => op,
            ReadonlyState::VersionUpperBound { op, .. } => op,
            ReadonlyState::ReadyToRead { op, .. } => op,
            ReadonlyState::Done { op, .. } => op,
        }
    }
}

#[is_variant]
pub ghost enum UpdateState<DT: Dispatch> {
    Init { op: DT::WriteOperation },
    Placed { op: DT::WriteOperation, idx: LogIdx },
    Applied { ret: DT::Response, idx: LogIdx },
    Done { ret: DT::Response, idx: LogIdx },
}

#[is_variant]
pub ghost enum CombinerState {
    Ready,
    Placed { queued_ops: Seq<ReqId> },
    LoadedLocalVersion { queued_ops: Seq<ReqId>, lversion: LogIdx },
    Loop {
        queued_ops: Seq<ReqId>,
        lversion: LogIdx,
        idx: nat,
        tail: LogIdx,
    },
    UpdatedVersion { queued_ops: Seq<ReqId>, tail: LogIdx },
}

impl CombinerState {
    pub open spec fn queued_ops(self) -> Seq<ReqId> {
        match self {
            CombinerState::Ready => Seq::empty(),
            CombinerState::Placed { queued_ops } => queued_ops,
            CombinerState::LoadedLocalVersion { queued_ops, .. } => queued_ops,
            CombinerState::Loop { queued_ops, .. } => queued_ops,
            CombinerState::UpdatedVersion { queued_ops, .. } => queued_ops,
        }
    }

    pub open spec fn queued_ops_set(&self) -> Set<ReqId> {
        seq_to_set(self.queued_ops())
    }
}

} 
tokenized_state_machine! {
UnboundedLog<DT: Dispatch> {
    fields {
        #[sharding(constant)]
        pub num_replicas: nat,

        #[sharding(map)]
        pub log: Map<LogIdx, LogEntry<DT>>,

        #[sharding(variable)]
        pub tail: nat,

        #[sharding(map)]
        pub replicas: Map<NodeId, DT::View>,

        #[sharding(map)]
        pub local_versions: Map<NodeId, LogIdx>, 

        #[sharding(variable)]
        pub version_upper_bound: LogIdx, 

        #[sharding(map)]
        pub local_reads: Map<ReqId, ReadonlyState<DT>>,

        #[sharding(map)]
        pub local_updates: Map<ReqId, UpdateState<DT>>,

        #[sharding(map)]
        pub combiner: Map<NodeId, CombinerState>
    }



    #[invariant]
    pub fn inv_request_ids_finite(&self) -> bool {
        &&& self.local_reads.dom().finite()
        &&& self.local_updates.dom().finite()
        &&& self.combiner.dom().finite()
    }



    #[invariant]
    pub fn inv_local_combiner_complete(&self) -> bool {
        forall |node_id: NodeId| 0 <= node_id < self.num_replicas <==>
            self.combiner.contains_key(node_id)
    }

    #[invariant]
    pub fn combiner_local_versions_domains(&self) -> bool {
        forall |k| self.local_versions.contains_key(k) <==> self.combiner.contains_key(k)
    }

    #[invariant]
    pub fn combiner_replicas_domains(&self) -> bool {
        forall |k| #![auto] self.replicas.contains_key(k) <==> self.combiner.contains_key(k)
    }

    pub open spec fn wf_node_id(&self, node_id: NodeId) -> bool {
        &&& 0 <= node_id < self.num_replicas
        &&& self.combiner.contains_key(node_id)
        &&& self.local_versions.contains_key(node_id)
        &&& self.replicas.contains_key(node_id)
    }






    #[invariant]
    pub fn inv_version_in_range(&self) -> bool {
        self.version_upper_bound <= self.tail
    }


    #[invariant]
    pub fn inv_local_version_upper_bound_heads(&self) -> bool {
        forall |node_id| (#[trigger]  self.local_versions.contains_key(node_id))
            ==> self.local_versions[node_id] <= self.version_upper_bound
    }


    #[invariant]
    pub fn inv_readonly_requests_wf(&self) -> bool {
        forall |rid| (#[trigger] self.local_reads.contains_key(rid))
             ==> self.wf_readstate(self.local_reads[rid])
    }

    pub open spec fn wf_readstate(&self, rs: ReadonlyState<DT>) -> bool {
        match rs {
            ReadonlyState::Init{op} => {
                true
            }
            ReadonlyState::VersionUpperBound{op, version_upper_bound} => {
                version_upper_bound <= self.version_upper_bound
            }
            ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                &&& self.wf_node_id(node_id)
                &&& version_upper_bound <= self.version_upper_bound
                &&& version_upper_bound <= self.current_local_version(node_id)
            }
            ReadonlyState::Done{op, ret, node_id, version_upper_bound } => {
                &&& self.wf_node_id(node_id)
                &&& version_upper_bound <= self.version_upper_bound
                &&& version_upper_bound <= self.current_local_version(node_id)
            }
        }
    }


    #[invariant]
    pub open spec fn combiner_states_wf(&self) -> bool {
        forall |node_id| (#[trigger] self.combiner.contains_key(node_id))
             ==> self.wf_combiner_for_node_id(node_id)
    }

    pub open spec fn wf_combiner_for_node_id(&self, node_id: NodeId) -> bool
        recommends self.wf_node_id(node_id)
    {
        match self.combiner[node_id] {
            CombinerState::Ready => {
                &&& LogRangeNoNodeId(self.log, self.local_versions[node_id], self.tail, node_id)
            }
            CombinerState::Placed { queued_ops } => {
                &&& LogRangeMatchesQueue(queued_ops, self.log, 0, self.local_versions[node_id], self.tail, node_id, self.local_updates)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
                &&& seq_unique(queued_ops)
            }
            CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                &&& lversion == self.local_versions[node_id]
                &&& LogRangeMatchesQueue(queued_ops, self.log, 0, lversion, self.tail, node_id, self.local_updates)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
                &&& seq_unique(queued_ops)
            }
            CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                &&& tail <= self.tail
                &&& lversion >= self.local_versions[node_id]
                &&& lversion <= tail
                &&& LogContainsEntriesUpToHere(self.log, lversion)
                &&& 0 <= idx <= queued_ops.len()
                &&& LogRangeMatchesQueue(queued_ops, self.log, idx, lversion, tail, node_id, self.local_updates)
                &&& LogRangeNoNodeId(self.log, tail, self.tail, node_id)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, idx)
                &&& QueueRidsUpdateDone(queued_ops, self.local_updates, idx)
                &&& seq_unique(queued_ops)
            }
            CombinerState::UpdatedVersion{ queued_ops, tail } => {
                &&& tail <= self.version_upper_bound
                &&& self.local_versions[node_id] <= tail
                &&& LogContainsEntriesUpToHere(self.log, tail)
                &&& LogRangeNoNodeId(self.log, tail, self.tail, node_id)
                &&& QueueRidsUpdateDone(queued_ops, self.local_updates, queued_ops.len())
                &&& seq_unique(queued_ops)
            }
        }
    }


    #[invariant]
    pub fn inv_log_complete(&self) -> bool {
        &&& LogContainsEntriesUpToHere(self.log, self.tail)
        &&& LogNoEntriesFromHere(self.log, self.tail)
    }


    #[invariant]
    pub fn inv_local_updates(&self) -> bool {
        forall |rid| (#[trigger] self.local_updates.contains_key(rid))
            ==>  self.inv_local_updates_wf(self.local_updates[rid])
    }

    pub open spec fn inv_local_updates_wf(&self, update: UpdateState<DT>) -> bool {
        match update {
            UpdateState::Init { op } => { true },
            UpdateState::Placed { op: _, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.tail
            },
            UpdateState::Applied { ret, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.tail
            },
            UpdateState::Done { ret, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.version_upper_bound
            },
        }
    }


    #[invariant]
    pub fn inv_read_results(&self) -> bool {
        forall |rid| (#[trigger] self.local_reads.contains_key(rid))
             ==>  self.read_results_match(self.local_reads[rid])
    }

    pub open spec fn read_results_match(&self, read: ReadonlyState<DT>) -> bool {
        match read {
            ReadonlyState::Done { ret, version_upper_bound, op, .. } => {
                exists |v: nat| (#[trigger] rangeincl(version_upper_bound, v, self.version_upper_bound))
                    && ret == DT::dispatch_spec(compute_nrstate_at_version(self.log, v), op)
            },
            _ => true,
        }
    }


    #[invariant]
    pub fn inv_update_results(&self) -> bool {
        forall |rid| (#[trigger] self.local_updates.contains_key(rid))
            ==>  self.update_results_match(self.local_updates[rid])
    }

    pub open spec fn update_results_match(&self, update: UpdateState<DT>) -> bool {
        match update {
            UpdateState::Applied { ret, idx } => {
                ret == DT::dispatch_mut_spec(compute_nrstate_at_version(self.log, idx), self.log[idx].op).1
            },
            UpdateState::Done { ret, idx } => {
                ret == DT::dispatch_mut_spec(compute_nrstate_at_version(self.log, idx), self.log[idx].op).1
            },
            _ => true,
        }
    }


    #[invariant]
    pub fn inv_combiner_rids_distinct(&self) -> bool
    {
      forall |node_id1, node_id2|
          (#[trigger] self.combiner.contains_key(node_id1)
          && #[trigger] self.combiner.contains_key(node_id2)
          && node_id1 != node_id2) ==>
            seq_disjoint(self.combiner[node_id1].queued_ops(), self.combiner[node_id2].queued_ops())
    }


    #[invariant]
    pub open spec fn replica_state(&self) -> bool {
        forall |node_id| (#[trigger] self.replicas.contains_key(node_id)) ==>
            self.replicas[node_id] == compute_nrstate_at_version(self.log, self.current_local_version(node_id))
    }



    init!{
        initialize(number_of_nodes: nat) {
            require(number_of_nodes > 0);

            init num_replicas = number_of_nodes;
            init log = Map::empty();
            init tail = 0;
            init replicas = Map::new(Set::range(0, number_of_nodes), |n| DT::init_spec());
            init local_versions = Map::new(Set::range(0, number_of_nodes), |n| 0);
            init version_upper_bound = 0;
            init local_reads = Map::empty();
            init local_updates = Map::empty();
            init combiner = Map::new(Set::range(0, number_of_nodes), |n| CombinerState::Ready);
        }
    }


    transition!{
        readonly_version_upper_bound(rid: ReqId) {
            remove local_reads -= [ rid => let ReadonlyState::Init { op } ];
            add    local_reads += [ rid => ReadonlyState::VersionUpperBound {
                                                op, version_upper_bound: pre.version_upper_bound } ];
        }
    }

    transition!{
        readonly_ready_to_read(rid: ReqId, node_id: NodeId) {
            remove local_reads    -= [ rid => let ReadonlyState::VersionUpperBound { op, version_upper_bound } ];
            have   local_versions >= [ node_id => let local_head ];

            require(local_head >= version_upper_bound);

            add local_reads += [ rid => ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} ];
        }
    }

    transition!{
        readonly_apply(rid: ReqId) {
            remove local_reads -= [ rid => let ReadonlyState::ReadyToRead { op, node_id, version_upper_bound } ];
            have   combiner    >= [ node_id => CombinerState::Ready ];
            have   replicas    >= [ node_id => let state ];

            let ret = DT::dispatch_spec(state, op);

            add local_reads += [ rid => ReadonlyState::Done{ op, node_id, version_upper_bound, ret } ];
        }
    }


    transition!{
        update_place_ops_in_log_one(node_id: NodeId, rid: ReqId) {
            remove combiner      -= [ node_id => let CombinerState::Placed{ queued_ops } ];
            remove local_updates -= [ rid => let UpdateState::Init{ op }];

            update tail = pre.tail + 1;
            add log           += [ pre.tail => LogEntry{ op, node_id }];
            add local_updates += [ rid => UpdateState::Placed{ op, idx: pre.tail }];
            add combiner      += [ node_id => CombinerState::Placed { queued_ops: queued_ops.push(rid) } ];
        }
    }

    transition!{
        update_done(rid:ReqId) {
            remove local_updates -= [ rid => let UpdateState::Applied { ret, idx } ];

            require(pre.version_upper_bound > idx);

            add local_updates += [ rid => UpdateState::Done { ret, idx } ];
        }
    }





    transition!{
        exec_trivial_start(node_id: NodeId) {
            remove combiner -= [ node_id => CombinerState::Ready ];

            add    combiner += [ node_id => CombinerState::Placed { queued_ops: Seq::empty() } ];
        }
    }

    transition!{
        exec_load_local_version(node_id: NodeId) {
            remove combiner      -= [ node_id => let CombinerState::Placed { queued_ops } ];

            have   local_versions >= [node_id => let lversion];

            add    combiner      += [ node_id => CombinerState::LoadedLocalVersion { queued_ops, lversion }];
        }
    }

    transition!{
        exec_load_global_head(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::LoadedLocalVersion { queued_ops, lversion } ];

            add    combiner += [ node_id => CombinerState::Loop { queued_ops, lversion, idx: 0, tail: pre.tail } ];
        }
    }

    property!{
        pre_exec_dispatch_local(node_id: NodeId) {
            have combiner >= [ node_id => let CombinerState::Loop{ queued_ops, lversion, tail, idx } ];
            have log      >= [ lversion => let log_entry ];

            require(log_entry.node_id == node_id);
            require(lversion < tail);
            assert(idx < queued_ops.len()) by {
            };
            assert(queued_ops.len() > 0);
        }
    }

    transition!{
        exec_dispatch_local(node_id: NodeId) {
            remove combiner      -= [ node_id => let CombinerState::Loop { queued_ops, lversion, tail, idx } ];
            remove replicas      -= [ node_id => let old_nr_state ];
            let rid = queued_ops.index(idx as int);
            remove local_updates -= [ rid => let local_update ];

            have log >= [lversion => let log_entry];


            require(lversion < tail);
            require(log_entry.node_id == node_id);
            let (new_nr_state, ret) = DT::dispatch_mut_spec(old_nr_state, log_entry.op);

            add local_updates += [ rid => UpdateState::Applied { ret, idx: lversion }];
            add replicas      += [ node_id => new_nr_state];
            add combiner      += [ node_id => CombinerState::Loop { queued_ops, lversion: lversion + 1, tail, idx: idx + 1}];
        }
    }

    transition!{
        exec_dispatch_remote(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState:: Loop { queued_ops, lversion, tail, idx } ];
            remove replicas -= [ node_id => let old_nr_state ];

            have   log      >= [ lversion => let log_entry ];

            require(lversion < tail);
            require(log_entry.node_id != node_id);
            let (new_nr_state, ret) = DT::dispatch_mut_spec(old_nr_state, log_entry.op);

            add replicas    += [ node_id => new_nr_state ];
            add combiner    += [ node_id => CombinerState::Loop { queued_ops, lversion: lversion + 1, tail, idx}];
        }
    }

    property!{
        pre_exec_update_version_upper_bound(node_id: NodeId) {
            have combiner >= [ node_id => let CombinerState::Loop{ queued_ops, lversion, tail, idx } ];

            require(lversion == tail);
            assert(idx == queued_ops.len()) by {
            };
        }
    }

    transition!{
        exec_update_version_upper_bound(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Loop { queued_ops, lversion, tail, idx, }];

            require(lversion == tail);


            update version_upper_bound = if pre.version_upper_bound >= tail {
                pre.version_upper_bound
            } else {
                tail
            };
            add combiner += [ node_id => CombinerState::UpdatedVersion { queued_ops, tail } ];
        }
    }

    transition!{
        exec_finish(node_id: NodeId) {
            remove combiner       -= [ node_id => let CombinerState::UpdatedVersion { queued_ops, tail } ];
            remove local_versions -= [ node_id => let old_local_head ];


            add    local_versions += [ node_id => tail ];
            add    combiner       += [ node_id => CombinerState::Ready ];
        }
    }

    transition!{
        exec_finish_no_change(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::LoadedLocalVersion { queued_ops, lversion } ];

            require(lversion == pre.tail);
            assert(queued_ops.len() == 0);

            add    combiner += [ node_id => CombinerState::Ready];
        }
    }




    #[inductive(initialize)]
    fn initialize_inductive(post: Self, number_of_nodes: nat) {

        let max_dom = (post.num_replicas - 1) as nat;
        let cmap = map_new_rec(max_dom, CombinerState::Ready);
        assert(cmap.dom().finite()) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(forall |n: nat| 0 <= n < post.num_replicas <==> post.combiner.contains_key(n));
        assert(forall |n: nat| 0 <= n <= max_dom <==> cmap.contains_key(n)) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(forall |n: nat| 0 <= n <= max_dom <==> cmap.contains_key(n));
        assert(forall |n: nat| 0 <= n < post.num_replicas <==> cmap.contains_key(n));

        assert(forall |n: nat| post.combiner.contains_key(n) <==> #[trigger]cmap.contains_key(n));
        assert(post.combiner.dom() =~= cmap.dom());
        assert(forall |n| #[trigger]post.combiner.contains_key(n) ==> post.combiner[n] == CombinerState::Ready);

        assert(forall |n| #[trigger]cmap.contains_key(n) ==> cmap[n] == CombinerState::Ready) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(post.combiner =~= cmap);
    }


    #[inductive(readonly_version_upper_bound)]
    fn readonly_version_upper_bound_inductive(pre: Self, post: Self, rid: ReqId) { admit(); }

    #[inductive(readonly_ready_to_read)]
    fn readonly_ready_to_read_inductive(pre: Self, post: Self, rid: ReqId, node_id: NodeId) { admit(); }

    #[inductive(readonly_apply)]
    fn readonly_apply_inductive(pre: Self, post: Self, rid: ReqId) { admit(); }

    pub proof fn add_ticket_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: InputOperation<DT>,
        rid: ReqId,
    )
        requires pre.invariant(),
            add_ticket(pre, post, input, rid),
            rid == get_fresh_nat(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner)
        ensures post.invariant(),
    {
        get_fresh_nat_not_in(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner);
        match input {
            InputOperation::Read(op) => {
                assert(post.inv_readonly_requests_wf());
            }
            InputOperation::Write(op) => {
                assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
                    assert(post.combiner[node_id] == pre.combiner[node_id]);
                    match post.combiner[node_id] {
                        CombinerState::Placed { queued_ops } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                            assert(post.wf_combiner_for_node_id(node_id));
                        }
                        CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                            assert(post.wf_combiner_for_node_id(node_id));
                        }
                        CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                        }
                        _ => {
                        }
                    }
                }
            }
        }
    }

    #[inductive(update_done)]
    fn update_done_inductive(pre: Self, post: Self, rid: ReqId) { admit(); }

    pub proof fn consume_stub_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: OutputOperation<DT>,
        rid: ReqId,
    )
        requires pre.invariant(),
            consume_stub(pre, post, output, rid),
        ensures post.invariant(),
    {
        match output {
            OutputOperation::Read(op) => {
                assert(post.inv_readonly_requests_wf());
            }
            OutputOperation::Write(op) => {
                assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
                    match post.combiner[node_id] {
                        CombinerState::Placed { queued_ops } => {
                            LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                        }
                        CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                            LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                        }
                        CombinerState::Loop { queued_ops, idx, lversion, tail } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    #[inductive(exec_trivial_start)]
    fn exec_trivial_start_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(update_place_ops_in_log_one)]
    fn update_place_ops_in_log_one_inductive(pre: Self, post: Self, node_id: NodeId, rid: ReqId) { admit(); }


    #[inductive(exec_load_local_version)]
    fn exec_load_local_version_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(exec_load_global_head)]
    fn exec_load_global_head_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(exec_dispatch_local)]
    fn exec_dispatch_local_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(exec_dispatch_remote)]
    fn exec_dispatch_remote_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(exec_update_version_upper_bound)]
    fn exec_update_version_upper_bound_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert(pre.version_upper_bound <= post.version_upper_bound);
        assert(post.local_reads =~= pre.local_reads);
        assert(post.log =~= pre.log);
        assert(post.inv_read_results()) by {
            assert forall |rid| #[trigger] post.local_reads.contains_key(rid)
                implies post.read_results_match(post.local_reads[rid]) by {
                assert(pre.local_reads.contains_key(rid));
                assert(pre.read_results_match(post.local_reads[rid]));
                match post.local_reads[rid] {
                    ReadonlyState::Done { op, ret, version_upper_bound, .. } => {
                        assert(exists |v: nat| #[trigger] rangeincl(version_upper_bound, v, pre.version_upper_bound)
                            && ret == DT::dispatch_spec(compute_nrstate_at_version(pre.log, v), op));
                        assert(exists |v: nat| #[trigger] rangeincl(version_upper_bound, v, post.version_upper_bound)
                            && ret == DT::dispatch_spec(compute_nrstate_at_version(post.log, v), op)) by {
                            let v = choose |v: nat| rangeincl(version_upper_bound, v, pre.version_upper_bound)
                                && ret == DT::dispatch_spec(compute_nrstate_at_version(pre.log, v), op);
                            assert(rangeincl(version_upper_bound, v, post.version_upper_bound));
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    #[inductive(exec_finish)]
    fn exec_finish_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }

    #[inductive(exec_finish_no_change)]
    fn exec_finish_no_change_inductive(pre: Self, post: Self, node_id: NodeId) { admit(); }


    pub open spec fn current_local_version(&self, node_id: NodeId) -> nat
        recommends self.combiner.contains_key(node_id) && self.local_versions.contains_key(node_id)
    {
        match self.combiner[node_id] {
            CombinerState::Ready                              => self.local_versions[node_id],
            CombinerState::Placed{ .. }                       => self.local_versions[node_id],
            CombinerState::LoadedLocalVersion{ lversion, .. } => lversion,
            CombinerState::Loop { lversion, .. }              => lversion,
            CombinerState::UpdatedVersion { tail, .. }        => tail,
        }
    }

}

} 

verus! {

pub open spec fn combiner_request_ids(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    decreases combiners.dom().len(),
    when (combiners.dom().finite() && combiners.dom().len() >= 0)
    via combiner_request_ids_decreases
{
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
            Set::empty()
        } else {
            let node_id = combiners.dom().choose();
            let req_ids = combiner_request_ids(combiners.remove(node_id));
            req_ids + seq_to_set(combiners[node_id].queued_ops())
        }
    } else {
        arbitrary()
    }
}

#[via_fn]
proof fn combiner_request_ids_decreases(combiners: Map<NodeId, CombinerState>) {
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
        } else {
            let node_id = combiners.dom().choose();
            assert(combiners.remove(node_id).dom().len() < combiners.dom().len());  
        }
    } else {
    }
}

pub proof fn combiner_request_ids_proof(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    requires
        combiners.dom().finite(),
    decreases combiners.dom().len(),
{
    if combiners.dom().len() == 0 {
        Set::empty()
    } else {
        let node_id = combiners.dom().choose();
        let s1 = combiner_request_ids_proof(combiners.remove(node_id));
        s1 + seq_to_set(
            combiners[node_id].queued_ops(),
        )

    }
}

pub open spec fn combiner_request_id_fresh(
    combiners: Map<NodeId, CombinerState>,
    rid: ReqId,
) -> bool {
    forall|n| (#[trigger] combiners.contains_key(n)) ==> !combiners[n].queued_ops().contains(rid)
}

pub proof fn combiner_request_ids_not_contains(combiners: Map<NodeId, CombinerState>, rid: ReqId)
    requires
        combiners.dom().finite(),
    ensures
        combiner_request_id_fresh(combiners, rid) <==> !combiner_request_ids(combiners).contains(
            rid,
        ),
    decreases combiners.dom().len(),
{
    if !(combiners.dom() =~= Set::empty()) {
        let node_id = combiners.dom().choose();
        combiner_request_ids_not_contains(combiners.remove(node_id), rid);
        assert(combiner_request_id_fresh(combiners.remove(node_id), rid) <==> !combiner_request_ids(
            combiners.remove(node_id),
        ).contains(rid));
        if !combiners[node_id].queued_ops().contains(rid) {
            if combiner_request_id_fresh(combiners.remove(node_id), rid) {
                assert forall|n|
                    (#[trigger] combiners.contains_key(
                        n,
                    )) implies !combiners[n].queued_ops().contains(rid) by {
                    if n != node_id {
                        assert(combiners.remove(node_id).contains_key(n));
                    }
                }
            }
        }
    }
}

pub proof fn combiner_request_ids_finite(combiners: Map<NodeId, CombinerState>)
    requires
        combiners.dom().finite(),
    ensures
        combiner_request_ids(combiners).finite(),
    decreases combiners.dom().len(),
{
    if combiners.dom().len() == 0 {
        assert(combiner_request_ids(combiners).finite())
    } else {
        let node_id = combiners.dom().choose();
        assert(combiner_request_ids(combiners.remove(node_id)).finite()) by {
            combiner_request_ids_finite(combiners.remove(node_id));
        }
    }
}

pub closed spec fn get_fresh_nat(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>) -> nat
    recommends
        reqs.finite() && combiner.dom().finite(),
{
    choose|n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n)
}

proof fn max_of_set(s: Set<nat>) -> (r: nat)
    requires
        s.finite(),
    ensures
        forall|x: nat| #[trigger] s.contains(x) ==> x <= r,
    decreases s.len(),
{
    if s.is_empty() {
        0
    } else {
        let v1 = s.choose();
        let v2 = max_of_set(s.remove(v1));
        assert(forall|x: nat| #[trigger] s.contains(x) && x != v1 ==> s.remove(v1).contains(x));
        if v1 >= v2 {
            v1
        } else {
            v2
        }
    }
}

proof fn element_outside_set(s: Set<nat>) -> (r: nat)
    requires
        s.finite(),
    ensures
        !s.contains(r),
{
    max_of_set(s) + 1
}

pub proof fn get_fresh_nat_not_in(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>)
    requires
        reqs.finite(),
        combiner.dom().finite(),
    ensures
        !reqs.contains(get_fresh_nat(reqs, combiner)),
        combiner_request_id_fresh(combiner, get_fresh_nat(reqs, combiner)),
{
    let rid = get_fresh_nat(reqs, combiner);
    let combiner_req_ids = combiner_request_ids(combiner);
    assert(!combiner_req_ids.contains(rid) == combiner_request_id_fresh(combiner, rid)) by {
        combiner_request_ids_not_contains(combiner, rid);
    }
    assert(combiner_req_ids.finite()) by {
        combiner_request_ids_finite(combiner);
    }
    let req_ids = reqs + combiner_req_ids;
    assert(req_ids.finite());
    let r = element_outside_set(req_ids);
    assert(!reqs.contains(r));
    assert(!combiner_req_ids.contains(r));
    assert(combiner_request_id_fresh(combiner, r)) by {
        combiner_request_ids_not_contains(combiner, r);
    }
    assert(exists|n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n));
}

pub open spec fn LogContainsEntriesUpToHere<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    end: LogIdx,
) -> bool {
    forall|i: nat| 0 <= i < end ==> log.contains_key(i)
}

pub open spec fn LogNoEntriesFromHere<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    start: LogIdx,
) -> bool {
    forall|i: nat| start <= i ==> !log.contains_key(i)
}

pub open spec fn LogRangeNoNodeId<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    start: LogIdx,
    end: LogIdx,
    node_id: NodeId,
) -> bool {
    decreases_when(start <= end);
    decreases(end - start);
    (start < end ==> {
        &&& log.contains_key(start)
        &&& log.index(start).node_id != node_id
        &&& LogRangeNoNodeId(log, start + 1, end, node_id)
    })
}

pub open spec fn LogRangeMatchesQueue<DT: Dispatch>(
    queue: Seq<ReqId>,
    log: Map<LogIdx, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: LogIdx,
    logIndexUpper: LogIdx,
    nodeId: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
) -> bool {
    recommends([0 <= queueIndex <= queue.len(), LogContainsEntriesUpToHere(log, logIndexUpper)]);
    decreases_when(logIndexLower <= logIndexUpper);
    decreases(logIndexUpper - logIndexLower);
    &&& (logIndexLower == logIndexUpper ==> queueIndex
        == queue.len())

    &&& (logIndexLower < logIndexUpper ==> {
        &&& log.contains_key(
            logIndexLower,
        )

        &&& (log.index(logIndexLower).node_id == nodeId ==> {
            &&& queueIndex < queue.len()
            &&& updates.contains_key(queue.index(queueIndex as int))
            &&& updates.index(queue.index(queueIndex as int)).is_Placed()
            &&& updates.index(queue.index(queueIndex as int)).get_Placed_idx() == logIndexLower
            &&& LogRangeMatchesQueue(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates,
            )
        })

        &&& (log.index(logIndexLower).node_id != nodeId ==> LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower + 1,
            logIndexUpper,
            nodeId,
            updates,
        ))
    })
}

proof fn LogRangeMatchesQueue_update_change<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    nodeId: nat,
    updates1: Map<ReqId, UpdateState<DT>>,
    updates2: Map<ReqId, UpdateState<DT>>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates1,
        ),
        forall|rid| #[trigger]
            updates1.contains_key(rid) ==> updates1[rid].is_Placed() && logIndexLower
                <= updates1[rid].get_Placed_idx() < logIndexUpper ==> updates2.contains_key(rid)
                && updates2[rid] === updates1[rid],
    ensures
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates2,
        ),
    decreases logIndexUpper - logIndexLower,
{
    if logIndexLower == logIndexUpper {
    } else {
        if log.index(logIndexLower).node_id == nodeId {
            LogRangeMatchesQueue_update_change(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        } else {
            LogRangeMatchesQueue_update_change(
                queue,
                log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_update_change_2<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    nodeId: nat,
    updates1: Map<ReqId, UpdateState<DT>>,
    updates2: Map<ReqId, UpdateState<DT>>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates1,
        ),
        forall|rid| #[trigger]
            updates1.contains_key(rid) ==> queue.contains(rid) ==> updates2.contains_key(rid)
                && updates2[rid] === updates1[rid],
    ensures
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates2,
        ),
    decreases logIndexUpper - logIndexLower,
{
    if logIndexLower == logIndexUpper {
    } else {
        if log.index(logIndexLower).node_id == nodeId {
            LogRangeMatchesQueue_update_change_2(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        } else {
            LogRangeMatchesQueue_update_change_2(
                queue,
                log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_append<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
    new_updates: Map<ReqId, UpdateState<DT>>,
    new_rid: ReqId,
    log_entry: LogEntry<DT>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id == node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed {
            op: log_entry.op,
            idx: logIndexUpper,
        }),
        !queue.contains(new_rid),
        forall|rid| #[trigger]
            updates.contains_key(rid) && rid != new_rid ==> new_updates.contains_key(rid)
                && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            updates,
        ),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeMatchesQueue(
            queue.push(new_rid),
            new_log,
            queueIndex,
            logIndexLower,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            assert(LogRangeMatchesQueue(
                queue.push(new_rid),
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        }
        if new_log.index(logIndexLower).node_id != node_id {
            assert(LogRangeMatchesQueue(
                queue.push(new_rid),
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        }
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeMatchesQueue_append(
                queue,
                log,
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
            assert(LogRangeMatchesQueue(
                queue.push(new_rid),
                new_log,
                queueIndex,
                logIndexLower,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        } else {
            LogRangeMatchesQueue_append(
                queue,
                log,
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_append_other<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    logLen: nat,
    node_id: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
    new_updates: Map<ReqId, UpdateState<DT>>,
    new_rid: ReqId,
    log_entry: LogEntry<DT>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper <= logLen,
        log_entry.node_id != node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed { op: log_entry.op, idx: logLen }),
        !queue.contains(new_rid),
        forall|rid| #[trigger]
            updates.contains_key(rid) && rid != new_rid ==> new_updates.contains_key(rid)
                && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            updates,
        ),
        new_log === log.insert(logLen, log_entry),
    ensures
        LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            new_updates,
        ),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower != logIndexUpper {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeMatchesQueue_append_other(
                queue,
                log,
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                logLen,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        } else {
            LogRangeMatchesQueue_append_other(
                queue,
                log,
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                logLen,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_append_other_augment<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
    new_updates: Map<ReqId, UpdateState<DT>>,
    new_rid: ReqId,
    log_entry: LogEntry<DT>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed {
            op: log_entry.op,
            idx: logIndexUpper,
        }),
        !queue.contains(new_rid),
        forall|rid| #[trigger]
            updates.contains_key(rid) && rid != new_rid ==> new_updates.contains_key(rid)
                && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            updates,
        ),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        assert(new_log.index(logIndexLower).node_id != node_id);
        assert(LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower + 1,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ));
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeMatchesQueue_append_other_augment(
                queue,
                log,
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
            assert(LogRangeMatchesQueue(
                queue,
                new_log,
                queueIndex,
                logIndexLower,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        } else {
            LogRangeMatchesQueue_append_other_augment(
                queue,
                log,
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        }
    }
}

proof fn LogRangeNoNodeId_append_other<DT: Dispatch>(
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    log_entry: LogEntry<DT>,
)
    requires
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        LogRangeNoNodeId(log, logIndexLower, logIndexUpper, node_id),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        assert(new_log[logIndexLower].node_id != node_id);
        assert(LogRangeNoNodeId(new_log, logIndexLower + 1, logIndexUpper + 1, node_id));
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeNoNodeId_append_other(
                log,
                new_log,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                log_entry,
            );
            assert(LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id));
        } else {
            LogRangeNoNodeId_append_other(
                log,
                new_log,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                log_entry,
            );
        }
    }
}

pub open spec fn QueueRidsUpdateDone<DT: Dispatch>(
    queued_ops: Seq<ReqId>,
    localUpdates: Map<ReqId, UpdateState<DT>>,
    bound: nat,
) -> bool
    recommends
        0 <= bound <= queued_ops.len(),
{
    forall|j|
        0 <= j < bound ==> localUpdates.contains_key(#[trigger] queued_ops[j]) ==> {
            ||| localUpdates[queued_ops[j]].is_Applied()
            ||| localUpdates[queued_ops[j]].is_Done()
        }
}

pub open spec fn QueueRidsUpdatePlaced<DT: Dispatch>(
    queued_ops: Seq<ReqId>,
    localUpdates: Map<ReqId, UpdateState<DT>>,
    bound: nat,
) -> bool
    recommends
        0 <= bound <= queued_ops.len(),
{
    forall|j|
        bound <= j < queued_ops.len() ==> {
            &&& localUpdates.contains_key(#[trigger] queued_ops[j])
            &&& localUpdates[queued_ops[j]].is_Placed()
        }
}

proof fn concat_LogRangeNoNodeId_LogRangeMatchesQueue<DT: Dispatch>(
    queue: Seq<ReqId>,
    log: Map<LogIdx, LogEntry<DT>>,
    queueIndex: nat,
    a: nat,
    b: nat,
    c: nat,
    nodeId: nat,
    updates: Map<ReqId, UpdateState<DT>>,
)
    requires
        a <= b <= c,
        0 <= queueIndex <= queue.len(),
        LogRangeNoNodeId(log, a, b, nodeId),
        LogRangeMatchesQueue(queue, log, queueIndex, b, c, nodeId, updates),
    ensures
        LogRangeMatchesQueue(queue, log, queueIndex, a, c, nodeId, updates),
    decreases b - a,
{
    if a != b {
        concat_LogRangeNoNodeId_LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            a + 1,
            b,
            c,
            nodeId,
            updates,
        );
    }
}

pub open spec fn compute_nrstate_at_version<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    version: LogIdx,
) -> DT::View
    recommends
        forall|i| 0 <= i < version ==> log.contains_key(i),
    decreases version,
{
    if version == 0 {
        DT::init_spec()
    } else {
        let ver = (version - 1) as nat;
        DT::dispatch_mut_spec(compute_nrstate_at_version(log, ver), log[ver].op).0
    }
}

pub proof fn compute_nrstate_at_version_preserves<DT: Dispatch>(
    a: Map<LogIdx, LogEntry<DT>>,
    b: Map<LogIdx, LogEntry<DT>>,
    version: LogIdx,
)
    requires
        forall|i| 0 <= i < version ==> a.contains_key(i),
        forall|i| 0 <= i < version ==> a[i] == b[i],
    ensures
        compute_nrstate_at_version(a, version) == compute_nrstate_at_version(b, version),
    decreases version,
{
    if version > 0 {
        compute_nrstate_at_version_preserves(a, b, (version - 1) as nat);
    }
}

} 
