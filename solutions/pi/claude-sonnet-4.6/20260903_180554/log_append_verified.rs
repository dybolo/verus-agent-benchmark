#[allow(unused_imports)]
use verus_builtin::*;
use verus_state_machines_macros::state_machine;
use vstd::prelude::*;

pub mod constants {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

pub open const MAX_REPLICAS_PER_LOG: usize = 16;

#[verus::trusted]
pub open const MAX_REPLICAS: usize = 16;

pub open const DEFAULT_LOG_BYTES: usize = 2 * 1024 * 1024;

pub open const LOG_SIZE: usize = 512 * 1024;

pub open const MAX_THREADS_PER_REPLICA: usize = 128;

pub open const MAX_PENDING_OPS: usize = 1;

pub open const MAX_REQUESTS: usize = MAX_THREADS_PER_REPLICA * MAX_PENDING_OPS;

pub open const RESPONSE_CHECK_INTERVAL: usize = 0x2000_0000;

pub open const GC_FROM_HEAD: usize = MAX_PENDING_OPS * MAX_THREADS_PER_REPLICA;

pub open const WARN_THRESHOLD: usize = 0x10000000;

pub open const MAX_IDX: u64 = 0xffff_ffff_f000_0000;

} 
}
mod exec {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::prelude::*;

use crate::Dispatch;

use crate::spec::{cyclicbuffer::CyclicBuffer, unbounded_log::UnboundedLog};

use crate::exec::context::ThreadToken;
use crate::exec::log::{NrLog, NrLogTokens};
use crate::exec::replica::{Replica, ReplicaConfig, ReplicaId};

use crate::constants::{LOG_SIZE, MAX_REPLICAS, MAX_THREADS_PER_REPLICA};
use crate::AffinityFn;

pub mod context {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::{
    atomic_ghost::AtomicU64,
    atomic_with_ghost,
    cell::{CellId, PCell, PointsTo},
    prelude::*,
};

use crate::Dispatch;

use crate::constants::MAX_THREADS_PER_REPLICA;

use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::unbounded_log::UnboundedLog;

use crate::exec::replica::{ReplicaId, ReplicaToken};
use crate::exec::CachePadded;
use crate::exec::Replica;

verus! {

pub type ThreadId = u32;

pub struct ThreadToken<DT: Dispatch> {
    pub                       
     rid: ReplicaToken,
    pub                       
     tid: ThreadId,
    pub fc_client: Tracked<FlatCombiner::clients>,
    pub batch_perm: Tracked<PointsTo<PendingOperation<DT>>>,
}

impl<DT: Dispatch> ThreadToken<DT> {
    pub open spec fn wf2(&self, num_replicas: nat) -> bool {
        &&& self.rid.wf(num_replicas)
        &&& self.fc_client@.value().is_Idle()
        &&& (self.tid as nat)
            < MAX_THREADS_PER_REPLICA

        &&& self.batch_perm@.mem_contents().is_uninit()
        &&& self.fc_client@.key() == self.tid as nat
    }

    pub open spec fn wf(&self, replica: &Replica<DT>) -> bool {
        &&& self.wf2(replica.spec_id() + 1)  

        &&& self.rid@ == replica.spec_id()
        &&& self.fc_client@.instance_id() == replica.flat_combiner_instance@.id()
        &&& self.batch_perm@@.pcell == replica.contexts[self.thread_id_spec() as int].batch.0.id()
    }

    pub fn thread_id(&self) -> (result: ThreadId)
        ensures
            result as nat == self.thread_id_spec(),
    {
        self.tid
    }

    pub open spec fn thread_id_spec(&self) -> nat {
        self.tid as nat
    }

    pub const fn replica_id(&self) -> (result: ReplicaId)
        ensures
            result as nat == self.replica_id_spec(),
    {
        self.rid.id()
    }

    pub open spec fn replica_token(&self) -> ReplicaToken {
        self.rid
    }

    pub open spec fn replica_id_spec(&self) -> nat {
        self.rid.id_spec()
    }
}

pub struct PendingOperation<DT: Dispatch> {
    pub                     
     op: DT::WriteOperation,
    pub                     
     resp: Option<DT::Response>,
}

impl<DT: Dispatch> PendingOperation<DT> {
    pub fn new(op: DT::WriteOperation) -> (res: Self)
        ensures
            res.op == op,
    {
        PendingOperation { op, resp: None }
    }

    pub fn set_result(&mut self, resp: DT::Response) {
        self.resp = Some(resp);
    }

}

struct_with_invariants!{
#[repr(align(128))]
pub struct Context<DT: Dispatch> {
    pub                    batch: CachePadded<PCell<PendingOperation<DT>>>,

    pub                    atomic: CachePadded<AtomicU64<_, ContextGhost<DT>, _>>,

    pub thread_id_g: Ghost<nat>,

    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
}

pub open spec fn wf(&self, thread_idx: nat) -> bool {
    predicate {
        self.thread_id_g@ == thread_idx
    }
    invariant on atomic with (flat_combiner_instance, unbounded_log_instance, batch, thread_id_g) specifically (self.atomic.0) is (v: u64, g: ContextGhost<DT>) {
        &&& g.inv(v, thread_id_g@, batch.0, flat_combiner_instance@, unbounded_log_instance@)
    }
}}  


impl<DT: Dispatch> Context<DT> {
    pub fn new(
        thread_id: usize,
        slot: Tracked<FlatCombiner::slots>,
        flat_combiner_instance: Tracked<FlatCombiner::Instance>,
        unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    ) -> (res: (Context<DT>, Tracked<PointsTo<PendingOperation<DT>>>))
        requires
            slot@.value().is_Empty(),
            slot@.instance_id() == flat_combiner_instance@.id(),
            slot@.key() == thread_id as nat,
        ensures
            res.0.wf(thread_id as nat),
            res.0.batch.0.id() == res.1@@.pcell,
            res.0.flat_combiner_instance == flat_combiner_instance,
            res.0.unbounded_log_instance == unbounded_log_instance,
            res.1@.mem_contents().is_uninit(),
    {
        let ghost mut thread_id_g;
        proof {
            thread_id_g = thread_id as nat;
        }
        let (batch, batch_perms) = PCell::empty();
        let batch = CachePadded(batch);
        let tracked context_ghost = ContextGhost {
            batch_perms: None,
            slots: slot.get(),
            update: Option::None,
        };
        let atomic = CachePadded(
            AtomicU64::new(
                Ghost((flat_combiner_instance, unbounded_log_instance, batch, Ghost(thread_id_g))),
                0,
                Tracked(context_ghost),
            ),
        );
        (
            Context {
                batch,
                atomic,
                thread_id_g: Ghost(thread_id_g),
                flat_combiner_instance,
                unbounded_log_instance,
            },
            batch_perms,
        )
    }

    pub fn enqueue_op(
        &self,
        op: DT::WriteOperation,
        context_ghost: Tracked<FCClientRequestResponseGhost<DT>>,
    ) -> (res: (bool, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            context_ghost@.enqueue_op_pre(
                self.thread_id_g@,
                op,
                self.batch.0.id(),
                self.flat_combiner_instance@,
                self.unbounded_log_instance@,
            ),
            self.wf(self.thread_id_g@),
        ensures
            res.1@.enqueue_op_post(context_ghost@),
            res.1@.cell_id == self.batch.0.id(),
            self.wf(self.thread_id_g@),
    {
        let tracked FCClientRequestResponseGhost {
            batch_perms: batch_perms,
            cell_id,
            local_updates: local_updates,
            fc_clients: mut fc_clients,
        } = context_ghost.get();
        let tracked mut batch_perms = batch_perms.tracked_unwrap();
        let tracked local_updates = local_updates.tracked_unwrap();
        self.batch.0.put(Tracked(&mut batch_perms), PendingOperation::new(op));
        let tracked send_request_result;
        let res =
            atomic_with_ghost!(
            &self.atomic.0 => store(1);
            update prev->next;
            ghost g => {
                let ghost tid = fc_clients.key();
                let ghost rid = local_updates.key();

                self.flat_combiner_instance.borrow().pre_send_request(tid, &fc_clients, &g.slots);
                send_request_result = self.flat_combiner_instance.borrow().send_request(tid, rid, fc_clients, g.slots);
                fc_clients = send_request_result.0.get();

                g.slots = send_request_result.1.get();
                g.batch_perms = Some(batch_perms);
                g.update = Some(local_updates);

                assert(g.inv(1, tid, self.batch.0, self.flat_combiner_instance.view(), self.unbounded_log_instance.view()))
            }
        );
        let tracked new_context_ghost = FCClientRequestResponseGhost {
            batch_perms: None,
            cell_id,
            local_updates: None,
            fc_clients,
        };
        (true, Tracked(new_context_ghost))
    }

    pub fn dequeue_response(
        &self,
        context_ghost: Tracked<FCClientRequestResponseGhost<DT>>,
    ) -> (res: (Option<DT::Response>, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            context_ghost@.dequeue_resp_pre(
                self.batch.0.id(),
                self.thread_id_g@,
                self.flat_combiner_instance@,
            ),
            self.wf(self.thread_id_g@),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, res.0, self.unbounded_log_instance@),
            self.wf(self.thread_id_g@),
    {
        let tracked FCClientRequestResponseGhost {
            batch_perms: mut batch_perms,
            cell_id,
            local_updates: mut local_updates,
            fc_clients: mut fc_clients,
        } = context_ghost.get();
        let tracked recv_response_result;
        let res =
            atomic_with_ghost!(
            &self.atomic.0 => load();
            returning res;
            ghost g => {
                if res == 0 {
                    batch_perms = g.batch_perms;
                    local_updates = g.update;

                    let tid = fc_clients.key();
                    let rid = fc_clients.value().get_Waiting_0();
                    self.flat_combiner_instance.borrow().pre_recv_response(tid, &fc_clients, &g.slots);
                    recv_response_result = self.flat_combiner_instance.borrow().recv_response(tid, rid, fc_clients, g.slots);
                    fc_clients = recv_response_result.0.get();

                    g.slots = recv_response_result.1.get();
                    g.batch_perms = None;
                    g.update = None;
                }
            }
        );
        if res == 0 {
            let tracked mut batch_perms = batch_perms.tracked_unwrap();
            let op = self.batch.0.take(Tracked(&mut batch_perms));
            let resp = op.resp.unwrap();
            let tracked new_context_ghost = FCClientRequestResponseGhost {
                batch_perms: Some(batch_perms),
                cell_id,
                local_updates,
                fc_clients,
            };
            (Some(resp), Tracked(new_context_ghost))
        } else {
            let tracked new_context_ghost = FCClientRequestResponseGhost {
                batch_perms,
                cell_id,
                local_updates,
                fc_clients,
            };
            (None, Tracked(new_context_ghost))
        }
    }

    #[inline(always)]
    pub(crate) fn batch_size() -> usize {
        1
    }  

}

struct_with_invariants!{
pub tracked struct ContextGhost<DT: Dispatch> {
    pub batch_perms: Option<PointsTo<PendingOperation<DT>>>,

    pub slots: FlatCombiner::slots,

    pub update: Option<UnboundedLog::local_updates<DT>>
}

pub open spec fn inv(&self, v: u64, tid: nat, cell: PCell<PendingOperation<DT>>, fc: FlatCombiner::Instance, inst: UnboundedLog::Instance<DT>) -> bool {
    predicate {
        &&& self.slots.key() == tid
        &&& self.slots.instance_id() == fc.id()

        &&& ((v == 0) || (v == 1))
        &&& (v == 0 ==> self.slots.value().is_Empty() || self.slots.value().is_Response())
        &&& (v == 1 ==> self.slots.value().is_Request() || self.slots.value().is_InProgress())

        &&& (self.slots.value().is_Empty() ==> {
            &&& self.update.is_none()
            &&& self.batch_perms.is_none()
        })

        &&& (self.slots.value().is_Request() ==> {
            &&& self.update matches Some(update)
            &&& update.value().is_Init()
            &&& update.key() == self.slots.value().get_ReqId()
            &&& update.instance_id() == inst.id()

            &&& self.batch_perms matches Some(batch_perms)
            &&& batch_perms.mem_contents().is_init()
            &&& batch_perms@.pcell == cell.id()
            &&& batch_perms.mem_contents().value().op == update.value().get_Init_op()
        })

        &&& (self.slots.value().is_InProgress() ==> {
            &&& self.update.is_none()
            &&& self.batch_perms.is_none()
        })

        &&& (self.slots.value().is_Response() ==> {
            &&& self.update matches Some(update)
            &&& update.value().is_Done()
            &&& update.key() == self.slots.value().get_ReqId()
            &&& update.instance_id() == inst.id()

            &&& self.batch_perms matches Some(batch_perms)
            &&& batch_perms.mem_contents().is_init()
            &&& batch_perms@.pcell == cell.id()
            &&& batch_perms.mem_contents().value().resp matches Some(resp)
            &&& resp == update.value().get_Done_ret()
        })
    }
}
}  


pub tracked struct FCClientRequestResponseGhost<DT: Dispatch> {
    pub tracked batch_perms: Option<PointsTo<PendingOperation<DT>>>,
    pub tracked cell_id: Ghost<CellId>,
    pub tracked local_updates: Option<UnboundedLog::local_updates<DT>>,
    pub tracked fc_clients: FlatCombiner::clients,
}

impl<DT: Dispatch> FCClientRequestResponseGhost<DT> {
    pub open spec fn enqueue_op_pre(
        &self,
        tid: nat,
        op: DT::WriteOperation,
        batch_cell: CellId,
        fc_inst: FlatCombiner::Instance,
        inst: UnboundedLog::Instance<DT>,
    ) -> bool {
        &&& self.local_updates matches Some(local_updates)
        &&& local_updates.instance_id() == inst.id()
        &&& local_updates.value().is_Init()
        &&& local_updates.value().get_Init_op() == op
        &&& self.batch_perms matches Some(batch_perms)
        &&& batch_perms@.pcell == self.cell_id
        &&& self.cell_id == batch_cell
        &&& batch_perms.mem_contents().is_uninit()
        &&& self.fc_clients.instance_id() == fc_inst.id()
        &&& self.fc_clients.key() == tid
        &&& self.fc_clients.value().is_Idle()
    }

    pub open spec fn enqueue_op_post(&self, pre: FCClientRequestResponseGhost<DT>) -> bool
        recommends
            pre.local_updates.is_some(),
    {
        &&& self.fc_clients.value().is_Waiting()
        &&& self.fc_clients.value().get_Waiting_0() == pre.local_updates.unwrap().key()
        &&& self.fc_clients.instance_id() == pre.fc_clients.instance_id()
        &&& self.fc_clients.key() == pre.fc_clients.key()
        &&& self.cell_id == pre.cell_id
        &&& self.batch_perms.is_none()
        &&& self.local_updates.is_none()
    }

    pub open spec fn dequeue_resp_pre(
        &self,
        batch_cell: CellId,
        tid: nat,
        fc_inst: FlatCombiner::Instance,
    ) -> bool {
        &&& self.fc_clients.key() == tid
        &&& self.fc_clients.instance_id() == fc_inst.id()
        &&& self.fc_clients.value().is_Waiting()
        &&& self.batch_perms.is_none()
        &&& self.local_updates.is_none()
        &&& self.cell_id == batch_cell
    }

    pub open spec fn dequeue_resp_post(
        &self,
        pre: FCClientRequestResponseGhost<DT>,
        ret: Option<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
    ) -> bool {
        &&& ret matches Some(ret) ==> {
            &&& self.cell_id == pre.cell_id
            &&& self.batch_perms matches Some(batch_perms)
            &&& batch_perms.mem_contents().is_uninit()
            &&& batch_perms@.pcell == self.cell_id
            &&& self.local_updates matches Some(local_updates)
            &&& local_updates.instance_id() == inst.id()
            &&& local_updates.value().is_Done()
            &&& local_updates.key() == pre.fc_clients.value().get_Waiting_0()
            &&& local_updates.value().get_Done_ret() == ret
            &&& self.fc_clients.instance_id() == pre.fc_clients.instance_id()
            &&& self.fc_clients.key() == pre.fc_clients.key()
            &&& self.fc_clients.value().is_Idle()
        }
        &&& ret.is_none() ==> {
            &&& self == pre
        }
    }
}

} 
}
pub mod log {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::{
    atomic_ghost::{AtomicBool, AtomicU64},
    atomic_with_ghost,
    cell::{CellId, PCell},
    map::Map,
    prelude::*,
};

#[cfg(verus_keep_ghost)]
use crate::spec::cyclicbuffer::{log_entry_alive_value, log_entry_idx, stored_type_inv};
use crate::spec::cyclicbuffer::{CyclicBuffer, LogicalLogIdx, StoredType};
use crate::spec::types::{ConcreteLogEntry, LogIdx, NodeId, ReqId};
use crate::spec::unbounded_log::UnboundedLog;
use crate::Dispatch;

use crate::constants::{
    GC_FROM_HEAD, LOG_SIZE, MAX_IDX, MAX_REPLICAS, MAX_REQUESTS, WARN_THRESHOLD,
};
use crate::exec::replica::{ReplicaId, ReplicaToken};
use crate::exec::CachePadded;

verus! {

#[verus::line_count::ignore]
#[verus::trusted]
#[verifier(external_body)]             
pub fn print_starvation_warning(line: u32) {
    eprintln!("WARNING({line}): has been looping for `WARN_THRESHOLD` iterations. Are we starving?");
}

#[verus::trusted]
#[verifier(external_body)]             
pub fn warn_with_tail_too_big() {
    eprintln!("WARNING: Tail value exceeds the maximum value of u64.");
}

struct_with_invariants!{
#[repr(align(128))]
pub struct BufferEntry<DT: Dispatch> {

    pub log_entry: PCell<Option<ConcreteLogEntry<DT>>>,

    pub alive: AtomicBool<_, CyclicBuffer::alive_bits<DT>, _>,

    pub cyclic_buffer_idx: Ghost<nat>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>
}

pub open spec fn wf(&self, idx: nat, cb_inst: CyclicBuffer::Instance<DT>) -> bool {
    predicate {
        &&& self.cyclic_buffer_instance@ == cb_inst
        &&& self.cyclic_buffer_idx == idx
    }
    invariant on alive with (cyclic_buffer_idx, cyclic_buffer_instance) is (v: bool, g: CyclicBuffer::alive_bits<DT>) {
        &&& g.instance_id() == cyclic_buffer_instance@.id()
        &&& g.key() == cyclic_buffer_idx@
        &&& g.value() === v
    }
}
}  


struct_with_invariants!{
#[repr(align(128))]
pub struct NrLog<DT: Dispatch>
{
    pub slog: Vec<BufferEntry<DT>>,

    pub version_upper_bound: CachePadded<AtomicU64<_, UnboundedLog::version_upper_bound<DT>, _>>,

    pub head: CachePadded<AtomicU64<_, CyclicBuffer::head<DT>, _>>,

    pub tail: CachePadded<AtomicU64<_, (UnboundedLog::tail<DT>, CyclicBuffer::tail<DT>), _>>,

    pub                    local_versions: Vec<CachePadded<AtomicU64<_, (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>), _>>>,  


    pub num_replicas: Ghost<nat>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
}

pub open spec fn wf(&self) -> bool {
    predicate {
        &&& 0 < self.num_replicas@ <=  MAX_REPLICAS

        &&& self.local_versions.len() == self.num_replicas

        &&& self.slog.len() == LOG_SIZE
        &&& self.slog.len() == self.cyclic_buffer_instance@.buffer_size()
        &&& self.slog.len() == self.cyclic_buffer_instance@.cell_ids().len()
        &&& (forall |i| #![trigger self.slog[i]] 0 <= i < self.slog.len() ==> {
            &&& self.slog[i].log_entry.id() == (#[trigger]self.cyclic_buffer_instance@.cell_ids()[i])
        })

        &&& (forall |i: nat| i < LOG_SIZE ==> (#[trigger] self.slog[i as int]).wf(i, self.cyclic_buffer_instance@))

        &&& self.unbounded_log_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance@.unbounded_log_instance() == self.unbounded_log_instance
    }

    invariant on version_upper_bound with (unbounded_log_instance) specifically (self.version_upper_bound.0) is (v: u64, g: UnboundedLog::version_upper_bound<DT>) {
        &&& g.instance_id() == unbounded_log_instance@.id()
        &&& g.value() == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on head with (cyclic_buffer_instance) specifically (self.head.0) is (v: u64, g: CyclicBuffer::head<DT>) {
        &&& g.instance_id() == cyclic_buffer_instance@.id()
        &&& g.value() == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on tail with (cyclic_buffer_instance, unbounded_log_instance) specifically (self.tail.0) is (v: u64, g: (UnboundedLog::tail<DT>, CyclicBuffer::tail<DT>)) {
        &&& g.0.instance_id() == unbounded_log_instance@.id()
        &&& g.0.value() == v
        &&& g.1.instance_id() == cyclic_buffer_instance@.id()
        &&& g.1.value() == v
        &&& 0 <= v <= MAX_IDX
    }

    invariant on local_versions with (unbounded_log_instance, cyclic_buffer_instance)
        forall |i: int|
        where (0 <= i < self.local_versions@.len())
        specifically (self.local_versions@[i].0)
        is (v: u64, g: (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>)) {

        &&& g.0.instance_id() == unbounded_log_instance@.id()
        &&& g.0.key() == i
        &&& g.0.value() == v
        &&& g.1.instance_id() == cyclic_buffer_instance@.id()
        &&& g.1.key() == i
        &&& g.1.value() == v
        &&& 0 <= v <= MAX_IDX
    }
}
}  


impl<DT: Dispatch> NrLog<DT> {
    pub fn new(num_replicas: usize, log_size: usize) -> (res: (
        Self,
        Vec<ReplicaToken>,
        Tracked<NrLogTokens<DT>>,
    ))
        requires
            log_size == LOG_SIZE,
            0 < num_replicas && num_replicas <= MAX_REPLICAS,
        ensures
            res.0.wf(),
            res.0.unbounded_log_instance@ == res.2@.unbounded_log_instance,
            res.0.cyclic_buffer_instance@ == res.2@.cyclic_buffer_instance,
            res.1.len() == num_replicas,
            forall|i| #![trigger res.1[i]] 0 <= i < num_replicas ==> res.1[i].id_spec() == i,
            res.2@.wf(num_replicas as nat),
    {
        let tracked unbounded_log_instance: UnboundedLog::Instance<DT>;
        let tracked ul_tail: UnboundedLog::tail<DT>;
        let tracked ul_replicas: Map<NodeId, UnboundedLog::replicas<DT>>;
        let tracked mut ul_local_versions: Map<NodeId, UnboundedLog::local_versions<DT>>;
        let tracked ul_version_upper_bound: UnboundedLog::version_upper_bound<DT>;
        let tracked ul_combiner: Map<NodeId, UnboundedLog::combiner<DT>>;
        proof {
            let tracked (
                Tracked(unbounded_log_instance0),  
                Tracked(ul_log0),  
                Tracked(ul_tail0),  
                Tracked(ul_replicas0),  
                Tracked(ul_local_versions0),  
                Tracked(ul_version_upper_bound0),  
                _,  
                _,  
                Tracked(ul_combiner0),  
            ) = UnboundedLog::Instance::initialize(num_replicas as nat);
            unbounded_log_instance = unbounded_log_instance0;
            ul_tail = ul_tail0;
            ul_replicas = ul_replicas0.into_map();
            ul_local_versions = ul_local_versions0.into_map();
            ul_version_upper_bound = ul_version_upper_bound0;
            ul_combiner = ul_combiner0.into_map();
        }
        let ghost mut logical_log_idx;
        proof {
            logical_log_idx = -log_size as int;
        }
        let mut slog_entries: Vec<Option<PCell<Option<ConcreteLogEntry<DT>>>>> = Vec::with_capacity(
            log_size,
        );
        let ghost mut cell_ids: Seq<CellId> = Seq::empty();
        let tracked mut contents: Map<LogicalLogIdx, StoredType<DT>> = Map::tracked_empty();
        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                log_size == LOG_SIZE,
                logical_log_idx == log_idx - log_size,
                -log_size <= logical_log_idx <= 0,
                slog_entries.len() == log_idx,
                cell_ids.len() == log_idx,
                forall|i| 0 <= i < log_idx ==> (#[trigger] slog_entries[i]).is_some(),
                forall|i|
                    0 <= i < log_idx ==> #[trigger] cell_ids[i] == (
                    #[trigger] slog_entries[i]).unwrap().id(),
                forall|i| -log_size <= i < logical_log_idx <==> #[trigger] contents.contains_key(i),
                forall|i| #[trigger]
                    contents.contains_key(i) ==> stored_type_inv(
                        contents[i],
                        i,
                        cell_ids[log_entry_idx(i, log_size as nat) as int],
                        unbounded_log_instance,
                    ),
            decreases log_size - log_idx
        {
            let (pcell, token) = PCell::new(Option::None);
            proof {
                cell_ids = cell_ids.push(pcell.id());
            }
            slog_entries.push(Option::Some(pcell));
            let tracked stored_type = StoredType {
                cell_perms: token.get(),
                log_entry: Option::None,
            };
            proof {
                contents.tracked_insert(logical_log_idx, stored_type);
            }
            log_idx = log_idx + 1;
            proof {
                logical_log_idx = logical_log_idx + 1;
            }
        }

        let tracked cyclic_buffer_instance: CyclicBuffer::Instance<DT>;
        let tracked cb_head: CyclicBuffer::head<DT>;
        let tracked cb_tail: CyclicBuffer::tail<DT>;
        let tracked mut cb_local_versions: Map<NodeId, CyclicBuffer::local_versions<DT>>;
        let tracked mut cb_alive_bits: Map<LogIdx, CyclicBuffer::alive_bits<DT>>;
        let tracked cb_combiners: Map<NodeId, CyclicBuffer::combiner<DT>>;
        proof {
            let tracked (
                Tracked(cyclic_buffer_instance0),  
                Tracked(cb_head0),  
                Tracked(cb_tail0),  
                Tracked(cb_local_versions0),  
                Tracked(cb_alive_bits0),  
                Tracked(cb_combiner0),  
            ) = CyclicBuffer::Instance::initialize(
                log_size as nat,
                num_replicas as nat,
                contents,
                cell_ids,
                unbounded_log_instance,
                contents,
            );
            cyclic_buffer_instance = cyclic_buffer_instance0;
            cb_head = cb_head0;
            cb_tail = cb_tail0;
            cb_local_versions = cb_local_versions0.into_map();
            cb_alive_bits = cb_alive_bits0.into_map();
            cb_combiners = cb_combiner0.into_map();
        }
        let mut slog: Vec<BufferEntry<DT>> = Vec::with_capacity(log_size);
        let mut log_idx = 0;
        while log_idx < log_size
            invariant
                0 <= log_idx <= log_size,
                slog_entries.len() == log_size,
                slog.len() == log_idx,
                cell_ids.len() == log_size,
                forall|i|
                    #![trigger slog[i]]
                    0 <= i < log_idx ==> {
                        &&& slog[i].wf(i as nat, cyclic_buffer_instance)
                        &&& slog[i].log_entry.id() == (#[trigger] cell_ids[i])
                    },
                forall|i| log_idx <= i < log_size ==> cb_alive_bits.contains_key(i),
                forall|i|
                    #![trigger cb_alive_bits[i]]
                    log_idx <= i < log_size ==> {
                        &&& cb_alive_bits[i].key() == i
                        &&& cb_alive_bits[i].value() == false
                        &&& cb_alive_bits[i].instance_id() == cyclic_buffer_instance.id()
                    },
                forall|i| 0 <= i < log_idx ==> slog_entries.spec_index(i).is_none(),
                forall|i|
                    #![trigger slog_entries[i]]
                    log_idx <= i < log_size ==> {
                        &&& slog_entries[i] matches Some(entry)
                        &&& entry.id() == cell_ids[i]
                    },
            decreases log_size - log_idx
        {
            let tracked cb_alive_bit;
            proof {
                cb_alive_bit = cb_alive_bits.tracked_remove(log_idx as nat);
            }
            let mut log_entry = Option::None;
            slog_entries.set_and_swap(log_idx, &mut log_entry);
            assert(log_entry.is_some());
            let log_entry = log_entry.unwrap();
            let cb_inst = Tracked(cyclic_buffer_instance.clone());
            let entry = BufferEntry {
                log_entry: log_entry,
                alive: AtomicBool::new(
                    Ghost((Ghost(log_idx as nat), cb_inst)),
                    false,
                    Tracked(cb_alive_bit),
                ),
                cyclic_buffer_idx: Ghost(log_idx as nat),
                cyclic_buffer_instance: Tracked(cyclic_buffer_instance.clone()),
            };
            slog.push(entry);
            log_idx = log_idx + 1;
        }
        let ul_inst = Tracked(unbounded_log_instance.clone());
        let version_upper_bound = CachePadded(
            AtomicU64::new(Ghost(ul_inst), 0, Tracked(ul_version_upper_bound)),
        );
        let cb_inst = Tracked(cyclic_buffer_instance.clone());
        let head = CachePadded(AtomicU64::new(Ghost(cb_inst), 0, Tracked(cb_head)));
        let cb_inst = Tracked(cyclic_buffer_instance.clone());
        let ul_inst = Tracked(unbounded_log_instance.clone());
        let tail = CachePadded(
            AtomicU64::new(Ghost((cb_inst, ul_inst)), 0, Tracked((ul_tail, cb_tail))),
        );
        let mut local_versions: Vec<
            CachePadded<
                AtomicU64<
                    (Tracked<UnboundedLog::Instance<DT>>, Tracked<CyclicBuffer::Instance<DT>>, int),
                    (UnboundedLog::local_versions<DT>, CyclicBuffer::local_versions<DT>),
                    _,
                >,
            >,
        > = Vec::with_capacity(num_replicas);
        let mut nid = 0;
        while nid < num_replicas
            invariant
                0 <= nid <= num_replicas,
                local_versions.len() == nid,
                forall|i| nid <= i < num_replicas ==> ul_local_versions.contains_key(i),
                forall|i| nid <= i < num_replicas ==> cb_local_versions.contains_key(i),
                forall|i|
                    #![trigger cb_local_versions[i]]
                    nid <= i < num_replicas ==> {
                        &&& cb_local_versions[i].instance_id() == cyclic_buffer_instance.id()
                        &&& cb_local_versions[i].key() == i
                        &&& cb_local_versions[i].value() == 0
                    },
                forall|i|
                    #![trigger ul_local_versions[i]]
                    nid <= i < num_replicas ==> {
                        &&& ul_local_versions[i].instance_id() == unbounded_log_instance.id()
                        &&& ul_local_versions[i].key() == i
                        &&& ul_local_versions[i].value() == 0
                    },
                forall|i: int|
                    #![trigger local_versions[i]]
                    0 <= i < local_versions.len() ==> {
                        &&& local_versions[i].0.well_formed()
                        &&& local_versions[i].0.constant().0 == unbounded_log_instance
                        &&& local_versions[i].0.constant().1 == cyclic_buffer_instance
                        &&& local_versions[i].0.constant().2 == i
                    },
            decreases num_replicas - nid
        {
            let ghost mut nid_ghost;
            let tracked ul_version;
            let tracked cb_version;
            proof {
                nid_ghost = nid as int;
                ul_version = ul_local_versions.tracked_remove(nid as nat);
                cb_version = cb_local_versions.tracked_remove(nid as nat);
            }
            let cb_inst = Tracked(cyclic_buffer_instance.clone());
            let ul_inst = Tracked(unbounded_log_instance.clone());
            local_versions.push(
                CachePadded(
                    AtomicU64::new(
                        Ghost((ul_inst, cb_inst, nid_ghost)),
                        0,
                        Tracked((ul_version, cb_version)),
                    ),
                ),
            );
            nid = nid + 1;
        }

        let mut replica_tokens: Vec<ReplicaToken> = Vec::with_capacity(num_replicas);
        let mut idx = 0;
        while idx < num_replicas
            invariant
                0 <= idx <= num_replicas,
                num_replicas <= MAX_REPLICAS,
                replica_tokens.len() == idx,
                forall|i|
                    #![trigger replica_tokens[i]]
                    0 <= i < idx ==> replica_tokens[i].id_spec() == i,
            decreases num_replicas - idx
        {
            replica_tokens.push(ReplicaToken::new(idx as ReplicaId));
            idx = idx + 1;
        }
        let ghost mut num_replicas_ghost;
        proof { num_replicas_ghost = num_replicas as nat }
        ;
        let tracked config = NrLogTokens {
            num_replicas: num_replicas_ghost,
            replicas: ul_replicas,
            combiners: ul_combiner,
            cb_combiners,
            unbounded_log_instance: unbounded_log_instance.clone(),
            cyclic_buffer_instance: cyclic_buffer_instance.clone(),
        };
        let log = NrLog {
            slog,
            version_upper_bound,
            head,
            tail,
            local_versions,
            num_replicas: Ghost(num_replicas as nat),
            unbounded_log_instance: Tracked(unbounded_log_instance),
            cyclic_buffer_instance: Tracked(cyclic_buffer_instance),
        };
        (log, replica_tokens, Tracked(config))
    }

    #[inline(always)]
    pub(crate) fn index(&self, logical: u64) -> (result: usize)
        requires
            self.slog.len() == LOG_SIZE,
        ensures
            result as nat == self.index_spec(logical as nat),
            result == log_entry_idx(logical as int, self.slog.len() as nat),
            result < self.slog.len(),
    {
        (logical as usize) % self.slog.len()
    }

    pub                     
     open spec fn index_spec(&self, logical: nat) -> nat
        recommends
            self.slog.len() == LOG_SIZE,
    {
        logical % (self.slog.len() as nat)
    }

    #[inline(always)]
    pub(crate) fn is_alive_value(&self, logical: u64) -> (result: bool)
        requires
            self.slog.len() == LOG_SIZE,
        ensures
            result == self.is_alive_value_spec(logical as int),
            result == log_entry_alive_value(logical as int, self.slog.len() as nat),
    {
        ((logical as usize) / LOG_SIZE % 2) == 0
    }

    pub                     
     open spec fn is_alive_value_spec(&self, logical: int) -> bool
        recommends
            self.slog.len() == LOG_SIZE,
    {
        ((logical / (LOG_SIZE as int)) % 2) == 0
    }

    pub(crate) fn get_version_upper_bound(
        &self,
        local_reads: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (ret: (u64, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            local_reads@.instance_id() == self.unbounded_log_instance@.id(),
            local_reads@.value().is_Init(),
        ensures
            ret.1@.value().is_VersionUpperBound(),
            ret.1@.value().get_VersionUpperBound_version_upper_bound() == ret.0 as nat,
            ret.1@.value().get_VersionUpperBound_op() == local_reads@.value().get_Init_op(),
            ret.1@.instance_id() == self.unbounded_log_instance@.id(),
            ret.1@.key() == local_reads@.key(),
    {
        let tracked local_reads = local_reads.get();
        let ghost rid = local_reads.key();
        let tracked new_local_reads_g: UnboundedLog::local_reads<DT>;
        let res =
            atomic_with_ghost!(
            &self.version_upper_bound.0 => load();
            returning res;
            ghost g => {
                new_local_reads_g = self.unbounded_log_instance.borrow()
                                            .readonly_version_upper_bound(rid, &g, local_reads);
            }
        );
        (res, Tracked(new_local_reads_g))
    }

    pub fn is_replica_synced_for_reads(
        &self,
        node_id: ReplicaId,
        version_upper_bound: u64,
        local_reads: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (result: (bool, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            node_id < self.local_versions.len(),
            local_reads@.instance_id() == self.unbounded_log_instance@.id(),
            local_reads@.value().is_VersionUpperBound(),
            local_reads@.value().get_VersionUpperBound_version_upper_bound() == version_upper_bound,
        ensures
            result.0 ==> result.1@.value().is_ReadyToRead(),
            result.0 ==> result.1@.value().get_ReadyToRead_node_id() == node_id,
            result.0 ==> result.1@.value().get_ReadyToRead_op()
                == local_reads@.value().get_VersionUpperBound_op(),
            !result.0 ==> result.1 == local_reads,
            result.1@.instance_id() == self.unbounded_log_instance@.id(),
            result.1@.key() == local_reads@.key(),
    {
        let rid_g: Ghost<ReqId> = Ghost(local_reads@.key());
        let tracked new_local_reads_g: UnboundedLog::local_reads<DT>;
        let local_version = &self.local_versions[node_id as usize].0;
        let res =
            atomic_with_ghost!(
            local_version => load();
            returning res;
            ghost g => {
                new_local_reads_g = if res >= version_upper_bound {
                    self.unbounded_log_instance
                        .borrow()
                        .readonly_ready_to_read(rid_g.view(), node_id as NodeId, &g.0, local_reads.get())
                } else {
                    local_reads.get()
                };
            }
        );
        (res >= version_upper_bound, Tracked(new_local_reads_g))
    }

    proof fn unbounded_log_append_entries(
        tracked &self,
        nid: nat,
        ridx: nat,
        tracked state: AppendEntriesGhostState<DT>,
    ) -> (tracked ret: AppendEntriesGhostState<DT>)
        requires
            self.wf(),
            state.idx == 0,
            state.wf(nid, ridx, self.unbounded_log_instance@),
        ensures
            ret.request_ids == state.request_ids,
            ret.operations == state.operations,
            ret.idx == ridx + 1,
            ret.old_tail == state.old_tail,
            ret.wf(nid, ridx, self.unbounded_log_instance@),
        decreases ridx,
    {
        let tracked mut state = state;
        if ridx != 0 {
            state = self.unbounded_log_append_entries(nid, (ridx - 1) as nat, state);
        }
        let tracked AppendEntriesGhostState {
            idx,
            old_tail,
            mut log_entries,
            mut local_updates,
            combiner,
            mut tail,
            request_ids,
            operations,
        } = state;
        let reqid = request_ids[ridx as int];
        let tracked local_update = local_updates.tracked_remove(ridx);
        let tracked update_result =
            self.unbounded_log_instance.borrow().update_place_ops_in_log_one(
            nid as nat,
            reqid,
            &mut tail,
            local_update,
            combiner,
        );
        let tracked combiner = update_result.2.get();
        log_entries.tracked_insert(ridx, update_result.0.get());
        local_updates.tracked_insert(ridx, update_result.1.get());
        let tracked res = AppendEntriesGhostState {
            idx: idx + 1,
            old_tail,
            log_entries,
            local_updates,
            combiner,
            tail,
            request_ids,
            operations,
        };
        res
    }

    #[inline(always)]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn append(
        &self,
        replica_token: &ReplicaToken,
        operations: &Vec<DT::WriteOperation>,
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>,
    ) -> (result: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            replica_token@ < self.local_versions.len(),
            old(responses).len() == 0,
            ghost_data@.append_pre(
                replica_token@,
                old(actual_replica).view(),
                operations@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
            operations.len() <= MAX_REQUESTS,
        ensures
            result@.append_post(
                ghost_data@,
                replica_token@,
                final(actual_replica).view(),
                operations@,
                final(responses)@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
    {
        let tracked mut ghost_data_new = ghost_data.get();
        let nid = replica_token.id() as usize;
        let nops = operations.len();
        let mut iteration = 1;
        let mut waitgc = 1;
        loop
            invariant
                self.wf(),
                0 <= waitgc <= WARN_THRESHOLD,
                0 <= iteration <= WARN_THRESHOLD,
                responses.len() == 0,
                replica_token@ < self.local_versions.len(),
                nid == replica_token@,
                nops == operations.len(),
                nops <= MAX_REQUESTS,
                ghost_data_new.cb_combiner@.value() == ghost_data@.cb_combiner@.value(),
                ghost_data_new.request_ids@ == ghost_data@.request_ids@,
                ghost_data_new.append_pre(
                    replica_token@,
                    actual_replica.view(),
                    operations@,
                    self.unbounded_log_instance@,
                    self.cyclic_buffer_instance@,
                ),
        {
            let tracked NrLogAppendExecDataGhost {
                local_updates,
                ghost_replica,
                combiner,
                cb_combiner,
                request_ids,
            } = ghost_data_new;
            let tracked mut cb_combiner = cb_combiner.get();
            let tracked mut combiner = combiner.get();
            let tracked mut local_updates = local_updates.get();
            if iteration == WARN_THRESHOLD {
                print_starvation_warning(line!());
                iteration = 0;
            }
            iteration = iteration + 1;
            let tail =
                atomic_with_ghost!(
                &self.tail.0 => load();
                returning tail;
                ghost g => { }
            );
            let head =
                atomic_with_ghost!(
                &self.head.0 => load();
                returning tail;
                ghost g => {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_tail_start(nid as nat, &g, cb_combiner);
                }
            );
            if tail > head + (self.slog.len() as u64 - GC_FROM_HEAD as u64) {
                if waitgc == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    waitgc = 0;
                }
                waitgc = waitgc + 1;
                proof {
                    cb_combiner =
                    self.cyclic_buffer_instance.borrow().advance_tail_abort(
                        nid as nat,
                        cb_combiner,
                    );
                }
                let tracked ghost_data0 = NrLogAppendExecDataGhost {
                    local_updates: Tracked(local_updates),
                    ghost_replica,
                    combiner: Tracked(combiner),
                    cb_combiner: Tracked(cb_combiner),
                    request_ids: Ghost(Seq::empty()),
                };
                let ghost_data0 = self.execute(
                    replica_token,
                    responses,
                    actual_replica,
                    Tracked(ghost_data0),
                );
                let tracked ghost_data0 = ghost_data0.get();
                proof {
                    ghost_data_new =
                    NrLogAppendExecDataGhost {
                        local_updates: ghost_data0.local_updates,
                        ghost_replica: ghost_data0.ghost_replica,
                        combiner: ghost_data0.combiner,
                        cb_combiner: ghost_data0.cb_combiner,
                        request_ids,
                    };
                }
                continue ;
            }
            let new_tail = tail + (nops as u64);
            if new_tail >= MAX_IDX {
                warn_with_tail_too_big();
                #[allow(while_true)]
                while true {
                }  

            }

            let advance = new_tail > head + (self.slog.len() - GC_FROM_HEAD) as u64;
            let tracked mut cb_log_entries: Map<int, StoredType<DT>> = Map::tracked_empty();
            let tracked mut log_entries: Map<nat, UnboundedLog::log<DT>> = Map::tracked_empty();
            let result =
                atomic_with_ghost!(
                &self.tail.0 => compare_exchange_weak(tail, new_tail);
                update prev -> next;
                returning result;
                ghost g => {
                    if prev == tail {
                        let tracked (_, Tracked(withdrawn), Tracked(new_cb_combiner)) =
                            self.cyclic_buffer_instance.borrow().advance_tail_finish(nid as nat, new_tail as nat, &mut g.1, cb_combiner);
                        cb_combiner = new_cb_combiner;
                        cb_log_entries = withdrawn;
                        if nops > 0 {
                            combiner = self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);
                            let tracked append_state = AppendEntriesGhostState {
                                idx: 0,
                                old_tail: tail as nat,
                                log_entries: Map::tracked_empty(),
                                local_updates,
                                combiner,
                                tail: g.0,
                                request_ids: request_ids@,
                                operations: operations@,
                            };
                            let tracked ret = self.unbounded_log_append_entries(nid as nat, (nops - 1) as nat, append_state);
                            local_updates = ret.local_updates;
                            combiner = ret.combiner;
                            log_entries = ret.log_entries;
                            g.0 = ret.tail;
                        }
                    } else {
                        cb_combiner = self.cyclic_buffer_instance.borrow().advance_tail_abort(nid as nat, cb_combiner);
                    }
                }
            );
            if !matches!(result, Result::Ok(tail)) {
                proof {
                    ghost_data_new =
                    NrLogAppendExecDataGhost {
                        local_updates: Tracked(local_updates),  
                        ghost_replica,  
                        combiner: Tracked(combiner),  
                        cb_combiner: Tracked(cb_combiner),  
                        request_ids,  
                    };
                }
                continue ;
            }
            let ghost cell_ids = self.cyclic_buffer_instance@.cell_ids();
            let ghost buffer_size = self.cyclic_buffer_instance@.buffer_size();
            let mut idx = 0;
            while idx < nops
                invariant
                    self.wf(),
                    0 <= idx <= nops,
                    tail + idx <= new_tail,
                    tail + nops == new_tail,
                    nops == operations.len(),
                    nops == request_ids@.len(),
                    buffer_size == LOG_SIZE,
                    cell_ids == self.cyclic_buffer_instance@.cell_ids(),
                    cell_ids.len() == buffer_size,
                    cb_combiner.key() == nid,
                    cb_combiner.value().is_Appending(),
                    cb_combiner.value().get_Appending_cur_idx() == tail + idx,
                    cb_combiner.value().get_Appending_tail() == new_tail,
                    cb_combiner.value().get_Appending_cur_idx()
                        <= cb_combiner.value().get_Appending_tail(),
                    cb_combiner.instance_id() == self.cyclic_buffer_instance@.id(),
                    forall|i|
                        #![trigger log_entries[i]]
                        idx <= i < request_ids@.len() ==> {
                            &&& (#[trigger] log_entries.contains_key(i))
                            &&& log_entries[i].key() == tail + i
                            &&& log_entries[i].instance_id() == self.unbounded_log_instance@.id()
                            &&& log_entries[i].value().node_id
                                == nid as nat

                            &&& log_entries[i].value().op
                                == operations[i as int]

                        },
                    forall|i|
                        (tail + idx) - LOG_SIZE <= i < new_tail - LOG_SIZE
                            <==> cb_log_entries.contains_key(i),
                    forall|i|
                        cb_log_entries.contains_key(i) ==> stored_type_inv(
                            #[trigger] cb_log_entries.index(i),
                            i,
                            cell_ids[log_entry_idx(i, buffer_size) as int],
                            self.unbounded_log_instance@,
                        ),
                decreases nops - idx
            {
                let tracked cb_log_entry;
                proof {
                    cb_log_entry = cb_log_entries.tracked_remove((tail + idx) - LOG_SIZE);
                }
                let tracked mut cb_log_entry_perms = cb_log_entry.cell_perms;
                let logical_log_idx = tail + idx as u64;
                let log_idx = self.index(logical_log_idx);
                let new_log_entry = ConcreteLogEntry {
                    op: DT::clone_write_op(&operations[idx as usize]),
                    node_id: nid as u64,
                };
                self.slog[log_idx].log_entry.replace(
                    Tracked(&mut cb_log_entry_perms),
                    Option::Some(new_log_entry),
                );
                let m = self.is_alive_value(logical_log_idx as u64);
                atomic_with_ghost!(
                    &self.slog[log_idx].alive => store(m);
                    ghost g => {
                        let tracked log_entry_tok = log_entries.tracked_remove(idx as nat);
                        let tracked deposited = StoredType {
                            cell_perms: cb_log_entry_perms,
                            log_entry: Option::Some(log_entry_tok),
                        };
                        let tracked (Tracked(new_alive_bit), Tracked(new_cb_combiner)) =
                            self.cyclic_buffer_instance.borrow().append_flip_bit(nid as nat, deposited, deposited, g, cb_combiner);
                        g = new_alive_bit;
                        cb_combiner = new_cb_combiner;
                    }
                );
                idx = idx + 1;
            }
            assert(forall|i|
                #![trigger log_entries[i]]
                idx <= i < request_ids@.len() ==> {
                    &&& #[trigger] log_entries.contains_key(i)
                    &&& log_entries[i].key() == tail + i
                    &&& log_entries[i].instance_id() == self.unbounded_log_instance@.id()
                    &&& log_entries[i].value().node_id == nid as nat
                    &&& log_entries[i].value().op == operations[i as int]
                });
            assert(forall|i|
                (tail + idx) - LOG_SIZE <= i < new_tail - LOG_SIZE <==> cb_log_entries.contains_key(
                    i,
                ));
            assert(forall|i|
                cb_log_entries.contains_key(i) ==> stored_type_inv(
                    #[trigger] cb_log_entries.index(i),
                    i,
                    cell_ids[log_entry_idx(i, buffer_size) as int],
                    self.unbounded_log_instance@,
                ));
            proof {
                cb_combiner =
                self.cyclic_buffer_instance.borrow().append_finish(nid as nat, cb_combiner);
                ghost_data_new =
                NrLogAppendExecDataGhost {
                    local_updates: Tracked(local_updates),  
                    ghost_replica,  
                    combiner: Tracked(combiner),  
                    cb_combiner: Tracked(cb_combiner),  
                    request_ids,  
                };
            }
            if advance {
                let ghost_data_new = self.advance_head(
                    replica_token,
                    responses,
                    actual_replica,
                    Tracked(ghost_data_new),
                );
                return ghost_data_new;
            } else {
                return Tracked(ghost_data_new);
            }
        }
    }

    #[inline(always)]
    #[verifier::exec_allows_no_decreases_clause]
    fn advance_head(
        &self,
        replica_token: &ReplicaToken,
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>,
    ) -> (res: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            replica_token.wf(self.num_replicas@),
            ghost_data@.advance_head_pre(
                replica_token.id_spec(),
                old(actual_replica).view(),
                old(responses)@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
        ensures
            res@.advance_head_post(
                ghost_data@,
                replica_token.id_spec(),
                final(actual_replica).view(),
                final(responses)@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
    {
        let mut ghost_data_new = ghost_data;
        let mut iteration = 1;
        loop
            invariant
                self.wf(),
                replica_token.wf(self.num_replicas@),
                ghost_data_new@.cb_combiner@.value().is_Idle(),
                ghost_data_new@.combiner@.value().is_Placed() ==> ghost_data_new@.pre_exec(
                    responses@,
                ),
                ghost_data_new@.advance_head_post(
                    ghost_data@,
                    replica_token.id_spec(),
                    actual_replica.view(),
                    responses@,
                    self.unbounded_log_instance@,
                    self.cyclic_buffer_instance@,
                ),
                0 <= iteration <= WARN_THRESHOLD,
        {
            let Tracked(ghost_data0) = ghost_data_new;
            let tracked NrLogAppendExecDataGhost {
                local_updates,
                ghost_replica,
                combiner,
                cb_combiner,
                request_ids,
            } = ghost_data0;
            let tracked mut cb_combiner = cb_combiner.get();
            let global_head =
                atomic_with_ghost!(
                &self.head.0 => load();
                returning ret;
                ghost g => {             }
            );
            let global_tail =
                atomic_with_ghost!(
                &self.tail.0 => load();
                returning ret;
                ghost g => {             }
            );
            let (min_local_version, cb_combiner0) = self.find_min_local_version(
                Tracked(cb_combiner),
            );
            let tracked mut cb_combiner = cb_combiner0.get();
            if min_local_version == global_head {
                proof {
                    cb_combiner =
                    self.cyclic_buffer_instance.borrow().advance_head_abort(
                        replica_token.id_spec(),
                        cb_combiner,
                    );
                }
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    iteration = 0;
                }
                let cb_combiner = Tracked(cb_combiner);
                let tracked ghost_data0 = NrLogAppendExecDataGhost {
                    local_updates,
                    ghost_replica,
                    combiner,
                    cb_combiner,
                    request_ids,
                };
                ghost_data_new =
                self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
                continue ;
            }

            atomic_with_ghost!(
                &self.head.0 => store(min_local_version);
                update old_val -> new_val;
                ghost g => {
                    cb_combiner = self.cyclic_buffer_instance.borrow().advance_head_finish(replica_token.id_spec(), &mut g, cb_combiner);
            });
            if global_tail < min_local_version + self.slog.len() as u64 - GC_FROM_HEAD as u64 {
                let cb_combiner = Tracked(cb_combiner);
                let tracked ghost_data_new = NrLogAppendExecDataGhost {
                    local_updates,
                    ghost_replica,
                    combiner,
                    cb_combiner,
                    request_ids,
                };
                return Tracked(ghost_data_new);
            }
            let cb_combiner = Tracked(cb_combiner);
            let tracked ghost_data0 = NrLogAppendExecDataGhost {
                local_updates,
                ghost_replica,
                combiner,
                cb_combiner,
                request_ids,
            };
            ghost_data_new =
            self.execute(replica_token, responses, actual_replica, Tracked(ghost_data0));
        }
    }

    proof fn execute_update_done_multiple(
        tracked &self,
        request_ids: Seq<ReqId>,
        tracked local_updates: Map<nat, UnboundedLog::local_updates<DT>>,
        tracked version_upper_bound: &UnboundedLog::version_upper_bound<DT>,
    ) -> (tracked res: Map<nat, UnboundedLog::local_updates<DT>>)
        requires
            self.wf(),
            version_upper_bound.instance_id() == self.unbounded_log_instance@.id(),
            forall|i|
                #![trigger local_updates[i]]
                0 <= i < request_ids.len() ==> {
                    &&& #[trigger] local_updates.contains_key(i)
                    &&& local_updates[i].key() == request_ids[i as int]
                    &&& local_updates[i].instance_id() == self.unbounded_log_instance@.id()
                    &&& local_updates[i].value().is_Applied()
                    &&& local_updates[i].value().get_Applied_idx() < version_upper_bound.value()
                },
        ensures
            forall|i|
                #![trigger res[i]]
                0 <= i < request_ids.len() ==> {
                    &&& #[trigger] res.contains_key(i)
                    &&& res[i].key() == request_ids[i as int]
                    &&& res[i].instance_id() == self.unbounded_log_instance@.id()
                    &&& res[i].value().is_Done()
                    &&& res[i].value().get_Done_ret() == local_updates[i].value().get_Applied_ret()
                },
        decreases request_ids.len(),
    {
        if request_ids.len() == 0 {
            return local_updates;
        }
        let tracked mut local_updates_new = local_updates;
        let idx = (request_ids.len() - 1) as nat;
        let tracked local_update = local_updates_new.tracked_remove(idx);
        local_updates_new =
        self.execute_update_done_multiple(
            request_ids.subrange(0, request_ids.len() - 1),
            local_updates_new,
            version_upper_bound,
        );
        let tracked update_done_result = self.unbounded_log_instance.borrow().update_done(
            request_ids.last(),
            version_upper_bound,
            local_update,
        );
        local_updates_new.tracked_insert(idx, update_done_result);
        return local_updates_new;
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn execute(
        &self,
        replica_token: &ReplicaToken,
        responses: &mut Vec<DT::Response>,
        actual_replica: &mut DT,
        ghost_data: Tracked<NrLogAppendExecDataGhost<DT>>,
    ) -> (result: Tracked<NrLogAppendExecDataGhost<DT>>)
        requires
            self.wf(),
            replica_token@ < self.local_versions.len(),
            ghost_data@.execute_pre(
                replica_token@,
                old(actual_replica).view(),
                old(responses)@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
        ensures
            result@.execute_post(
                ghost_data@,
                replica_token@,
                final(actual_replica).view(),
                old(responses)@,
                final(responses)@,
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ),
    {
        let nid = replica_token.id() as usize;
        let tracked ghost_data = ghost_data.get();
        let tracked mut local_updates = ghost_data.local_updates.get();  
        let tracked mut ghost_replica = ghost_data.ghost_replica.get();  
        let tracked mut combiner = ghost_data.combiner.get();  
        let tracked mut cb_combiner = ghost_data.cb_combiner.get();  
        let ghost request_ids = ghost_data.request_ids@;  
        let ghost mut request_ids_new = request_ids;
        proof {
            if combiner.value().is_Ready() {
                combiner =
                self.unbounded_log_instance.borrow().exec_trivial_start(nid as nat, combiner);
                request_ids_new = Seq::empty();
            }
        }
        let mut local_version =
            atomic_with_ghost!(
            &self.local_versions[nid].0 => load();
            returning ret;
            ghost g => {
                combiner = self.unbounded_log_instance.borrow().exec_load_local_version(nid as nat, &g.0, combiner);
                cb_combiner = self.cyclic_buffer_instance.borrow().reader_start(nid as nat, &g.1, cb_combiner);
            }
        );
        let global_tail =
            atomic_with_ghost!(
            &self.tail.0 => load();
            returning global_tail;
            ghost g => {
                if (local_version == global_tail) {
                    combiner = self.unbounded_log_instance.borrow().exec_finish_no_change(nid as nat, &g.0, combiner);
                    cb_combiner = self.cyclic_buffer_instance.borrow().reader_abort(nid as nat, cb_combiner);
                } else {
                    combiner = self.unbounded_log_instance.borrow().exec_load_global_head(nid as nat, &g.0, combiner);
                    cb_combiner = self.cyclic_buffer_instance.borrow().reader_enter(nid as nat,  &g.1, cb_combiner);
                }
            }
        );
        if local_version == global_tail {
            let tracked ghost_data_ret = NrLogAppendExecDataGhost {
                local_updates: Tracked(local_updates),  
                ghost_replica: Tracked(ghost_replica),  
                combiner: Tracked(combiner),  
                cb_combiner: Tracked(cb_combiner),  
                request_ids: Ghost(request_ids),  
            };
            assert(ghost_data_ret.common_pred(
                replica_token@,
                actual_replica.view(),
                self.unbounded_log_instance@,
                self.cyclic_buffer_instance@,
            ));
            return Tracked(ghost_data_ret);
        }

        let ghost local_updates_old = local_updates;
        let ghost responses_old = responses@;
        let mut responses_idx: usize = 0;
        while local_version < global_tail
            invariant
                self.wf(),
                ghost_data.combiner@.value().is_Placed() ==> {
                    &&& ghost_data.combiner@.value().get_Placed_queued_ops() == request_ids
                    &&& combiner.value().get_Loop_queued_ops() == request_ids
                },
                ghost_data.combiner@.value().is_Ready() ==> combiner.value().get_Loop_queued_ops()
                    == Seq::<ReqId>::empty(),
                combiner.value().queued_ops() == request_ids_new,
                0 <= local_version <= global_tail,
                0 <= responses_idx as nat <= request_ids_new.len(),
                responses_idx == 0 ==> responses@ == responses_old && local_updates
                    == local_updates_old,
                ghost_data.combiner@.value().is_Placed() ==> responses.len() == responses_idx,
                request_ids_new.len() <= MAX_REQUESTS,
                ghost_replica.instance_id() == self.unbounded_log_instance@.id(),
                ghost_replica.key() == nid as nat,
                ghost_replica.value() == actual_replica.view(),
                cb_combiner.key() == nid as nat,
                cb_combiner.instance_id() == self.cyclic_buffer_instance@.id(),
                cb_combiner.value().is_Reading(),
                cb_combiner.value().get_Reading_0().is_Range(),
                cb_combiner.value().get_Reading_0().get_Range_cur() == local_version,
                cb_combiner.value().get_Reading_0().get_Range_end() == global_tail,
                combiner.key() == nid as nat,
                combiner.instance_id() == self.unbounded_log_instance@.id(),
                combiner.value().is_Loop(),
                combiner.value().get_Loop_queued_ops() == request_ids_new,
                combiner.value().get_Loop_lversion() == local_version,
                combiner.value().get_Loop_tail() == global_tail,
                combiner.value().get_Loop_idx() == responses_idx,
                forall|i|
                    #![trigger local_updates[i]]
                    responses_idx <= i < request_ids_new.len() ==> {
                        &&& #[trigger ] local_updates.contains_key(i)
                        &&& local_updates[i].key() == request_ids_new[i as int]
                        &&& local_updates[i].value().is_Placed()
                        &&& local_updates[i].instance_id() == self.unbounded_log_instance@.id()
                    },
                ghost_data.combiner@.value().is_Placed() ==> forall|i|
                    #![trigger local_updates[i]]
                    0 <= i < responses_idx ==> {
                        &&& #[trigger] local_updates.contains_key(i)
                        &&& local_updates[i].key() == request_ids_new[i as int]
                        &&& local_updates[i].instance_id() == self.unbounded_log_instance@.id()
                        &&& local_updates[i].value().is_Applied()
                        &&& local_updates[i].value().get_Applied_ret() == responses[i as int]
                        &&& local_updates[i].value().get_Applied_idx()
                            < combiner.value().get_Loop_tail()
                    },
            decreases global_tail - local_version
        {
            let phys_log_idx = self.index(local_version);
            let is_alive_value = self.is_alive_value(local_version);
            let mut iteration = 1;
            let mut is_alive = false;
            while !is_alive
                invariant
                    self.wf(),
                    local_version < global_tail,
                    phys_log_idx < self.slog.len(),
                    phys_log_idx as nat == self.index_spec(local_version as nat),
                    is_alive_value == self.is_alive_value_spec(local_version as int),
                    0 <= iteration <= WARN_THRESHOLD,
                    cb_combiner.instance_id() == self.cyclic_buffer_instance@.id(),
                    cb_combiner.key() == nid as nat,
                    cb_combiner.value().is_Reading(),
                    !is_alive ==> cb_combiner.value().get_Reading_0().is_Range(),
                    !is_alive ==> cb_combiner.value().get_Reading_0().get_Range_cur()
                        == local_version,
                    !is_alive ==> cb_combiner.value().get_Reading_0().get_Range_end() == global_tail,
                    is_alive ==> cb_combiner.value().get_Reading_0().is_Guard(),
                    is_alive ==> cb_combiner.value().get_Reading_0().get_Guard_cur()
                        == local_version,
                    is_alive ==> cb_combiner.value().get_Reading_0().get_Guard_end() == global_tail,
                    self.slog.spec_index(phys_log_idx as int).wf(
                        phys_log_idx as nat,
                        self.cyclic_buffer_instance@,
                    ),
            {
                if iteration == WARN_THRESHOLD {
                    print_starvation_warning(line!());
                    iteration = 0;
                }
                let alive_bit =
                    atomic_with_ghost!(
                    &self.slog[phys_log_idx].alive => load();
                    returning alive_bit;
                    ghost g => {
                        if alive_bit == is_alive_value {
                            let tracked (_, Tracked(cb_combiner0)) =
                                self.cyclic_buffer_instance.borrow().reader_guard(nid as nat, &g, cb_combiner);
                            cb_combiner = cb_combiner0;
                        }
                    });
                is_alive = alive_bit == is_alive_value;
                iteration = iteration + 1;
            }

            let tracked stored_entry: &StoredType<DT>;
            proof {
                stored_entry =
                self.cyclic_buffer_instance.borrow().guard_guards(nid as nat, &cb_combiner);
            }
            let log_entry = self.slog[phys_log_idx].log_entry.borrow(
                Tracked(&stored_entry.cell_perms),
            );
            let res = actual_replica.dispatch_mut(
                DT::clone_write_op(&log_entry.as_ref().unwrap().op),
            );
            if log_entry.as_ref().unwrap().node_id == nid as u64 {
                proof {
                    if let Option::Some(e) = &stored_entry.log_entry {
                        self.unbounded_log_instance.borrow().pre_exec_dispatch_local(
                            nid as nat,
                            e,
                            &combiner,
                        );
                        let tracked local_update = local_updates.tracked_remove(
                            responses_idx as nat,
                        );
                        let tracked (
                            Tracked(ghost_replica0),
                            Tracked(local_update),
                            Tracked(combiner0),
                        ) = self.unbounded_log_instance.borrow().exec_dispatch_local(
                            nid as nat,
                            e,
                            ghost_replica,
                            local_update,
                            combiner,
                        );
                        ghost_replica = ghost_replica0;
                        local_updates.tracked_insert(responses_idx as nat, local_update);
                        combiner = combiner0;
                    } else {
                        assert(false);
                    }
                }
                responses.push(res);
                responses_idx = responses_idx + 1;
            } else {
                proof {
                    assert(stored_entry.log_entry.unwrap().value().node_id != nid);
                    if let Option::Some(e) = &stored_entry.log_entry {
                        assert(e.value().node_id != nid);
                        let tracked exec_dispatch_remote_result =
                            self.unbounded_log_instance.borrow().exec_dispatch_remote(
                            nid as nat,
                            e,
                            ghost_replica,
                            combiner,
                        );
                        ghost_replica = exec_dispatch_remote_result.0.get();
                        combiner = exec_dispatch_remote_result.1.get();
                    } else {
                        assert(false)  

                    }
                }
            }
            proof {
                cb_combiner =
                self.cyclic_buffer_instance.borrow().reader_unguard(nid as nat, cb_combiner);
            }
            local_version = local_version + 1;
        }
        proof {
            self.unbounded_log_instance.borrow().pre_exec_update_version_upper_bound(
                nid as nat,
                &combiner,
            );
        }
        atomic_with_ghost!(
            &self.version_upper_bound.0 => fetch_max(global_tail);
            ghost g => {
                combiner = self.unbounded_log_instance.borrow().exec_update_version_upper_bound(nid as nat, &mut g, combiner);

                if ghost_data.combiner@.value().is_Placed() {
                    local_updates = self.execute_update_done_multiple(request_ids_new,  local_updates, &g);
                }
            });
        atomic_with_ghost!(
            &self.local_versions[nid].0 => store(global_tail);
            ghost g => {
                let tracked (Tracked(ul_local_versions), Tracked(ul_combiner))
                    = self.unbounded_log_instance.borrow().exec_finish(nid as nat, g.0, combiner);
                let tracked (Tracked(cb_local_versions), Tracked(cb_combiner0))
                    = self.cyclic_buffer_instance.borrow().reader_finish(nid as nat, g.1, cb_combiner);

                combiner = ul_combiner;
                cb_combiner = cb_combiner0;

                g = (ul_local_versions, cb_local_versions);
        });
        let tracked ghost_data_ret = NrLogAppendExecDataGhost {
            local_updates: Tracked(local_updates),  
            ghost_replica: Tracked(ghost_replica),  
            combiner: Tracked(combiner),  
            cb_combiner: Tracked(cb_combiner),  
            request_ids: Ghost(request_ids),  
        };
        assert(ghost_data_ret.execute_post(
            ghost_data,
            replica_token@,
            actual_replica.view(),
            old(responses)@,
            responses@,
            self.unbounded_log_instance@,
            self.cyclic_buffer_instance@,
        ));
        Tracked(ghost_data_ret)
    }

    pub(crate) fn find_min_local_version(
        &self,
        cb_combiner: Tracked<CyclicBuffer::combiner<DT>>,
    ) -> (result: (u64, Tracked<CyclicBuffer::combiner<DT>>))
        requires
            self.wf(),
            cb_combiner@.instance_id() == self.cyclic_buffer_instance@.id(),
            cb_combiner@.value().is_Idle(),
        ensures
            result.0 <= MAX_IDX,
            result.1@.key() == cb_combiner@.key(),
            result.1@.value().is_AdvancingHead(),
            result.1@.instance_id() == self.cyclic_buffer_instance@.id(),
            result.1@.value().get_AdvancingHead_idx() == self.num_replicas,
            result.1@.value().get_AdvancingHead_min_local_version() == result.0,
    {
        let num_replicas = self.local_versions.len();
        let tracked mut g_cb_comb_new: CyclicBuffer::combiner<DT> = cb_combiner.get();
        let ghost g_node_id = cb_combiner@.key();
        let mut min_local_version =
            atomic_with_ghost!(
            &self.local_versions[0].0 => load();
            returning ret;
            ghost g => {
                g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                        .advance_head_start(g_node_id, &g.1, g_cb_comb_new);
            });
        let mut idx: usize = 1;
        while idx < num_replicas
            invariant
                self.wf(),
                0 <= idx <= num_replicas,
                min_local_version <= MAX_IDX,
                g_cb_comb_new.instance_id() == self.cyclic_buffer_instance@.id(),
                g_cb_comb_new.value().is_AdvancingHead(),
                g_cb_comb_new.value().get_AdvancingHead_idx() == idx,
                g_cb_comb_new.value().get_AdvancingHead_min_local_version() == min_local_version,
                g_cb_comb_new.key() == g_node_id,
                num_replicas == self.local_versions.len(),
            decreases num_replicas - idx
        {
            let cur_local_tail =
                atomic_with_ghost!(
                &self.local_versions[idx].0 => load();
                returning ret;
                ghost g => {
                    g_cb_comb_new = self.cyclic_buffer_instance.borrow()
                                            .advance_head_next(g_node_id, &g.1, g_cb_comb_new);
                });
            if cur_local_tail < min_local_version {
                min_local_version = cur_local_tail;
            }
            idx = idx + 1;
        }
        (min_local_version, Tracked(g_cb_comb_new))
    }
}

pub tracked struct NrLogAppendExecDataGhost<DT: Dispatch> {
    pub                      
     local_updates: Tracked::<Map<ReqId, UnboundedLog::local_updates<DT>>>,
    pub                      
     ghost_replica: Tracked<UnboundedLog::replicas<DT>>,
    pub                      
     combiner: Tracked<UnboundedLog::combiner<DT>>,
    pub                      
     cb_combiner: Tracked<CyclicBuffer::combiner<DT>>,
    pub                      
     request_ids: Ghost<Seq<ReqId>>,
}

impl<DT: Dispatch> NrLogAppendExecDataGhost<DT> {
    pub open spec fn common_pred(
        &self,
        nid: NodeId,
        data: DT::View,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& (forall|i| #![all_triggers]
            0 <= i < self.request_ids@.len() ==> {
                &&& (self.local_updates@.contains_key(i))
                &&& self.local_updates@[i].instance_id() == inst.id()
            })
        &&& self.ghost_replica@.key() == nid
        &&& self.ghost_replica@.instance_id() == inst.id()
        &&& self.ghost_replica@.value() == data
        &&& self.combiner@.key() == nid
        &&& self.combiner@.instance_id() == inst.id()
        &&& self.cb_combiner@.key() == nid
        &&& self.cb_combiner@.instance_id() == cb_inst.id()
        &&& self.request_ids@.len() <= MAX_REQUESTS
    }

    pub open spec fn append_pre(
        &self,
        nid: NodeId,
        data: DT::View,
        ops: Seq<DT::WriteOperation>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& (forall|i|
            #![trigger self.local_updates@[i]]
            0 <= i < self.request_ids@.len() ==> {
                &&& #[trigger] self.local_updates@.contains_key(i)
                &&& self.local_updates@[i].key() == self.request_ids@[i as int]
                &&& self.local_updates@[i].value().is_Init()
                &&& self.local_updates@[i].value().get_Init_op() == ops[i as int]
            })
        &&& self.combiner@.value().is_Ready()
        &&& self.cb_combiner@.value().is_Idle()
        &&& self.request_ids@.len() == ops.len()
    }

    pub open spec fn append_post(
        &self,
        pre: Self,
        nid: NodeId,
        data: DT::View,
        operations: Seq<DT::WriteOperation>,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.combiner@.value().is_Ready() || self.combiner@.value().is_Placed()
        &&& self.combiner@.value().is_Ready() ==> self.post_exec(pre.request_ids@, responses)
        &&& self.combiner@.value().is_Placed() ==> self.pre_exec(responses)
        &&& self.cb_combiner@.value()
            == pre.cb_combiner@.value()  

        &&& self.request_ids == pre.request_ids
    }

    pub open spec fn execute_pre(
        &self,
        nid: NodeId,
        data: DT::View,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.cb_combiner@.value().is_Idle()
        &&& self.combiner@.value().is_Ready() || self.combiner@.value().is_Placed()
        &&& self.combiner@.value().is_Placed() ==> self.pre_exec(responses)
        &&& self.combiner@.value().is_Ready() ==> {
            &&& self.request_ids@.len() == responses.len()
        }
    }

    pub open spec fn execute_post(
        &self,
        pre: Self,
        nid: NodeId,
        data: DT::View,
        responses_old: Seq<DT::Response>,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.cb_combiner@.value() == pre.cb_combiner@.value()
        &&& self.request_ids == pre.request_ids
        &&& pre.combiner@.value().is_Placed() ==> {
            &&& self.post_exec(pre.request_ids@, responses)
        }
        &&& pre.combiner@.value().is_Ready() ==> {
            &&& self.combiner@.value() == pre.combiner@.value()
            &&& self.local_updates == pre.local_updates
            &&& responses == responses_old
        }
    }

    pub open spec fn advance_head_pre(
        &self,
        nid: NodeId,
        data: DT::View,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.pre_exec(responses)
        &&& self.cb_combiner@.value().is_Idle()
        &&& self.combiner@.value().is_Placed()
    }

    pub open spec fn advance_head_post(
        &self,
        pre: Self,
        nid: NodeId,
        data: DT::View,
        responses: Seq<DT::Response>,
        inst: UnboundedLog::Instance<DT>,
        cb_inst: CyclicBuffer::Instance<DT>,
    ) -> bool {
        &&& self.common_pred(nid, data, inst, cb_inst)
        &&& self.request_ids == pre.request_ids
        &&& self.cb_combiner@.value() == pre.cb_combiner@.value()
        &&& self.combiner@.value().is_Ready() || self.combiner@.value().is_Placed()
        &&& self.combiner@.value().is_Ready() ==> {
            &&& self.post_exec(self.request_ids@, responses)
        }
        &&& self.combiner@.value().is_Placed() ==> {
            &&& responses.len() == 0
            &&& self.local_updates == pre.local_updates
            &&& self.combiner@.value() == pre.combiner@.value()
            &&& self.ghost_replica@.value() == pre.ghost_replica@.value()
        }
    }

    pub open spec fn pre_exec(&self, responses: Seq<DT::Response>) -> bool {
        &&& responses.len() == 0
        &&& self.combiner@.value().is_Placed()
        &&& self.combiner@.value().get_Placed_queued_ops() == self.request_ids
        &&& (forall|i|
            #![trigger self.local_updates@[i]]
            0 <= i < self.request_ids@.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& self.local_updates@[i].key() == self.request_ids@[i as int]
                &&& self.local_updates@[i].value().is_Placed()
            })
    }

    pub open spec fn post_exec(
        &self,
        request_ids: Seq<ReqId>,
        responses: Seq<DT::Response>,
    ) -> bool {
        &&& request_ids.len() == responses.len()
        &&& self.combiner@.value().is_Ready()
        &&& (forall|i|
            #![trigger self.local_updates@[i]]
            0 <= i < request_ids.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& self.local_updates@[i].value().is_Done()
                &&& self.local_updates@[i].value().get_Done_ret() == responses[i as int]
                &&& self.local_updates@[i].key() == request_ids[i as int]
            })
    }
}

struct_with_invariants!{
pub tracked struct AppendEntriesGhostState<DT: Dispatch> {
    pub ghost idx               : nat,
    pub ghost old_tail          : nat,
    pub tracked log_entries     : Map<nat, UnboundedLog::log<DT>>,
    pub tracked local_updates   : Map<nat, UnboundedLog::local_updates<DT>>,
    pub tracked combiner        : UnboundedLog::combiner<DT>,
    pub tracked tail            : UnboundedLog::tail<DT>,
    pub ghost request_ids       : Seq<ReqId>,
    pub ghost operations        : Seq<<DT as Dispatch>::WriteOperation>
}

pub open spec fn wf(&self, nid: nat, ridx: nat, inst: UnboundedLog::Instance<DT>) -> bool {
    predicate {
        &&& 0 <= self.idx <= self.request_ids.len()
        &&& ridx < self.request_ids.len()

        &&& self.tail.value() == self.old_tail + self.idx
        &&& self.tail.instance_id() == inst.id()

        &&& self.combiner.instance_id() == inst.id()
        &&& self.combiner.key() == nid
        &&& self.combiner.value().is_Placed()
        &&& self.combiner.value().get_Placed_queued_ops().len() == self.idx

        &&& (forall |i| 0 <= i < self.idx ==> #[trigger]self.request_ids[i] == self.combiner.value().get_Placed_queued_ops()[i])

        &&& (forall |i| 0 <= i < self.idx <==> self.log_entries.contains_key(i))
        &&& (forall |i| 0 <= i < self.request_ids.len() ==> self.local_updates.contains_key(i))

        &&& (forall |i| #![trigger self.local_updates[i]] 0 <= i < self.idx ==> {
            &&& self.local_updates[i].instance_id() == inst.id()
            &&& self.local_updates[i].key() == self.request_ids[i as int]
            &&& self.local_updates[i].value().is_Placed()
            &&& self.local_updates[i].value().get_Placed_op() == self.operations[i as int]
        })

        &&& (forall |i| #![trigger self.local_updates[i]] self.idx <= i < self.request_ids.len() ==> {
            &&& self.local_updates[i].instance_id() == inst.id()
            &&& self.local_updates[i].key() == self.request_ids[i as int]
            &&& self.local_updates[i].value().is_Init()
            &&& self.local_updates[i].value().get_Init_op() == self.operations[i as int]
        })

        &&& (forall |i| #![trigger self.log_entries[i]] 0 <= i < self.idx ==> {
            &&& self.log_entries[i].instance_id() == inst.id()
            &&& self.log_entries[i].key() == self.old_tail + i
            &&& self.log_entries[i].value().node_id == nid
            &&& self.log_entries[i].value().op == self.operations[i as int]
        })
    }
}
}  


struct_with_invariants!{
pub tracked struct NrLogTokens<DT: Dispatch> {
    pub ghost num_replicas: nat,
    pub tracked replicas                : Map<NodeId,UnboundedLog::replicas<DT>>,
    pub tracked combiners               : Map<NodeId,UnboundedLog::combiner<DT>>,
    pub tracked cb_combiners            : Map<NodeId, CyclicBuffer::combiner<DT>>,
    pub tracked unbounded_log_instance  : UnboundedLog::Instance<DT>,
    pub tracked cyclic_buffer_instance  : CyclicBuffer::Instance<DT>,
}

pub open spec fn wf(&self, num_replicas: nat) -> bool {
    predicate {
        &&& self.num_replicas == num_replicas
        &&& self.unbounded_log_instance.num_replicas() == self.num_replicas
        &&& self.cyclic_buffer_instance.num_replicas() == self.num_replicas
        &&& (forall |i| #![trigger self.replicas[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger] self.replicas.contains_key(i)
            &&& self.replicas[i].instance_id() == self.unbounded_log_instance.id()
            &&& self.replicas[i].key() == i
            &&& self.replicas[i].value() == DT::init_spec()
        })

        &&& (forall |i| #![trigger self.combiners[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger]  self.combiners.contains_key(i)
            &&& self.combiners[i].instance_id() == self.unbounded_log_instance.id()
            &&& self.combiners[i].key() == i
            &&& self.combiners[i].value().is_Ready()
        })

        &&& (forall |i| #![trigger self.cb_combiners[i]]0 <= i < self.num_replicas ==> {
            &&& #[trigger] self.cb_combiners.contains_key(i)
            &&& self.cb_combiners[i].instance_id() == self.cyclic_buffer_instance.id()
            &&& self.cb_combiners[i].key() == i
            &&& self.cb_combiners[i].value().is_Idle()
        })
    }
}

}  


} 
}
pub mod replica {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::{
    atomic_ghost::AtomicU64,
    atomic_with_ghost,
    cell::{CellId, PCell, PointsTo},
    map::Map,
    prelude::*,
};

use crate::constants::{
    MAX_REPLICAS, MAX_REQUESTS, MAX_THREADS_PER_REPLICA, RESPONSE_CHECK_INTERVAL,
};

use crate::Dispatch;

use crate::spec::cyclicbuffer::CyclicBuffer;
use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::types::{NodeId, ReqId};
use crate::spec::unbounded_log::UnboundedLog;
#[cfg(verus_keep_ghost)]
use crate::{is_readonly_stub, is_readonly_ticket, is_update_stub, is_update_ticket};

use crate::exec::context::{
    Context, FCClientRequestResponseGhost, PendingOperation, ThreadId, ThreadToken,
};
use crate::exec::log::{NrLog, NrLogAppendExecDataGhost};
use crate::exec::rwlock::RwLock;
#[cfg(verus_keep_ghost)]
use crate::exec::utils::{rids_match, rids_match_add_none, rids_match_add_rid, rids_match_pop};
use crate::exec::CachePadded;


verus! {

#[verus::trusted]
#[verifier(external_body)]             
fn spin_loop_hint() {
    core::hint::spin_loop();
}

pub type ReplicaId = usize;

pub struct ReplicaToken {
    pub                       
     rid: ReplicaId,
}

impl ReplicaToken {
    pub const fn new(rid: ReplicaId) -> (res: ReplicaToken)
        ensures
            res@ == rid,
    {
        ReplicaToken { rid }
    }

    pub const fn clone(&self) -> (res: Self)
        ensures
            res == self,
    {
        ReplicaToken { rid: self.rid }
    }

    pub open spec fn wf(&self, max_replicas: nat) -> bool {
        &&& self.rid < max_replicas
    }

    pub const fn id(&self) -> (result: ReplicaId)
        ensures
            result as nat == self.id_spec(),
    {
        self.rid
    }

    pub open spec fn id_spec(&self) -> nat {
        self.rid as nat
    }

    pub open spec fn view(&self) -> nat {
        self.rid as nat
    }
}

struct_with_invariants!{
pub struct ReplicatedDataStructure<DT: Dispatch> {
    pub data: DT,
    pub replica: Tracked<UnboundedLog::replicas<DT>>,
    pub combiner: Tracked<UnboundedLog::combiner<DT>>,
    pub cb_combiner: Tracked<CyclicBuffer::combiner<DT>>
}

pub open spec fn wf(&self, nid: NodeId, inst: UnboundedLog::Instance<DT>, cb: CyclicBuffer::Instance<DT>) -> bool {
    predicate {
        &&& self.combiner@.instance_id() == inst.id()
        &&& self.replica@.instance_id() == inst.id()

        &&& self.replica@.value() == self.data.view()
        &&& self.replica@.key() == nid
        &&& self.combiner@.value().is_Ready()
        &&& self.combiner@.key() == nid
        &&& self.cb_combiner@.key() == nid
        &&& self.cb_combiner@.value().is_Idle()
        &&& self.cb_combiner@.instance_id() == cb.id()
    }
}}  


struct_with_invariants!{
#[repr(align(128))]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(DT))]
pub struct Replica<DT: Dispatch> {
    pub replica_token: ReplicaToken,

    pub combiner: CachePadded<AtomicU64<_, Option<CombinerLockStateGhost<DT>>, _>>,

    pub contexts: Vec<Context<DT>>,

    pub collected_operations: PCell<Vec<<DT as Dispatch>::WriteOperation>>,

    pub collected_operations_per_thread: PCell<Vec<usize>>,

    pub responses: PCell<Vec<<DT as Dispatch>::Response>>,

    pub data: CachePadded<RwLock<ReplicatedDataStructure<DT>>>,

    pub num_threads: u64, 

    pub                       thread_tokens: Vec<ThreadToken<DT>>,

    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
    pub flat_combiner_instance: Tracked<FlatCombiner::Instance>,
}

pub open spec fn wf(&self) -> bool {

    predicate {
        &&& (forall |i: int| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i]).wf(i as nat))
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).flat_combiner_instance == self.flat_combiner_instance)
        &&& (forall |i: nat| 0 <= i < self.contexts.len() ==> (#[trigger] self.contexts[i as int]).unbounded_log_instance == self.unbounded_log_instance)

        &&& self.replica_token.rid < self.unbounded_log_instance@.num_replicas()

        &&& self.contexts.len() == MAX_THREADS_PER_REPLICA
        &&& self.data.0.max_threads() == self.contexts.len()
        &&& 0 <= self.spec_id() < MAX_REPLICAS
        &&& self.data.0.wf()
        &&& (forall |v: ReplicatedDataStructure<DT>| (#[trigger] self.data.0.inv(v)) == v.wf(self.spec_id(), self.unbounded_log_instance@, self.cyclic_buffer_instance@))

        &&& self.flat_combiner_instance@.num_threads() == MAX_THREADS_PER_REPLICA
        &&& (forall |i| #![trigger self.thread_tokens[i]] 0 <= i < self.thread_tokens.len() ==> {
            self.thread_tokens[i].wf(self)
        })
    }

    invariant on combiner with (flat_combiner_instance, responses, collected_operations, collected_operations_per_thread) specifically (self.combiner.0) is (v: u64, g: Option<CombinerLockStateGhost<DT>>) {
        &&& (v == 0) <==> g.is_some()
        &&& (g matches Some(g) ==> g.inv(flat_combiner_instance@, responses.id(), collected_operations.id(), collected_operations_per_thread.id()))
    }

}

}  


impl<DT: Dispatch> Replica<DT> {
    pub fn new(
        replica_token: ReplicaToken,
        num_threads: usize,
        config: Tracked<ReplicaConfig<DT>>,
    ) -> (res: Self)
        requires
            num_threads == MAX_THREADS_PER_REPLICA,
            replica_token.id_spec() < MAX_REPLICAS,
            config@.wf(replica_token.id_spec()),
        ensures
            res.wf(),
            res.spec_id() == replica_token.id_spec(),
            res.unbounded_log_instance@ == config@.unbounded_log_instance,
            res.cyclic_buffer_instance@ == config@.cyclic_buffer_instance,
    {
        let tracked ReplicaConfig {
            replica: replica,
            combiner: combiner,
            cb_combiner: cb_combiner,
            unbounded_log_instance: unbounded_log_instance,
            cyclic_buffer_instance: cyclic_buffer_instance,
        } = config.get();
        let tracked fc_instance: FlatCombiner::Instance;
        let tracked mut fc_clients: Map<nat, FlatCombiner::clients>;
        let tracked mut fc_slots: Map<nat, FlatCombiner::slots>;
        let tracked fc_combiner: FlatCombiner::combiner;
        proof {
            let tracked (
                Tracked(fc_instance0),  
                Tracked(fc_clients0),  
                Tracked(fc_slots0),  
                Tracked(fc_combiner0),  
            ) = FlatCombiner::Instance::initialize(num_threads as nat);
            fc_instance = fc_instance0;
            fc_clients = fc_clients0.into_map();
            fc_slots = fc_slots0.into_map();
            fc_combiner = fc_combiner0;
        }
        let (responses, responses_token) = PCell::new(Vec::with_capacity(num_threads));
        let (collected_operations, collected_operations_perm) = PCell::new(
            Vec::with_capacity(num_threads),
        );
        let (collected_operations_per_thread, collected_operations_per_thread_perm) = PCell::new(
            Vec::with_capacity(num_threads),
        );
        let replicated_data_structure = ReplicatedDataStructure {
            data: DT::init(),
            replica: Tracked(replica),
            combiner: Tracked(combiner),
            cb_combiner: Tracked(cb_combiner),
        };
        assert(replicated_data_structure.wf(
            replica_token.id_spec(),
            unbounded_log_instance,
            cyclic_buffer_instance,
        ));
        let ghost data_structure_inv = |s: ReplicatedDataStructure<DT>|
            { s.wf(replica_token.id_spec(), unbounded_log_instance, cyclic_buffer_instance) };
        let data = CachePadded(
            RwLock::new(
                MAX_THREADS_PER_REPLICA,
                replicated_data_structure,
                Ghost(data_structure_inv),
            ),
        );
        let mut contexts: Vec<Context<DT>> = Vec::with_capacity(num_threads);
        let mut thread_tokens: Vec<ThreadToken<DT>> = Vec::with_capacity(num_threads);
        let mut idx = 0;
        while idx < num_threads
            invariant
                num_threads <= MAX_THREADS_PER_REPLICA,
                replica_token.id_spec() < unbounded_log_instance.num_replicas(),
                contexts.len() == idx,
                thread_tokens.len() == idx,
                0 <= idx <= num_threads,
                forall|i: nat| idx <= i < num_threads ==> fc_slots.contains_key(i),
                forall|i: nat|
                    #![trigger fc_slots[i]]
                    idx <= i < num_threads ==> {
                        &&& fc_slots[i].value().is_Empty()
                        &&& fc_slots[i].key() == i
                        &&& fc_slots[i].instance_id() == fc_instance.id()
                    },
                forall|i: nat| idx <= i < num_threads ==> fc_clients.contains_key(i),
                forall|i: nat|
                    #![trigger fc_clients[i]]
                    idx <= i < num_threads ==> {
                        &&& fc_clients[i].instance_id() == fc_instance.id()
                        &&& fc_clients[i].key() == i
                        &&& fc_clients[i].value().is_Idle()
                    },
                forall|i: nat| idx <= i < num_threads ==> fc_slots.contains_key(i),
                forall|i|
                    #![trigger contexts[i]]
                    0 <= i < contexts.len() ==> {
                        &&& contexts[i].wf(i as nat)
                        &&& contexts[i].flat_combiner_instance == fc_instance
                        &&& contexts[i].unbounded_log_instance == unbounded_log_instance
                    },
                forall|i|
                    #![trigger thread_tokens[i]]
                    0 <= i < thread_tokens.len() ==> {
                        &&& thread_tokens[i].wf2(unbounded_log_instance.num_replicas())
                        &&& thread_tokens[i].thread_id_spec() == i
                        &&& thread_tokens[i].rid@ == replica_token.id_spec()
                        &&& thread_tokens[i].fc_client@.instance_id() == fc_instance.id()
                        &&& thread_tokens[i].batch_perm@@.pcell == contexts[i].batch.0.id()
                    },
            decreases num_threads - idx
        {
            let tracked slot;
            let tracked client;
            proof {
                slot = fc_slots.tracked_remove(idx as nat);
                client = fc_clients.tracked_remove(idx as nat);
            }
            let fc_inst = Tracked(fc_instance.clone());
            let ul_inst = Tracked(unbounded_log_instance.clone());
            let (context, batch_perm) = Context::new(idx, Tracked(slot), fc_inst, ul_inst);
            let token = ThreadToken {
                rid: replica_token.clone(),
                tid: idx as u32,
                fc_client: Tracked(client),
                batch_perm,
            };
            contexts.push(context);
            thread_tokens.push(token);
            idx = idx + 1;
        }
        let tracked context_ghost = CombinerLockStateGhost {
            flat_combiner: Tracked(fc_combiner),
            collected_operations_perm,
            collected_operations_per_thread_perm,
            responses_token,
        };
        let tracked fc_inst = fc_instance.clone();
        let combiner = CachePadded(
            AtomicU64::new(
                Ghost(
                    (
                        Tracked(fc_inst),
                        responses,
                        collected_operations,
                        collected_operations_per_thread,
                    ),
                ),
                0,
                Tracked(Option::Some(context_ghost)),
            ),
        );
        let num_threads = 0;  
        Replica {
            replica_token,
            combiner,
            contexts,
            collected_operations,
            collected_operations_per_thread,
            responses,
            data,
            thread_tokens,
            num_threads,
            unbounded_log_instance: Tracked(unbounded_log_instance),
            cyclic_buffer_instance: Tracked(cyclic_buffer_instance),
            flat_combiner_instance: Tracked(fc_instance),
        }
    }

    pub fn id(&self) -> (res: ReplicaId)
        ensures
            res as nat == self.spec_id(),
    {
        self.replica_token.id()
    }

    pub open spec fn spec_id(&self) -> NodeId {
        self.replica_token.id_spec()
    }

    #[inline(always)]
    fn acquire_combiner_lock(&self) -> (result: (bool, Tracked<Option<CombinerLockStateGhost<DT>>>))
        requires
            self.wf(),
        ensures
            result.0 ==> result.1@.is_some(),
            result.0 ==> result.1@.unwrap().inv(
                self.flat_combiner_instance@,
                self.responses.id(),
                self.collected_operations.id(),
                self.collected_operations_per_thread.id(),
            ),
    {
        let res =
            atomic_with_ghost!(
                &self.combiner.0 => load();
                ghost g => { }
            );
        if res != 0 {
            return (false, Tracked(Option::None));
        }

        let tid = 1u64;
        let tracked lock_g: Option<CombinerLockStateGhost<DT>>;
        let res =
            atomic_with_ghost!(
            &self.combiner.0 => compare_exchange(0, tid + 1);
            update prev->next;
            ghost g => {
                if prev == 0 {
                    lock_g = g;    
                    g = Option::None;       
                } else {
                    lock_g = Option::None; 
                }
            }
        );
        if let Result::Ok(val) = res {
            (val == 0, Tracked(lock_g))
        } else {
            (false, Tracked(Option::None))
        }
    }

    #[inline(always)]
    fn release_combiner_lock(&self, lock_state: Tracked<CombinerLockStateGhost<DT>>)
        requires
            self.wf(),
            lock_state@.inv(
                self.flat_combiner_instance@,
                self.responses.id(),
                self.collected_operations.id(),
                self.collected_operations_per_thread.id(),
            ),
    {
        atomic_with_ghost!(
            &self.combiner.0 => store(0);
            update old_val -> new_val;
            ghost g
            => {
                g = Option::Some(lock_state.get());
            });
    }

    fn try_combine(&self, slog: &NrLog<DT>)
        requires
            self.wf(),
            slog.wf(),
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
    {
        let (acquired, combiner_lock) = self.acquire_combiner_lock();
        if acquired {
            assert(combiner_lock@.is_some());
            let combiner_lock = Tracked(combiner_lock.get().tracked_unwrap());
            let combiner_lock = self.combine(slog, combiner_lock);
            self.release_combiner_lock(combiner_lock);
        } else {
        }
    }

    fn combine(
        &self,
        slog: &NrLog<DT>,
        combiner_lock: Tracked<CombinerLockStateGhost<DT>>,
    ) -> (result: Tracked<CombinerLockStateGhost<DT>>)
        requires
            self.wf(),
            slog.wf(),
            slog.unbounded_log_instance@ == self.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
            combiner_lock@.inv(
                self.flat_combiner_instance@,
                self.responses.id(),
                self.collected_operations.id(),
                self.collected_operations_per_thread.id(),
            ),
        ensures
            result@.inv(
                self.flat_combiner_instance@,
                self.responses.id(),
                self.collected_operations.id(),
                self.collected_operations_per_thread.id(),
            ),
    {
        let tracked combiner_lock = combiner_lock.get();
        let flat_combiner = Tracked(combiner_lock.flat_combiner.get());
        let tracked mut collected_operations_perm = combiner_lock.collected_operations_perm.get();
        let tracked mut collected_operations_per_thread_perm =
            combiner_lock.collected_operations_per_thread_perm.get();
        let tracked mut responses_token = combiner_lock.responses_token.get();
        let mut responses = self.responses.take(Tracked(&mut responses_token));
        let mut operations = self.collected_operations.take(
            Tracked(&mut collected_operations_perm),
        );
        let mut num_ops_per_thread = self.collected_operations_per_thread.take(
            Tracked(&mut collected_operations_per_thread_perm),
        );
        let Tracked(collect_res) = self.collect_thread_ops(
            &mut operations,
            &mut num_ops_per_thread,
            flat_combiner,
        );
        let tracked ThreadOpsData { flat_combiner, local_updates, request_ids, cell_permissions } =
            collect_res;
        let (replicated_data_structure, write_handle) = self.data.0.acquire_write();
        let mut data = replicated_data_structure.data;
        let ghost_replica = replicated_data_structure.replica;
        let combiner = replicated_data_structure.combiner;
        let cb_combiner = replicated_data_structure.cb_combiner;
        let tracked append_exec_ghost_data = NrLogAppendExecDataGhost {
            local_updates,
            ghost_replica,
            combiner,
            cb_combiner,
            request_ids,
        };
        let append_exec_ghost_data = slog.append(
            &self.replica_token,
            &operations,
            &mut responses,
            &mut data,
            Tracked(append_exec_ghost_data),
        );
        let append_exec_ghost_data = slog.execute(
            &self.replica_token,
            &mut responses,
            &mut data,
            append_exec_ghost_data,
        );
        let Tracked(append_exec_ghost_data) = append_exec_ghost_data;
        let tracked NrLogAppendExecDataGhost {
            local_updates,
            ghost_replica,
            combiner,
            cb_combiner,
            request_ids,
        } = append_exec_ghost_data;
        let tracked ghost_replica = ghost_replica.get();
        let tracked combiner = combiner.get();
        let tracked cb_combiner = cb_combiner.get();
        let replicated_data_structure = ReplicatedDataStructure {
            data,
            replica: Tracked(ghost_replica),
            combiner: Tracked(combiner),
            cb_combiner: Tracked(cb_combiner),
        };
        self.data.0.release_write(replicated_data_structure, write_handle);
        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner,
            request_ids,
            local_updates,
            cell_permissions,
        };
        let distribute_thread_resps_result = self.distribute_thread_resps(
            &mut responses,
            &mut num_ops_per_thread,
            Tracked(thread_ops_data),
        );
        let tracked ThreadOpsData { flat_combiner, request_ids, local_updates, cell_permissions } =
            distribute_thread_resps_result.get();
        responses.clear();
        operations.clear();
        num_ops_per_thread.clear();
        self.responses.put(Tracked(&mut responses_token), responses);
        self.collected_operations.put(Tracked(&mut collected_operations_perm), operations);
        self.collected_operations_per_thread.put(
            Tracked(&mut collected_operations_per_thread_perm),
            num_ops_per_thread,
        );
        let tracked combiner_lock = CombinerLockStateGhost {
            flat_combiner,
            collected_operations_perm: Tracked(collected_operations_perm),
            collected_operations_per_thread_perm: Tracked(collected_operations_per_thread_perm),
            responses_token: Tracked(responses_token),
        };
        Tracked(combiner_lock)
    }

    #[inline(always)]
    fn collect_thread_ops(
        &self,
        operations: &mut Vec<DT::WriteOperation>,
        num_ops_per_thread: &mut Vec<usize>,
        flat_combiner: Tracked<FlatCombiner::combiner>,
    ) -> (response: Tracked<ThreadOpsData<DT>>)
        requires
            self.wf(),
            old(num_ops_per_thread).len() == 0,
            old(operations).len() == 0,
            flat_combiner@.instance_id() == self.flat_combiner_instance@.id(),
            flat_combiner@.value().is_Collecting(),
            flat_combiner@.value().get_Collecting_0().len() == 0,
        ensures
            final(operations).len() <= MAX_REQUESTS,
            response@.collect_thread_ops_post(
                self.flat_combiner_instance,
                self.unbounded_log_instance@,
                final(num_ops_per_thread)@,
                final(operations)@,
                self.contexts@,
            ),
    {
        let mut flat_combiner = flat_combiner;
        let tracked mut updates: Map<nat, UnboundedLog::local_updates<DT>> = Map::tracked_empty();
        let tracked mut cell_permissions: Map<nat, PointsTo<PendingOperation<DT>>> =
            Map::tracked_empty();
        let ghost mut request_ids = Seq::empty();
        let num_registered_threads = MAX_THREADS_PER_REPLICA;
        let mut thread_idx = 0;
        while thread_idx < num_registered_threads
            invariant
                0 <= thread_idx <= num_registered_threads,
                self.wf(),
                operations.len() <= thread_idx,
                operations.len() == request_ids.len(),
                num_ops_per_thread.len() == thread_idx,
                self.contexts.len() == num_registered_threads,
                self.flat_combiner_instance@.num_threads() == num_registered_threads,
                flat_combiner@.value().is_Collecting(),
                flat_combiner@.value().get_Collecting_0().len() == thread_idx,
                flat_combiner@.instance_id() == self.flat_combiner_instance@.id(),
                forall|i: nat|
                    i < flat_combiner@.value().get_Collecting_0().len() ==> (
                    num_ops_per_thread[i as int] > 0) == (
                    #[trigger] flat_combiner@.value().get_Collecting_0()[i as int]).is_some(),
                forall|i: nat|
                    i < flat_combiner@.value().get_Collecting_0().len() && (
                    #[trigger] flat_combiner@.value().get_Collecting_0()[i as int]).is_some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i].mem_contents().is_init()
                    },
                forall|i| 0 <= i < request_ids.len() <==> updates.contains_key(i),
                forall|i: nat|
                    #![trigger updates[i]]
                    i < request_ids.len() ==> {
                        &&& #[trigger] updates.contains_key(i)
                        &&& updates[i].instance_id() == self.unbounded_log_instance@.id()
                        &&& updates[i].key() == request_ids[i as int]
                        &&& updates[i].value().is_Init()
                        &&& updates[i].value().get_Init_op() == operations[i as int]
                    },
                rids_match(
                    flat_combiner@.value().get_Collecting_0(),
                    request_ids,
                    0,
                    flat_combiner@.value().get_Collecting_0().len(),
                    0,
                    request_ids.len(),
                ),
            decreases num_registered_threads - thread_idx
        {
            let tracked update_req: std::option::Option<UnboundedLog::local_updates<DT>>;
            let tracked batch_perms: std::option::Option<PointsTo<PendingOperation<DT>>>;
            let num_ops =
                atomic_with_ghost!(
                &self.contexts[thread_idx].atomic.0 => load();
                returning num_ops;
                ghost g 
            => {
                if num_ops == 1 {
                    self.flat_combiner_instance.borrow().pre_combiner_collect_request(&g.slots, flat_combiner.borrow());

                    rids_match_add_rid(flat_combiner.view().value().get_Collecting_0(), request_ids,
                        0, flat_combiner.view().value().get_Collecting_0().len(), 0, request_ids.len(),g.update.unwrap().key());

                    update_req = g.update;
                    batch_perms = g.batch_perms;

                    g.slots = self.flat_combiner_instance.borrow().combiner_collect_request(g.slots, flat_combiner.borrow_mut());
                    g.update = None;
                    g.batch_perms = None;
                } else {
                    rids_match_add_none(flat_combiner.view().value().get_Collecting_0(), request_ids,
                        0, flat_combiner.view().value().get_Collecting_0().len(), 0, request_ids.len());

                    self.flat_combiner_instance.borrow().combiner_collect_empty(&g.slots, flat_combiner.borrow_mut());
                    update_req = None;
                    batch_perms = None;
                }
            });
            if num_ops == 1 {
                let tracked batch_token_value = batch_perms.tracked_unwrap();
                let op = DT::clone_write_op(
                    &self.contexts[thread_idx].batch.0.borrow(Tracked(&batch_token_value)).op,
                );
                let tracked update_req = update_req.tracked_unwrap();
                proof {
                    updates.tracked_insert(request_ids.len() as nat, update_req);
                    cell_permissions.tracked_insert(thread_idx as nat, batch_token_value);
                }
                proof {
                    request_ids = request_ids.push(update_req.key());
                }
                operations.push(op);
            }

            num_ops_per_thread.push(num_ops as usize);
            thread_idx = thread_idx + 1;
        }
        proof {
            self.flat_combiner_instance.borrow().combiner_responding_start(
                flat_combiner.borrow_mut(),
            );
        }
        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner,
            request_ids: Ghost(request_ids),
            local_updates: Tracked(updates),
            cell_permissions: Tracked(cell_permissions),
        };
        Tracked(thread_ops_data)
    }

    fn distribute_thread_resps(
        &self,
        responses: &mut Vec<DT::Response>,
        num_ops_per_thread: &mut Vec<usize>,
        thread_ops_data: Tracked<ThreadOpsData<DT>>,
    ) -> (res: Tracked<ThreadOpsData<DT>>)
        requires
            self.wf(),
            thread_ops_data@.distribute_thread_resps_pre(
                self.flat_combiner_instance,
                self.unbounded_log_instance@,
                old(num_ops_per_thread)@,
                old(responses)@,
                self.contexts@,
            ),
            rids_match(
                thread_ops_data@.flat_combiner@.value().get_Responding_0(),
                thread_ops_data@.request_ids@,
                0,
                thread_ops_data@.flat_combiner@.value().get_Responding_0().len(),
                0,
                thread_ops_data@.request_ids@.len(),
            ),
        ensures
            res@.distribute_thread_resps_post(self.flat_combiner_instance),
    {
        let tracked ThreadOpsData {
            flat_combiner: flat_combiner,
            request_ids: request_ids,
            local_updates: local_updates,
            cell_permissions: cell_permissions,
        } = thread_ops_data.get();
        let tracked mut flat_combiner = flat_combiner.get();
        let tracked mut cell_permissions = cell_permissions.get();
        let tracked mut updates = local_updates.get();
        let num_registered_threads = MAX_THREADS_PER_REPLICA;
        let mut thread_idx = 0;
        let mut resp_idx: usize = 0;
        while thread_idx < num_registered_threads
            invariant
                0 <= thread_idx <= num_registered_threads,
                0 <= resp_idx <= responses.len(),
                resp_idx <= thread_idx,
                num_ops_per_thread.len() == num_registered_threads,
                request_ids@.len() == responses.len(),
                num_registered_threads == MAX_THREADS_PER_REPLICA,
                self.wf(),
                self.flat_combiner_instance@.num_threads() == num_registered_threads,
                flat_combiner.instance_id() == self.flat_combiner_instance@.id(),
                flat_combiner.value().is_Responding(),
                flat_combiner.value().get_Responding_1() == thread_idx,
                flat_combiner.value().get_Responding_0().len() == MAX_THREADS_PER_REPLICA,
                forall|i: nat|
                    i < flat_combiner.value().get_Responding_0().len() ==> (
                    num_ops_per_thread[i as int] > 0) == (
                    #[trigger] flat_combiner.value().get_Responding_0()[i as int]).is_some(),
                forall|i: nat|
                    thread_idx <= i < flat_combiner.value().get_Responding_0().len() && (
                    #[trigger] flat_combiner.value().get_Responding_0()[i as int]).is_some() ==> {
                        &&& cell_permissions.contains_key(i)
                        &&& cell_permissions[i]@.pcell === self.contexts@[i as int].batch.0.id()
                        &&& cell_permissions[i].mem_contents().is_init()
                    },
                forall|i: nat|
                    resp_idx <= i < request_ids@.len() ==> {
                        &&& updates.contains_key(i)
                    },
                forall|i: nat|
                    #![trigger updates[i]]
                    resp_idx <= i < request_ids@.len() ==> {
                        &&& updates.contains_key(i)
                        &&& updates[i].key() == request_ids@[i as int]
                        &&& updates[i].value().is_Done()
                        &&& updates[i].instance_id() == self.unbounded_log_instance@.id()
                        &&& updates[i].value().get_Done_ret() == responses[i as int]
                    },
                rids_match(
                    flat_combiner.value().get_Responding_0(),
                    request_ids@,
                    thread_idx as nat,
                    flat_combiner.value().get_Responding_0().len(),
                    resp_idx as nat,
                    request_ids@.len(),
                ),
            decreases num_registered_threads - thread_idx
        {
            proof {
                rids_match_pop(
                    flat_combiner.value().get_Responding_0(),
                    request_ids@,
                    thread_idx as nat,
                    flat_combiner.value().get_Responding_0().len(),
                    resp_idx as nat,
                    request_ids@.len(),
                );
            }
            let num_ops = num_ops_per_thread[thread_idx];
            if num_ops == 0 {
                proof {
                    self.flat_combiner_instance.borrow().combiner_responding_empty(
                        &mut flat_combiner,
                    );
                }
            } else {
                let tracked mut permission = cell_permissions.tracked_remove(thread_idx as nat);
                let mut op_resp = self.contexts[thread_idx].batch.0.take(Tracked(&mut permission));
                let resp: DT::Response = DT::clone_response(&responses[resp_idx]);
                op_resp.resp = Some(resp);
                self.contexts[thread_idx].batch.0.put(Tracked(&mut permission), op_resp);
                atomic_with_ghost!(
                    &self.contexts[thread_idx].atomic.0 => store(0);
                    update prev -> next;
                    ghost g 
                    => {
                        g.slots = self.flat_combiner_instance.borrow().combiner_responding_result(g.slots, &mut flat_combiner);
                        g.batch_perms = Some(permission);
                        g.update = Some(updates.tracked_remove(resp_idx as nat));
                    }
                );
                resp_idx = resp_idx + 1;
            }
            thread_idx = thread_idx + 1;
        }
        proof {
            self.flat_combiner_instance.borrow().combiner_responding_done(&mut flat_combiner);
        }
        let tracked thread_ops_data = ThreadOpsData {
            flat_combiner: Tracked(flat_combiner),
            request_ids,
            local_updates: Tracked(updates),
            cell_permissions: Tracked(cell_permissions),
        };
        Tracked(thread_ops_data)
    }

    pub fn register(&mut self) -> (res: Option<ThreadToken<DT>>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).replica_token@ == final(self).replica_token@,
            old(self).unbounded_log_instance@ == final(self).unbounded_log_instance@,
            old(self).cyclic_buffer_instance@ == final(self).cyclic_buffer_instance@,
            res matches Some(res) ==> res.wf(final(self)),
    {
        self.thread_tokens.pop()
    }

    #[verifier(external_body)]             
    pub fn progress(line: u32) {
        println!("Replica:: progress {line}");
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn execute(
        &self,
        slog: &NrLog<DT>,
        op: DT::ReadOperation,
        tkn: ThreadToken<DT>,
        ticket: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (result: (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>))
        requires
            self.wf(),
            slog.wf(),
            tkn.wf(self),
            tkn.batch_perm@@.pcell == self.contexts[tkn.thread_id_spec() as int].batch.0.id(),
            self.replica_token@ == tkn.replica_token()@,
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@,
            is_readonly_ticket(ticket@, op, slog.unbounded_log_instance@),
        ensures
            result.1.wf(&self),
            result.1.batch_perm@@.pcell
                == self.contexts[result.1.thread_id_spec() as int].batch.0.id(),
            is_readonly_stub(result.2@, ticket@.key(), result.0, slog.unbounded_log_instance@),
    {
        let ghost rid: nat = ticket@.key();
        let ghost nid = tkn.replica_id_spec();
        let (version_upper_bound, ticket) = slog.get_version_upper_bound(ticket);
        let (mut is_synced, mut ticket) = slog.is_replica_synced_for_reads(
            self.id(),
            version_upper_bound,
            ticket,
        );
        while !is_synced
            invariant
                self.wf(),
                slog.wf(),
                !is_synced ==> ticket@.value().is_VersionUpperBound(),
                !is_synced ==> ticket@.value().get_VersionUpperBound_version_upper_bound()
                    == version_upper_bound,
                !is_synced ==> ticket@.value().get_VersionUpperBound_op() == op,
                is_synced ==> ticket@.value().is_ReadyToRead(),
                is_synced ==> ticket@.value().get_ReadyToRead_node_id() == self.spec_id(),
                is_synced ==> ticket@.value().get_ReadyToRead_op() == op,
                ticket@.instance_id() == self.unbounded_log_instance@.id(),
                ticket@.key() == rid,
                slog.unbounded_log_instance@ == self.unbounded_log_instance@,
                slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
        {
            self.try_combine(slog);
            spin_loop_hint();
            let res = slog.is_replica_synced_for_reads(self.id(), version_upper_bound, ticket);
            is_synced = res.0;
            ticket = res.1;
        }
        let tracked ticket = ticket.get();
        assert(tkn.thread_id_spec() < self.data.0.max_threads());
        let read_handle = self.data.0.acquire_read(tkn.thread_id() as usize);
        let replica = self.data.0.borrow(Tracked(&read_handle));
        let result = replica.data.dispatch(op);
        let tracked ticket = self.unbounded_log_instance.borrow().readonly_apply(
            rid,
            replica.replica.borrow(),
            ticket,
            replica.combiner.borrow(),
        );
        self.data.0.release_read(read_handle);
        (result, tkn, Tracked(ticket))
    }

    pub fn execute_mut(
        &self,
        slog: &NrLog<DT>,
        op: DT::WriteOperation,
        tkn: ThreadToken<DT>,
        ticket: Tracked<UnboundedLog::local_updates<DT>>,
    ) -> (result: (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>))
        requires
            slog.wf(),
            self.wf(),
            tkn.wf(self),
            tkn.batch_perm@@.pcell == self.contexts[tkn.thread_id_spec() as int].batch.0.id(),
            self.replica_token == tkn.replica_token(),
            self.unbounded_log_instance@ == slog.unbounded_log_instance@,
            self.cyclic_buffer_instance@ == slog.cyclic_buffer_instance@,
            is_update_ticket(ticket@, op, slog.unbounded_log_instance@),
        ensures
            result.1.wf(self),
            result.1.batch_perm@@.pcell
                == self.contexts[result.1.thread_id_spec() as int].batch.0.id(),
            is_update_stub(result.2@, ticket@.key(), result.0, slog.unbounded_log_instance@),
    {
        let tracked ticket = ticket.get();
        let ghost req_id: nat = ticket.key();
        let ThreadToken { rid, tid, fc_client, batch_perm } = tkn;
        let tracked context_ghost = FCClientRequestResponseGhost {
            batch_perms: Some(batch_perm.get()),
            cell_id: Ghost(self.contexts[tkn.thread_id_spec() as int].batch.0.id()),
            local_updates: Some(ticket),
            fc_clients: fc_client.get(),
        };
        let mk_pending_res = self.make_pending(op, tid, Tracked(context_ghost));
        let context_ghost = mk_pending_res.1;
        self.try_combine(slog);
        let response = self.get_response(slog, tid, Ghost(req_id), context_ghost);
        let context_ghost = response.1;
        let tracked FCClientRequestResponseGhost {
            batch_perms: batch_perms,
            cell_id,
            local_updates: ticket,
            fc_clients: fc_clients,
        } = context_ghost.get();
        let tracked ticket = ticket.tracked_unwrap();
        let tracked batch_perm = batch_perms.tracked_unwrap();
        (
            response.0,
            ThreadToken {
                rid,
                tid,
                fc_client: Tracked(fc_clients),
                batch_perm: Tracked(batch_perm),
            },
            Tracked(ticket),
        )
    }

    #[inline(always)]
    fn make_pending(
        &self,
        op: DT::WriteOperation,
        tid: ThreadId,
        context_ghost: Tracked<FCClientRequestResponseGhost<DT>>,
    ) -> (res: (bool, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            self.wf(),
            0 <= tid < self.contexts.len(),
            context_ghost@.enqueue_op_pre(
                tid as nat,
                op,
                self.contexts[tid as int].batch.0.id(),
                self.flat_combiner_instance@,
                self.unbounded_log_instance@,
            ),
        ensures
            res.1@.enqueue_op_post(context_ghost@),
    {
        let context = &self.contexts[tid as usize];
        context.enqueue_op(op, context_ghost)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn get_response(
        &self,
        slog: &NrLog<DT>,
        tid: ThreadId,
        req_id: Ghost<ReqId>,
        context_ghost: Tracked<FCClientRequestResponseGhost<DT>>,
    ) -> (res: (DT::Response, Tracked<FCClientRequestResponseGhost<DT>>))
        requires
            self.wf(),
            slog.wf(),
            slog.unbounded_log_instance@ == self.unbounded_log_instance@,
            slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
            0 <= tid < self.contexts.len(),
            context_ghost@.dequeue_resp_pre(
                self.contexts[tid as int].batch.0.id(),
                tid as nat,
                self.flat_combiner_instance@,
            ),
        ensures
            res.1@.dequeue_resp_post(context_ghost@, Some(res.0), self.unbounded_log_instance@),
    {
        let mut context_ghost_new = context_ghost;
        let context = &self.contexts[tid as usize];
        let mut iter: usize = 0;
        let mut r = None;
        while r.is_none()
            invariant
                slog.wf(),
                self.wf(),
                slog.unbounded_log_instance@ == self.unbounded_log_instance@,
                slog.cyclic_buffer_instance@ == self.cyclic_buffer_instance@,
                context.wf(tid as nat),
                context.flat_combiner_instance@ == self.flat_combiner_instance@,
                context.unbounded_log_instance@ == self.unbounded_log_instance@,
                0 <= iter <= RESPONSE_CHECK_INTERVAL,
                r.is_none() ==> context_ghost_new@.dequeue_resp_pre(
                    context.batch.0.id(),
                    tid as nat,
                    self.flat_combiner_instance@,
                ),
                context_ghost_new@.dequeue_resp_post(
                    context_ghost@,
                    r,
                    self.unbounded_log_instance@,
                ),
        {
            if iter == RESPONSE_CHECK_INTERVAL {
                self.try_combine(slog);
                iter = 0;
            }
            let deq_resp_result = context.dequeue_response(context_ghost_new);
            r = deq_resp_result.0;
            context_ghost_new = deq_resp_result.1;
            iter = iter + 1;
        }
        let r = r.unwrap();
        (r, context_ghost_new)
    }
}

pub tracked struct ReplicaConfig<DT: Dispatch> {
    pub tracked replica: UnboundedLog::replicas<DT>,
    pub tracked combiner: UnboundedLog::combiner<DT>,
    pub tracked cb_combiner: CyclicBuffer::combiner<DT>,
    pub tracked unbounded_log_instance: UnboundedLog::Instance<DT>,
    pub tracked cyclic_buffer_instance: CyclicBuffer::Instance<DT>,
}

impl<DT: Dispatch> ReplicaConfig<DT> {
    pub open spec fn wf(&self, nid: nat) -> bool {
        &&& self.combiner.instance_id() == self.unbounded_log_instance.id()
        &&& self.cb_combiner.instance_id() == self.cyclic_buffer_instance.id()
        &&& self.cyclic_buffer_instance.unbounded_log_instance() == self.unbounded_log_instance
        &&& self.unbounded_log_instance.num_replicas() == self.cyclic_buffer_instance.num_replicas()
        &&& nid < self.unbounded_log_instance.num_replicas()
        &&& self.replica.value() == DT::init_spec()
        &&& self.replica.key() == nid
        &&& self.replica.instance_id() == self.unbounded_log_instance.id()
        &&& self.combiner.value().is_Ready()
        &&& self.combiner.key() == nid
        &&& self.cb_combiner.key() == nid
        &&& self.cb_combiner.value().is_Idle()
        &&& self.cb_combiner.instance_id() == self.cyclic_buffer_instance.id()
    }
}

struct_with_invariants!{
pub tracked struct CombinerLockStateGhost<DT: Dispatch> {
    pub flat_combiner: Tracked<FlatCombiner::combiner>,

    pub collected_operations_perm: Tracked<PointsTo<Vec<<DT as Dispatch>::WriteOperation>>>,

    pub collected_operations_per_thread_perm: Tracked<PointsTo<Vec<usize>>>,

    pub responses_token: Tracked<PointsTo<Vec<<DT as Dispatch>::Response>>>,
}

pub open spec fn inv(&self, combiner_instance: FlatCombiner::Instance, responses_id: CellId, op_buffer_id: CellId, thread_ops: CellId) -> bool {
    predicate {
        &&& self.flat_combiner@.value().is_Collecting()
        &&& self.flat_combiner@.value().get_Collecting_0().len() == 0
        &&& self.flat_combiner@.instance_id() == combiner_instance.id()

        &&& self.collected_operations_perm@.mem_contents().is_init()
        &&& self.collected_operations_perm@@.pcell == op_buffer_id
        &&& self.collected_operations_perm@.mem_contents().value().len() == 0 

        &&& self.responses_token@.mem_contents().is_init()
        &&& self.responses_token@@.pcell == responses_id
        &&& self.responses_token@.mem_contents().value().len() == 0 

        &&& self.collected_operations_per_thread_perm@.mem_contents().is_init()
        &&& self.collected_operations_per_thread_perm@@.pcell == thread_ops
        &&& self.collected_operations_per_thread_perm@.mem_contents().value().len() == 0
    }
}}  


tracked struct ThreadOpsData<DT: Dispatch> {
    flat_combiner: Tracked<FlatCombiner::combiner>,
    request_ids: Ghost<Seq<ReqId>>,
    local_updates: Tracked<Map<nat, UnboundedLog::local_updates<DT>>>,
    cell_permissions: Tracked<Map<nat, PointsTo<PendingOperation<DT>>>>,
}

impl<DT: Dispatch> ThreadOpsData<DT> {
    spec fn shared_inv(
        &self,
        flat_combiner_instance: Tracked<FlatCombiner::Instance>,
        num_ops_per_thread: Seq<usize>,
        replica_contexts: Seq<Context<DT>>,
    ) -> bool {
        &&& self.flat_combiner@.instance_id() == flat_combiner_instance@.id()
        &&& self.flat_combiner@.value().is_Responding()
        &&& self.flat_combiner@.value().get_Responding_0().len() as nat
            == MAX_THREADS_PER_REPLICA as nat
        &&& num_ops_per_thread.len() as nat == MAX_THREADS_PER_REPLICA as nat
        &&& self.flat_combiner@.value().get_Responding_1() == 0
        &&& (forall|i: nat|
            #![trigger num_ops_per_thread[i as int]]
            #![trigger self.flat_combiner@.value().get_Responding_0()[i as int]]
            i < self.flat_combiner@.value().get_Responding_0().len() ==> {
                &&& (num_ops_per_thread[i as int] > 0)
                    == self.flat_combiner@.value().get_Responding_0()[i as int].is_some()
                &&& self.flat_combiner@.value().get_Responding_0()[i as int].is_some() ==> {
                    &&& self.cell_permissions@.contains_key(i)
                    &&& self.cell_permissions@[i]@.pcell === replica_contexts[i as int].batch.0.id()
                    &&& self.cell_permissions@[i].mem_contents().is_init()
                }
            })
    }

    spec fn distribute_thread_resps_pre(
        &self,
        flat_combiner_instance: Tracked<FlatCombiner::Instance>,
        unbounded_log_instance: UnboundedLog::Instance<DT>,
        num_ops_per_thread: Seq<usize>,
        responses: Seq<DT::Response>,
        replica_contexts: Seq<Context<DT>>,
    ) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)
        &&& self.request_ids@.len() == responses.len()
        &&& (forall|i| 0 <= i < self.request_ids@.len() ==> self.local_updates@.contains_key(i))
        &&& (forall|i: nat|
            #![trigger self.local_updates@[i]]
            i < self.request_ids@.len() ==> {
                &&& self.local_updates@.contains_key(i)
                &&& self.local_updates@[i].instance_id() == unbounded_log_instance.id()
                &&& self.local_updates@[i].key() == self.request_ids@[i as int]
                &&& self.local_updates@[i].value().is_Done()
                &&& self.local_updates@[i].value().get_Done_ret() == responses[i as int]
            })
        &&& rids_match(
            self.flat_combiner@.value().get_Responding_0(),
            self.request_ids@,
            0,
            self.flat_combiner@.value().get_Responding_0().len(),
            0,
            self.request_ids@.len(),
        )
    }

    spec fn distribute_thread_resps_post(
        &self,
        flat_combiner_instance: Tracked<FlatCombiner::Instance>,
    ) -> bool {
        &&& self.flat_combiner@.instance_id() == flat_combiner_instance@.id()
        &&& self.flat_combiner@.value().is_Collecting()
        &&& self.flat_combiner@.value().get_Collecting_0().len() == 0
    }

    spec fn collect_thread_ops_post(
        &self,
        flat_combiner_instance: Tracked<FlatCombiner::Instance>,
        unbounded_log_instance: UnboundedLog::Instance<DT>,
        num_ops_per_thread: Seq<usize>,
        operations: Seq<DT::WriteOperation>,
        replica_contexts: Seq<Context<DT>>,
    ) -> bool {
        &&& self.shared_inv(flat_combiner_instance, num_ops_per_thread, replica_contexts)
        &&& self.request_ids@.len() == operations.len()
        &&& (forall|i| 0 <= i < self.request_ids@.len() <==> self.local_updates@.contains_key(i))
        &&& (forall|i: nat|
            #![trigger self.local_updates@[i]]
            i < self.request_ids@.len() ==> {
                &&& #[trigger] self.local_updates@.contains_key(i)
                &&& self.local_updates@[i].instance_id() == unbounded_log_instance.id()
                &&& self.local_updates@[i].key() == self.request_ids@[i as int]
                &&& self.local_updates@[i].value().is_Init()
                &&& self.local_updates@[i].value().get_Init_op() == operations[i as int]
            })
        &&& rids_match(
            self.flat_combiner@.value().get_Responding_0(),
            self.request_ids@,
            0,
            self.flat_combiner@.value().get_Responding_0().len(),
            0,
            self.request_ids@.len(),
        )
    }
}

} 
}
pub mod rwlock {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::{
    atomic_ghost::{AtomicBool, AtomicU64},
    atomic_with_ghost,
    cell::{PCell, PointsTo},
    prelude::*,
};

use crate::exec::CachePadded;
use crate::spec::rwlock::RwLockSpec;

verus! {

#[verifier::reject_recursive_types(T)]
pub tracked struct RwLockWriteGuard<T> {
    handle: Tracked<RwLockSpec::exc_guard<PointsTo<T>>>,
    cell_perms: Tracked<PointsTo<T>>,
}

#[verifier::reject_recursive_types(T)]
pub struct RwLockReadGuard<T> {
    tid: usize,
    perms: Ghost<PointsTo<T>>,
    handle: Tracked<RwLockSpec::shared_guard<PointsTo<T>>>,
}

impl<T> RwLockReadGuard<T> {
    pub closed spec fn view(&self) -> T {
        self.handle@.element().1.mem_contents().value()
    }
}

pub const MAX_RC: u64 = 0xffff_ffff_ffff_fff0;

#[verus::trusted]
#[verifier(external_body)]             
pub fn warn_with_ref_count_too_big() {
    panic!("WARNING: Refcount value exceeds the maximum value of u64.");
}

struct_with_invariants!{
    #[verifier::reject_recursive_types(T)]
    pub struct RwLock<T> {
        data: PCell<T>,
        exc_locked: CachePadded<AtomicBool<_, RwLockSpec::exc_locked<PointsTo<T>>, _>>,
        ref_counts: Vec<CachePadded<AtomicU64<_, RwLockSpec::ref_counts<PointsTo<T>>, _>>>,
        inst: Tracked<RwLockSpec::Instance<PointsTo<T>>>,
        user_inv: Ghost<ISet<T>>,
    }

    pub closed spec fn wf(&self) -> bool {

        predicate {
            &&& self.inst@.rc_width() == self.ref_counts@.len()

            &&& forall |i: int| #![trigger self.ref_counts@.index(i)] (0 <= i && i < self.ref_counts@.len()) ==>
                self.ref_counts@.index(i).0.well_formed()
                && self.ref_counts@.index(i).0.constant() === (self.inst, i)

            &&& forall |v: PointsTo<T>| #[trigger] self.inst@.user_inv().contains(v) == (
                equal(v@.pcell, self.data.id()) && v.mem_contents().is_init()
                        && self.user_inv@.contains(v.mem_contents().value())
            )
        }

        invariant on exc_locked with (inst) specifically (self.exc_locked.0) is (b: bool, g: RwLockSpec::exc_locked<PointsTo<T>>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == b
        }

        invariant on ref_counts with (inst)
            forall |i: int| where (0 <= i < self.ref_counts@.len()) specifically (self.ref_counts@[i].0)
            is (v: u64, g: RwLockSpec::ref_counts<PointsTo<T>>)
        {
            &&& g.instance_id() == inst@.id()
            &&& g.key() == i
            &&& g.value() == v as int
            &&& g.value() <= MAX_RC
        }
    }
}

impl<T> RwLock<T> {
    pub closed spec fn inv(&self, t: T) -> bool {
        self.user_inv@.contains(t)
    }

    pub open spec fn thread_id_valid(&self, t: nat) -> bool {
        0 <= t && t < self.max_threads()
    }

    pub closed spec fn max_threads(&self) -> nat {
        self.ref_counts@.len()
    }

    pub closed spec fn wf_read_handle(&self, read_handle: &RwLockReadGuard<T>) -> bool {
        &&& self.thread_id_valid(read_handle.tid as nat)
        &&& read_handle.handle@.instance_id() == self.inst@.id()
        &&& read_handle.handle@.element() == (read_handle.tid as int, read_handle.perms@)
        &&& read_handle.perms@@.pcell == self.data.id()
        &&& read_handle.perms@.mem_contents().is_init()
    }

    pub closed spec fn wf_write_handle(&self, write_handle: &RwLockWriteGuard<T>) -> bool {
        &&& write_handle.handle@.instance_id() == self.inst@.id()
        &&& write_handle.cell_perms@@.pcell == self.data.id()
        &&& write_handle.cell_perms@.mem_contents().is_uninit()
    }

    #[verifier(spinoff_prover)]
    pub fn new(rc_width: usize, t: T, inv: Ghost<spec_fn(T) -> bool>) -> (s: Self)
        requires
            0 < rc_width && inv@(t),
        ensures
            s.wf() && s.max_threads() == rc_width,
            forall|v: T| s.inv(v) == inv@(v),
    {
        let tracked inst;
        let tracked exc_locked_token;
        let tracked mut ref_counts_tokens;
        let (pcell_data, Tracked(mut pcell_token)) = PCell::new(t);
        let ghost set_inv = ISet::new(inv@);
        let ghost user_inv = ISet::new(
            |s: PointsTo<T>|
                {
                    &&& equal(s@.pcell, pcell_data.id())
                    &&& s.mem_contents().is_init()
                    &&& set_inv.contains(s.mem_contents().value())
                },
        );
        proof {
            let tracked (
                Tracked(inst0),
                Tracked(exc_locked_token0),
                Tracked(ref_counts_tokens0),
                _,
                _,
                _,
                _,
            ) = RwLockSpec::Instance::initialize(
                rc_width as int,
                pcell_token,
                user_inv,
                Option::Some(pcell_token),
            );
            inst = inst0;
            exc_locked_token = exc_locked_token0;
            ref_counts_tokens = ref_counts_tokens0.into_map();
        }
        let tracked_inst: Tracked<RwLockSpec::Instance<PointsTo<T>>> = Tracked(inst.clone());
        let exc_locked_atomic = AtomicBool::new(
            Ghost(tracked_inst),
            false,
            Tracked(exc_locked_token),
        );
        let mut v: Vec<
            CachePadded<
                AtomicU64<
                    (Tracked<RwLockSpec::Instance<PointsTo<T>>>, int),
                    RwLockSpec::ref_counts<PointsTo<T>>,
                    _,
                >,
            >,
        > = Vec::new();
        let mut i: usize = 0;
        assert forall|j: int|
            i <= j && j < rc_width implies #[trigger] ref_counts_tokens.dom().contains(j) && equal(
            ref_counts_tokens.index(j).instance_id(),
            inst.id(),
        ) && equal(ref_counts_tokens.index(j).key(), j) && equal(
            ref_counts_tokens.index(j).value(),
            0,
        ) by {
            assert(ref_counts_tokens.dom().contains(j));
            assert(equal(ref_counts_tokens.index(j).instance_id(), inst.id()));
            assert(equal(ref_counts_tokens.index(j).key(), j));
            assert(equal(ref_counts_tokens.index(j).value(), 0));
        }
        assert(forall|j: int|
            #![trigger( ref_counts_tokens.dom().contains(j) )]
            #![trigger( ref_counts_tokens.index(j) )]
            i <= j && j < rc_width ==> (ref_counts_tokens.dom().contains(j) && equal(
                ref_counts_tokens.index(j).instance_id(),
                inst.id(),
            ) && equal(ref_counts_tokens.index(j).key(), j) && equal(
                ref_counts_tokens.index(j).value(),
                0,
            )));
        while i < rc_width
            invariant
                i <= rc_width,
                v@.len() == i as int,
                forall|j: int|
                    #![trigger v@.index(j)]
                    0 <= j && j < i ==> v@.index(j).0.well_formed() && equal(
                        v@.index(j).0.constant(),
                        (tracked_inst, j),
                    ),
                tracked_inst@ == inst,
                forall|j: int|
                    #![trigger( ref_counts_tokens.dom().contains(j) )]
                    #![trigger( ref_counts_tokens.index(j) )]
                    i <= j && j < rc_width ==> (ref_counts_tokens.dom().contains(j) && equal(
                        ref_counts_tokens.index(j).instance_id(),
                        inst.id(),
                    ) && equal(ref_counts_tokens.index(j).key(), j) && equal(
                        ref_counts_tokens.index(j).value(),
                        0,
                    )),
            decreases rc_width - i
        {
            assert(ref_counts_tokens.dom().contains(i as int));
            let tracked ref_count_token = ref_counts_tokens.tracked_remove(i as int);
            let rc_atomic = AtomicU64::new(
                Ghost((tracked_inst, i as int)),
                0,
                Tracked(ref_count_token),
            );
            v.push(CachePadded(rc_atomic));
            i = i + 1;
            assert forall|j: int|
                i <= j && j < rc_width implies #[trigger] ref_counts_tokens.dom().contains(j)
                && equal(ref_counts_tokens.index(j).instance_id(), inst.id()) && equal(
                ref_counts_tokens.index(j).key(),
                j,
            ) && equal(ref_counts_tokens.index(j).value(), 0) by {
                assert(ref_counts_tokens.dom().contains(j));
                assert(equal(ref_counts_tokens.index(j).instance_id(), inst.id()));
                assert(equal(ref_counts_tokens.index(j).key(), j));
                assert(equal(ref_counts_tokens.index(j).value(), 0));
            }
        }
        let s = RwLock {
            user_inv: Ghost(set_inv),
            data: pcell_data,
            inst: Tracked(inst),
            exc_locked: CachePadded(exc_locked_atomic),
            ref_counts: v,
        };
        assert(s.inst@.rc_width() == s.ref_counts@.len());
        s
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_write(&self) -> (res: (T, Tracked<RwLockWriteGuard<T>>))
        requires
            self.wf(),
        ensures
            self.wf() && self.wf_write_handle(&res.1@) && self.inv(res.0),
    {
        let tracked mut token: Option<RwLockSpec::exc_pending<PointsTo<T>>> = None;
        let mut acquired = false;
        while !acquired
            invariant
                self.wf(),
                acquired ==> (token matches Some(token) && token.instance_id() == self.inst@.id()
                    && token.value() == 0),
        {
            let result =
                atomic_with_ghost!(
                &self.exc_locked.0 => compare_exchange(false, true);
                returning res;
                ghost g =>
            {
                if res.is_ok() {
                    token = Option::Some(self.inst.borrow().exc_start(&mut g));
                }
            });
            acquired = result.is_ok();
        }
        let tracked mut token = token.tracked_unwrap();
        let mut idx = 0;
        while idx < self.ref_counts.len()
            invariant
                self.wf(),
                idx <= self.ref_counts.len(),
                token.instance_id() == self.inst@.id(),
                token.value() == idx,
        {
            let mut taken = true;
            while taken
                invariant
                    self.wf(),
                    idx < self.ref_counts.len(),
                    token.instance_id() == self.inst@.id(),
                    taken ==> token.value() == idx,
                    !taken ==> token.value() == idx + 1,
            {
                let result =
                    atomic_with_ghost!(
                    &self.ref_counts[idx].0 => load();
                    returning res;
                    ghost g => {
                        if res == 0 {
                            token = self.inst.borrow().exc_check_count(&g, token);
                        }
                });
                taken = result != 0;
            }
            idx = idx + 1;
        }

        let tracked (_, Tracked(cell_perms), handle) = self.inst.borrow().exc_finish(token);
        let t = self.data.take(Tracked(&mut cell_perms));
        (t, Tracked(RwLockWriteGuard { handle, cell_perms: Tracked(cell_perms) }))
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_read<'a>(&'a self, tid: usize) -> (res: RwLockReadGuard<T>)
        requires
            self.wf() && self.thread_id_valid(tid as nat),
        ensures
            self.wf() && self.wf_read_handle(&res) && self.inv(res@),
    {
        loop
            invariant
                self.wf() && tid < self.ref_counts.len(),
        {
            let rc =
                atomic_with_ghost!(
                &self.ref_counts[tid].0 => load();
                returning rc;
                ghost g => { }
            );
            if rc == MAX_RC {
                warn_with_ref_count_too_big();
                #[allow(while_true)]
                while true {
                }  

            }

            let tracked mut shared_pending: Option<RwLockSpec::shared_pending<PointsTo<T>>>;
            let res =
                atomic_with_ghost!(
                &self.ref_counts[tid].0 => compare_exchange(rc, rc+1);
                update prev->next;
                ghost g =>
            {
                if prev == rc {
                    assert(rc < MAX_RC);
                    let tracked (_ref_counts, _shared_pending) = self.inst.borrow().shared_start(tid as int, g);
                    shared_pending = Some(_shared_pending.get());
                    g = _ref_counts.get();

                } else {
                    shared_pending = None;
                }


            });
            if res.is_err() {
                continue ;
            }

            let ghost mut perms: PointsTo<T>;
            let tracked shared_guard: Option<RwLockSpec::shared_guard<PointsTo<T>>>;
            let is_exc_locked =
                atomic_with_ghost!(
                &self.exc_locked.0 => load();
                returning res;
                ghost g => {
                    if !res {
                        let tracked (_perms, _shared_guard) = self.inst.borrow().shared_finish(tid as int, &g, shared_pending.tracked_unwrap());
                        perms = _perms@.unwrap();
                        shared_guard = Some(_shared_guard.get());
                        shared_pending = None;
                    } else {
                        shared_guard = None;
                    }
            });
            let perms = Ghost(perms);
            if is_exc_locked {
                let res =
                    atomic_with_ghost!(
                    &self.ref_counts[tid].0 => fetch_sub(1);
                    ghost g => {
                    let tracked shared_pending = shared_pending.tracked_unwrap();
                    self.inst.borrow().rc_not_zero_guard(tid as int, &g, &shared_pending);
                    g = self.inst.borrow().shared_abandon(tid as int, g, shared_pending);
                });
            } else {
                return RwLockReadGuard {
                    tid,
                    perms,
                    handle: Tracked(shared_guard.tracked_unwrap()),
                };
            }
        }
    }

    pub fn borrow<'a>(&'a self, read_handle: Tracked<&'a RwLockReadGuard<T>>) -> (res: &'a T)
        requires
            self.wf() && self.wf_read_handle(&read_handle@),
        ensures
            res == read_handle@@,
    {
        let ghost val = (read_handle@.tid as int, read_handle@.perms@);
        let tracked handle = read_handle.borrow().handle.borrow();
        let tracked perm = self.inst.borrow().do_guard(val, &handle);
        self.data.borrow(Tracked(&perm))
    }

    pub fn release_write(&self, val: T, write_handle: Tracked<RwLockWriteGuard<T>>)
        requires
            self.wf() && self.inv(val) && self.wf_write_handle(&write_handle@),
        ensures
            self.wf(),
    {
        let tracked RwLockWriteGuard { cell_perms, handle } = write_handle.get();
        let tracked mut cell_perms = cell_perms.get();
        self.data.put(Tracked(&mut cell_perms), val);
        let res =
            atomic_with_ghost!(
            &self.exc_locked.0 => store(false);
            ghost g => {
            let tracked exc_guard = handle.get();
            self.inst.borrow().exc_release(cell_perms, cell_perms, &mut g, exc_guard);
        });
    }

    pub fn release_read(&self, read_handle: RwLockReadGuard<T>)
        requires
            self.wf() && self.wf_read_handle(&read_handle),
        ensures
            self.wf(),
    {
        let RwLockReadGuard { tid, perms, handle } = read_handle;
        let res =
            atomic_with_ghost!(
            &self.ref_counts[tid].0 => fetch_sub(1);
            ghost g => {
                let val = (tid as int, perms@);
                g = self.inst.borrow().shared_release(val, g, handle.get());
        });
    }
}

} 
}
pub mod utils {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::{prelude::*, seq::Seq};

use crate::spec::types::ReqId;

verus! {

pub open spec fn rids_match(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
) -> bool
    decreases bools_end - bools_start,
    when 0 <= bools_start <= bools_end <= bools.len() && 0 <= rids_start <= rids_end <= rids.len()
{
    if bools_end == bools_start {
        rids_end == rids_start
    } else {
        if let Some(end) = bools[bools_end - 1] {
            &&& rids_end > rids_start
            &&& rids[rids_end - 1] == end
            &&& rids_match(
                bools,
                rids,
                bools_start,
                (bools_end - 1) as nat,
                rids_start,
                (rids_end - 1) as nat,
            )
        } else {
            rids_match(bools, rids, bools_start, (bools_end - 1) as nat, rids_start, rids_end)
        }
    }
}

#[verifier::external_body]
pub proof fn rids_match_add_none(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end),
    ensures
        rids_match(bools.push(Option::None), rids, bools_start, bools_end, rids_start, rids_end),
    decreases bools_end - bools_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn rids_match_add_rid(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
    rid: ReqId,
)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end),
    ensures
        rids_match(
            bools.push(Option::Some(rid)),
            rids.push(rid),
            bools_start,
            bools_end,
            rids_start,
            rids_end,
        ),
    decreases bools_end - bools_start,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn rids_match_pop(
    bools: Seq<Option<ReqId>>,
    rids: Seq<ReqId>,
    bools_start: nat,
    bools_end: nat,
    rids_start: nat,
    rids_end: nat,
)
    requires
        0 <= bools_start <= bools_end <= bools.len(),
        0 <= rids_start <= rids_end <= rids.len(),
        rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end),
    ensures
        bools_end == bools_start ==> {
            rids_match(bools, rids, bools_start, bools_end, rids_start, rids_end)
        },
        bools_end > bools_start ==> {
            &&& bools[bools_start as int] matches Some(start) ==> {
                &&& rids_start < rids_end
                &&& rids[rids_start as int] == start
                &&& rids_match(
                    bools,
                    rids,
                    (bools_start + 1) as nat,
                    bools_end,
                    (rids_start + 1) as nat,
                    rids_end,
                )
            }
            &&& bools[bools_start as int].is_none() ==> {
                &&& rids_match(
                    bools,
                    rids,
                    (bools_start + 1) as nat,
                    bools_end,
                    rids_start,
                    rids_end,
                )
            }
        },
    decreases bools_end - bools_start,
{
    unimplemented!()
}

} 
}

verus! {

#[verus::trusted]
#[repr(align(128))]
pub struct CachePadded<T>(pub T);

#[verifier::reject_recursive_types(DT)]
pub struct NodeReplicated<DT: Dispatch> {
    pub                       
     log: NrLog<DT>,
    pub                      
     replicas: Vec<Box<Replica<DT>>>,
    pub unbounded_log_instance: Tracked<UnboundedLog::Instance<DT>>,
    pub cyclic_buffer_instance: Tracked<CyclicBuffer::Instance<DT>>,
}

impl<DT: Dispatch> crate::ThreadTokenT<DT, Replica<DT>> for ThreadToken<DT> {
    open spec fn wf(&self, replica: &Replica<DT>) -> bool {
        ThreadToken::<DT>::wf(self, replica)
    }

    open spec fn replica_id_spec(&self) -> nat {
        ThreadToken::<DT>::replica_id_spec(self)
    }
}

impl<DT: Dispatch + Sync> crate::NodeReplicatedT<DT> for NodeReplicated<DT> {
    type Replica = Replica<DT>;

    type ReplicaId = ReplicaId;

    type TT = ThreadToken<DT>;

    open spec fn wf(&self) -> bool {
        &&& self.log.wf()
        &&& self.unbounded_log_instance@ == self.log.unbounded_log_instance@
        &&& self.cyclic_buffer_instance@
            == self.log.cyclic_buffer_instance@

        &&& self.replicas.len()
            <= MAX_REPLICAS

        &&& (forall|i|
            0 <= i < self.replicas.len() ==> {
                &&& (#[trigger] self.replicas[i]).wf()
                &&& self.replicas[i].spec_id() == i
                &&& self.replicas[i].replica_token@ == i
                &&& self.replicas[i].unbounded_log_instance@ == self.unbounded_log_instance@
                &&& self.replicas[i].cyclic_buffer_instance@ == self.cyclic_buffer_instance@
            })
    }

    open spec fn replicas(&self) -> Vec<Box<Self::Replica>> {
        self.replicas
    }

    open spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT> {
        self.log.unbounded_log_instance@
    }

    fn new(num_replicas: usize, chg_mem_affinity: AffinityFn) -> (res:
        Self)
    {
        chg_mem_affinity.call(0);
        let (log, replica_tokens, nr_log_tokens) = NrLog::new(num_replicas, LOG_SIZE);
        let tracked NrLogTokens {
            num_replicas: _,
            replicas: mut replicas,
            combiners: mut combiners,
            cb_combiners: mut cb_combiners,
            unbounded_log_instance: unbounded_log_instance,
            cyclic_buffer_instance: cyclic_buffer_instance,
        } = nr_log_tokens.get();
        let mut actual_replicas: Vec<Box<Replica<DT>>> = Vec::new();
        let mut thread_tokens: Vec<Vec<ThreadToken<DT>>> = Vec::new();
        let mut idx = 0;
        while idx < num_replicas
            invariant
                num_replicas <= MAX_REPLICAS,
                unbounded_log_instance.num_replicas() == num_replicas,
                cyclic_buffer_instance.num_replicas() == num_replicas,
                cyclic_buffer_instance.unbounded_log_instance() == unbounded_log_instance,
                0 <= idx <= num_replicas,
                replica_tokens.len() == num_replicas,
                forall|i| 0 <= i < num_replicas ==> (#[trigger] replica_tokens[i]).id_spec() == i,
                actual_replicas.len() == idx,
                forall|i|
                    #![trigger actual_replicas[i]]
                    0 <= i < idx ==> {
                        &&& actual_replicas[i as int].wf()
                        &&& actual_replicas[i as int].spec_id() == i
                        &&& actual_replicas[i as int].unbounded_log_instance@
                            == unbounded_log_instance
                        &&& actual_replicas[i as int].cyclic_buffer_instance@
                            == cyclic_buffer_instance
                    },
                (forall|i|
                    #![trigger replicas[i]]
                    idx <= i < num_replicas ==> {
                        &&& #[trigger] replicas.contains_key(i)
                        &&& replicas[i].instance_id() == unbounded_log_instance.id()
                        &&& replicas[i].key() == i
                        &&& replicas[i].value() == DT::init_spec()
                    }),
                (forall|i|
                    #![trigger combiners[i]]
                    idx <= i < num_replicas ==> {
                        &&& #[trigger] combiners.contains_key(i)
                        &&& combiners[i].instance_id() == unbounded_log_instance.id()
                        &&& combiners[i].key() == i
                        &&& combiners[i].value().is_Ready()
                    }),
                (forall|i|
                    #![trigger cb_combiners[i]]
                    idx <= i < num_replicas ==> {
                        &&& #[trigger] cb_combiners.contains_key(i)
                        &&& cb_combiners[i].instance_id() == cyclic_buffer_instance.id()
                        &&& cb_combiners[i].key() == i
                        &&& cb_combiners[i].value().is_Idle()
                    }),
            decreases num_replicas - idx
        {
            let ghost mut idx_ghost;
            proof { idx_ghost = idx as nat }
            ;
            let replica_token = replica_tokens[idx].clone();
            let tracked config = ReplicaConfig {
                replica: replicas.tracked_remove(idx_ghost),
                combiner: combiners.tracked_remove(idx_ghost),
                cb_combiner: cb_combiners.tracked_remove(idx_ghost),
                unbounded_log_instance: unbounded_log_instance.clone(),
                cyclic_buffer_instance: cyclic_buffer_instance.clone(),
            };
            chg_mem_affinity.call(replica_token.id());
            let replica = Replica::new(replica_token, MAX_THREADS_PER_REPLICA, Tracked(config));
            actual_replicas.push(Box::new(replica));
            idx = idx + 1;
        }

        chg_mem_affinity.call(0);
        let unbounded_log_instance = Tracked(unbounded_log_instance);
        let cyclic_buffer_instance = Tracked(cyclic_buffer_instance);
        NodeReplicated {
            log,
            replicas: actual_replicas,
            unbounded_log_instance,
            cyclic_buffer_instance,
        }
    }

    fn register(&mut self, replica_id: ReplicaId) -> (result: Option<
        ThreadToken<DT>,
    >)
    {
        if (replica_id as usize) < self.replicas.len() {
            let mut replica: Box<Replica<DT>> = self.replicas.remove(replica_id);
            let res: Option<ThreadToken<DT>> = (*replica).register();
            self.replicas.insert(replica_id, replica);
            res
        } else {
            Option::None
        }
    }

    fn execute_mut(
        &self,
        op: DT::WriteOperation,
        tkn: ThreadToken<DT>,
        ticket: Tracked<UnboundedLog::local_updates<DT>>,
    ) -> (result: Result<
        (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>),
        (ThreadToken<DT>, Tracked<UnboundedLog::local_updates<DT>>),
    >)
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            Ok((&self.replicas[replica_id]).execute_mut(&self.log, op, tkn, ticket))
        } else {
            Err((tkn, ticket))
        }
    }

    fn execute(
        &self,
        op: DT::ReadOperation,
        tkn: ThreadToken<DT>,
        ticket: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (result: Result<
        (DT::Response, ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>),
        (ThreadToken<DT>, Tracked<UnboundedLog::local_reads<DT>>),
    >)
    {
        let replica_id = tkn.replica_id() as usize;
        if replica_id < self.replicas.len() {
            Ok((&self.replicas[replica_id]).execute(&self.log, op, tkn, ticket))
        } else {
            Err((tkn, ticket))
        }
    }
}

} 
}
mod spec {
pub mod types {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use crate::Dispatch;

verus! {

pub use crate::{NodeId, LogIdx, ReqId, ThreadId};

pub tracked struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
}

pub struct ConcreteLogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: u64,
}

} 
}
pub mod utils {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::prelude::*;
use vstd::set::Set;

verus! {

pub open spec fn seq_unique<A>(
    seq: Seq<A>,
) -> bool
 {
    forall|i: int, j: int|
        (0 <= i < seq.len() && 0 <= j < seq.len() && i != j) ==> seq.index(i as int) !== seq.index(
            j as int,
        )
}

pub open spec fn seq_disjoint<A>(s: Seq<A>, t: Seq<A>) -> bool {
    forall|i, j| 0 <= i < s.len() && 0 <= j < t.len() ==> s.index(i) !== t.index(j)
}

spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len(),
    when seq.len() >= 0
    via seq_to_set_rec_decreases::<A>
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

#[via_fn]
proof fn seq_to_set_rec_decreases<A>(seq: Seq<A>) {
    if seq.len() == 0 {
    } else {
        assert(seq.drop_last().len() < seq.len());  
    }
}

#[verifier::external_body]
proof fn seq_to_set_rec_is_finite<A>(seq: Seq<A>)
    ensures
        seq_to_set_rec(seq).finite(),
    decreases seq.len(),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures
        forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a),
    decreases seq.len(),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures
        seq_to_set(seq) == seq_to_set_rec(seq),
{
    unimplemented!()
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
    decreases dom,
{
    unimplemented!()
}

pub open spec fn map_contains_value<K, V>(
    map: Map<K, V>,
    val: V,
) -> bool
 {
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
    unimplemented!()
}

} 
}

pub mod linearization {
#[allow(unused_imports)]
use verus_builtin::*;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::spec::simple_log::{compute_nrstate_at_version, ReadReq, SimpleLog, UpdateResp};
use crate::Dispatch;
#[cfg(verus_keep_ghost)]
use crate::{
    behavior_equiv, AsyncLabel, AsynchronousSingleton, AsynchronousSingletonBehavior,
    InputOperation, OutputOperation, SimpleLogBehavior, SimpleLogRefinesAsynchronousSingleton,
};
use crate::{LogIdx, ReqId};

verus! {

#[cfg(verus_keep_ghost)]
type SState<DT> = SimpleLog::State<DT>;

#[cfg(verus_keep_ghost)]
type AState<DT> = AsynchronousSingleton::State<DT>;

#[cfg(verus_keep_ghost)]
pub tracked struct RefinementProof;

#[cfg(verus_keep_ghost)]
impl<DT: Dispatch> SimpleLogRefinesAsynchronousSingleton<DT> for RefinementProof {
    #[verifier::external_body]
    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<
        DT,
    >)
    {
        unimplemented!()
    }
}

#[verifier::external_body]
proof fn exists_equiv_behavior_rec<DT: Dispatch>(
    a: SimpleLogBehavior<DT>,
    r_points: Map<ReqId, LogIdx>,
) -> (b: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf() && future_points_ok(a.get_last(), r_points),
    ensures
        b.wf() && behavior_equiv(a, b) && state_refinement_relation(
            a.get_last(),
            b.get_last(),
            r_points,
        ),
    decreases a, 0nat, 0nat,
{
    unimplemented!()
}

spec fn future_rid_ok<DT: Dispatch>(s: SState<DT>, rid: ReqId, version: LogIdx) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid] is Init ==> s.version <= version
    &&& s.readonly_reqs[rid] is Req ==> s.readonly_reqs[rid]->version <= version
}

spec fn future_points_ok<DT: Dispatch>(s: SState<DT>, r_points: Map<ReqId, LogIdx>) -> bool {
    &&& r_points.dom().finite()
    &&& (forall|rid| #[trigger] r_points.contains_key(rid) ==> future_rid_ok(s, rid, r_points[rid]))
}

spec fn readonly_requests_valid<DT: Dispatch>(
    s: SState<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
) -> bool {
    &&& (forall|rid|
        (#[trigger] s.readonly_reqs.contains_key(rid) && #[trigger] t.reqs.contains_key(rid))
            ==> readonly_request_is_valid(s, t, r_points, rid))
    &&& (forall|rid|
        (#[trigger] s.readonly_reqs.contains_key(rid) && #[trigger] t.resps.contains_key(rid))
            ==> readonly_response_is_valid(s, t, r_points, rid))
}

spec fn readonly_request_is_valid<DT: Dispatch>(
    s: SState<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& (s.readonly_reqs[rid] is Req ==> s.readonly_reqs[rid]->version <= s.version)
    &&& t.reqs.contains_key(rid)
    &&& t.reqs[rid] == InputOperation::<DT>::Read(s.readonly_reqs[rid].op())
    &&& (r_points.contains_key(rid) ==> {
        &&& s.version <= r_points[rid]
        &&& (s.readonly_reqs[rid] is Req ==> s.version < r_points[rid])
    })
}

spec fn readonly_response_is_valid<DT: Dispatch>(
    s: SState<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid] is Req
    &&& s.readonly_reqs[rid]->version <= s.version
    &&& t.resps.contains_key(rid)
    &&& (r_points.contains_key(rid) ==> {
        &&& s.readonly_reqs[rid]->version <= r_points[rid] && r_points[rid] <= s.version
        &&& 0 <= r_points[rid] && r_points[rid] <= s.log.len()
        &&& t.resps[rid] == OutputOperation::<DT>::Read(
            DT::dispatch_spec(s.nrstate_at_version(r_points[rid]), s.readonly_reqs[rid].op()),
        )
    })
}

spec fn update_response_is_valid<DT: Dispatch>(
    s: SState<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
) -> bool {
    &&& s.update_resps.contains_key(rid)
    &&& s.update_resps[rid].0 < s.log.len()
    &&& t.resps.contains_key(rid)
    &&& t.resps[rid] == OutputOperation::<DT>::Write(
        DT::dispatch_mut_spec(
            s.nrstate_at_version(s.update_resps[rid].0),
            s.log[s.update_resps[rid].0 as int],
        ).1,
    )
}

spec fn update_response_with_version(
    update_resps: Map<ReqId, UpdateResp>,
    version: LogIdx,
) -> bool {
    exists|rid| #[trigger] update_resps.contains_key(rid) && update_resps[rid].0 == version
}

spec fn state_refinement_relation_basic<DT: Dispatch>(
    s: SState<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
) -> bool {
    &&& (0 <= s.version && s.version
        <= s.log.len())
    &&& t.state == s.nrstate_at_version(
        s.version,
    )
    &&& s.readonly_reqs.dom().disjoint(s.update_reqs.dom())
    &&& s.readonly_reqs.dom().disjoint(s.update_resps.dom())
    &&& s.update_reqs.dom().disjoint(s.update_resps.dom())
    &&& t.reqs.dom().disjoint(
        t.resps.dom(),
    )
    &&& (forall|rid|
        (#[trigger] s.readonly_reqs.contains_key(rid) || #[trigger] s.update_reqs.contains_key(rid)
            || #[trigger] s.update_resps.contains_key(rid)) <==> (#[trigger] t.reqs.contains_key(
            rid,
        ) || #[trigger] t.resps.contains_key(
            rid,
        )))
    &&& (forall|rid| #[trigger]
        t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Read()
            ==> s.readonly_reqs.contains_key(rid))
    &&& (forall|rid| #[trigger]
        t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Write()
            ==> s.update_reqs.contains_key(rid) || s.update_resps.contains_key(rid))
    &&& (forall|rid| #[trigger]
        t.resps.contains_key(rid) ==> s.readonly_reqs.contains_key(rid)
            || s.update_resps.contains_key(
            rid,
        ))
    &&& (forall|v: LogIdx|
        s.version <= v && v < s.log.len() ==> update_response_with_version(
            s.update_resps,
            v,
        ))
    &&& (forall|rid1, rid2| #[trigger]
        s.update_resps.contains_key(rid1) && #[trigger] s.update_resps.contains_key(rid2) && rid1
            != rid2 ==> s.update_resps[rid1]
            != s.update_resps[rid2])
    &&& (forall|rid| #[trigger]
        s.update_resps.contains_key(rid) ==> s.update_resps[rid].0
            < s.log.len())
    &&& (forall|rid| #[trigger]
        s.update_reqs.contains_key(rid) ==> t.reqs.contains_key(rid) && t.reqs[rid]
            == InputOperation::<DT>::Write(
            s.update_reqs[rid],
        ))
    &&& (forall|rid| #[trigger]
        s.update_resps.contains_key(rid) && s.update_resps[rid].0 >= s.version ==> {
            &&& t.reqs.contains_key(rid)
            &&& t.reqs[rid] == InputOperation::<DT>::Write(s.log[s.update_resps[rid].0 as int])
        })
    &&& (forall|rid| #[trigger]
        s.update_resps.contains_key(rid) && s.update_resps[rid].0 < s.version
            ==> update_response_is_valid(s, t, r_points, rid))
}

spec fn state_refinement_relation<DT: Dispatch>(
    s: SState<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
) -> bool {
    &&& state_refinement_relation_basic(s, t, r_points)
    &&& readonly_requests_valid(s, t, r_points)
}

#[verifier::external_body]
proof fn readonly_start_refines<DT: Dispatch>(
    s: SState<DT>,
    s2: SState<DT>,
    aop: AsyncLabel<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
    rop: DT::ReadOperation,
) -> (t2: AState<DT>)
    requires
        SimpleLog::State::readonly_start(s, s2, aop, rid, rop),
        state_refinement_relation(s, t, r_points.remove(rid)),
        future_points_ok(s2, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(
            t,
            t2,
            aop,
        ),  
{
    unimplemented!()
}

#[verifier::external_body]
proof fn readonly_read_version_refines<DT: Dispatch>(
    s: SState<DT>,
    s2: SState<DT>,
    aop: AsyncLabel<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
) -> (t2: AState<DT>)
    requires
        SimpleLog::State::readonly_read_version(s, s2, aop, rid),
        state_refinement_relation(s, t, r_points),
        future_points_ok(s2, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(
            t,
            t2,
            aop,
        ),  
{
    unimplemented!()
}

#[verifier::external_body]
proof fn readonly_finish_refines<DT: Dispatch>(
    s: SState<DT>,
    s2: SState<DT>,
    aop: AsyncLabel<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
    version: LogIdx,
    ret: DT::Response,
) -> (t2: AState<DT>)
    requires
        SimpleLog::State::readonly_finish(s, s2, aop, rid, version, ret),
        state_refinement_relation(s, t, r_points.insert(rid, version)),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(
            t,
            t2,
            aop,
        ),  
{
    unimplemented!()
}

#[verifier::external_body]
proof fn update_start_refines<DT: Dispatch>(
    s: SState<DT>,
    s2: SState<DT>,
    aop: AsyncLabel<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
    uop: DT::WriteOperation,
) -> (t2: AState<DT>)
    requires
        SimpleLog::State::update_start(s, s2, aop, rid, uop),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(
            t,
            t2,
            aop,
        ),  
{
    unimplemented!()
}

#[verifier::external_body]
proof fn update_add_update_to_log_refines<DT: Dispatch>(
    s: SState<DT>,
    s2: SState<DT>,
    aop: AsyncLabel<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
) -> (t2: AState<DT>)
    requires
        SimpleLog::State::update_add_op_to_log(s, s2, aop, rid),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(
            t,
            t2,
            aop,
        ),  
{
    unimplemented!()
}

#[verifier::external_body]
proof fn update_finish_refines<DT: Dispatch>(
    s: SState<DT>,
    s2: SState<DT>,
    aop: AsyncLabel<DT>,
    t: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    rid: ReqId,
    resp: DT::Response,
) -> (t2: AState<DT>)
    requires
        SimpleLog::State::update_finish(s, s2, aop, rid, resp),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(
            t,
            t2,
            aop,
        ),  
{
    unimplemented!()
}

#[verifier::external_body]
proof fn update_incr_version_refines<DT: Dispatch>(
    a: SimpleLogBehavior<DT>,
    r_points: Map<ReqId, LogIdx>,
    new_version: LogIdx,
) -> (b: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(),
        future_points_ok(a.get_last(), r_points),
        a.is_Stepped(),
        a.get_Stepped_1().is_Internal(),
        SimpleLog::State::update_incr_version(
            a.get_Stepped_2().get_last(),
            a.get_last(),
            AsyncLabel::Internal,
            new_version,
        ),
    ensures
        b.wf(),
        behavior_equiv(a, b),
        state_refinement_relation(a.get_last(), b.get_last(), r_points),
    decreases *a.get_Stepped_2(), 1nat, new_version,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn update_incr_version_1_refines<DT: Dispatch>(
    b: AsynchronousSingletonBehavior<DT>,
    a: SimpleLogBehavior<DT>,
    a2: SimpleLogBehavior<DT>,
    r_points: Map<ReqId, LogIdx>,
) -> (b2: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(),
        future_points_ok(a2.get_last(), r_points),
        a.is_Stepped() && a2.is_Stepped(),
        a.get_Stepped_2() == a2.get_Stepped_2(),  
        a.get_Stepped_1().is_Internal() && a2.get_Stepped_1().is_Internal(),
        simple_log_state_equiv_inc_version(a.get_last(), a2.get_last()),
        a.get_last().version + 1 <= a.get_last().log.len(),
        b.wf(),
        behavior_equiv(a, b),
        state_refinement_relation(a.get_last(), b.get_last(), r_points),
    ensures
        b2.wf(),
        behavior_equiv(a2, b2),
        state_refinement_relation(a2.get_last(), b2.get_last(), r_points),
{
    unimplemented!()
}

spec fn simple_log_state_equiv_inc_version<DT: Dispatch>(a: SState<DT>, a2: SState<DT>) -> bool {
    &&& a2.log == a.log
    &&& a2.version == a.version + 1
    &&& a2.readonly_reqs == a.readonly_reqs
    &&& a2.update_reqs == a.update_reqs
    &&& a2.update_resps == a.update_resps
}

spec fn recursion_invariant<DT: Dispatch>(
    s: SState<DT>,
    s2: SState<DT>,
    t2: AState<DT>,
    r_points: Map<ReqId, LogIdx>,
    the_reads: Set<ReqId>,
) -> bool {
    &&& the_reads.finite()
    &&& s.version + 1 <= s.log.len()
    &&& state_refinement_relation_basic(s2, t2, r_points)
    &&& (forall|rid| #[trigger]
        the_reads.contains(rid) ==> {
            &&& r_points.contains_key(rid)
            &&& r_points[rid] == s.version + 1
            &&& s.readonly_reqs.contains_key(rid)
            &&& s.readonly_reqs[rid] is Req
        })
    &&& (forall|rid| #[trigger]
        s.readonly_reqs.contains_key(rid) && t2.reqs.contains_key(rid) ==> {
            !the_reads.contains(rid) ==> readonly_request_is_valid(s2, t2, r_points, rid)
        })
    &&& (forall|rid| #[trigger]
        s.readonly_reqs.contains_key(rid) && t2.resps.contains_key(rid) ==> {
            !the_reads.contains(rid) ==> readonly_response_is_valid(s2, t2, r_points, rid)
        })
    &&& (forall|rid| #[trigger]
        s.readonly_reqs.contains_key(rid) && t2.reqs.contains_key(rid) ==> {
            the_reads.contains(rid) ==> readonly_request_is_valid(s, t2, r_points, rid)
        })
    &&& (forall|rid| #[trigger]
        s.readonly_reqs.contains_key(rid) && t2.resps.contains_key(rid) ==> {
            the_reads.contains(rid) ==> readonly_response_is_valid(s, t2, r_points, rid)
        })
}

#[verifier::external_body]
proof fn update_incr_version_1_read_reqs<DT: Dispatch>(
    b2: AsynchronousSingletonBehavior<DT>,
    a: SimpleLogBehavior<DT>,
    a2: SimpleLogBehavior<DT>,
    r_points: Map<ReqId, LogIdx>,
    the_reads: Set<ReqId>,
) -> (res: AsynchronousSingletonBehavior<DT>)
    requires
        b2.wf(),
        behavior_equiv(a2, b2),
        recursion_invariant(a.get_last(), a2.get_last(), b2.get_last(), r_points, the_reads),
        simple_log_state_equiv_inc_version(a.get_last(), a2.get_last()),
    ensures
        res.wf(),
        behavior_equiv(a2, res),
        recursion_invariant(
            a.get_last(),
            a2.get_last(),
            res.get_last(),
            r_points,
            Set::<ReqId>::empty(),
        ),
    decreases the_reads.len(),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn state_at_version_preserves<DT: Dispatch>(
    a: Seq<DT::WriteOperation>,
    b: Seq<DT::WriteOperation>,
    x: DT::WriteOperation,
    i: LogIdx,
)
    requires
        b == a.push(x),
        i <= a.len(),
        i <= b.len(),
    ensures
        compute_nrstate_at_version::<DT>(a, i) == compute_nrstate_at_version::<DT>(b, i),
    decreases i,
{
    unimplemented!()
}

#[verifier::external_body]
proof fn pop_rid(t: Set<ReqId>) -> (res: (Set<ReqId>, ReqId))
    requires
        !t.is_empty(),
        t.finite(),
    ensures
        res.0.len() < t.len(),
        t.contains(res.1),
        res.0 =~= t.remove(res.1),
        res.0.finite(),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn trick_equiv<DT: Dispatch>(
    a: SimpleLogBehavior<DT>,
    a2: SimpleLogBehavior<DT>,
    b: AsynchronousSingletonBehavior<DT>,
)
    requires
        behavior_equiv(a, b),
        a.is_Stepped(),
        a2.is_Stepped(),
        a.get_Stepped_2() == a2.get_Stepped_2(),
        a.get_Stepped_1().is_Internal(),
        a2.get_Stepped_1().is_Internal(),
    ensures
        behavior_equiv(a2, b),
    decreases b,
{
    unimplemented!()
}

spec fn all_reads_for<DT: Dispatch>(
    readonly_reqs: Map<ReqId, ReadReq<DT::ReadOperation>>,
    r_points: Map<ReqId, LogIdx>,
    version: LogIdx,
) -> Set<ReqId>
    recommends
        r_points.dom().finite(),
{
    r_points.dom().filter(
        |rid|
            r_points[rid] == version && readonly_reqs.contains_key(rid)
                && readonly_reqs[rid] is Req,
    )
}

} 
}

pub mod simple_log {
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::*;

use vstd::prelude::*;

use crate::spec::types::*;
use crate::{AsyncLabel, Dispatch, InputOperation, OutputOperation};



verus! {

pub ghost enum ReadReq<R> {
    Init { op: R },
    Req { version: LogIdx, op: R },
}

impl<R> ReadReq<R> {
    pub open spec fn op(self) -> R {
        match self {
            ReadReq::Init { op } => op,
            ReadReq::Req { op, .. } => op,
        }
    }
}

pub ghost struct UpdateResp(pub LogIdx);

state_machine! {
    SimpleLog<DT: Dispatch> {
    fields {
        pub log: Seq<DT::WriteOperation>,
        pub version: LogIdx,
        pub readonly_reqs: Map<ReqId, ReadReq<DT::ReadOperation>>,
        pub update_reqs: Map<ReqId, DT::WriteOperation>,
        pub update_resps: Map<ReqId, UpdateResp>,
    }

    pub type Label<DT> = AsyncLabel<DT>;



    #[invariant]
    pub fn inv_version(&self) -> bool {
        0 <= self.version <= self.log.len()
    }

    #[invariant]
    pub fn inv_update_resp_version(&self) -> bool {
        forall |rid: ReqId| #[trigger] self.update_resps.contains_key(rid)
            ==> self.update_resps[rid].0 < self.log.len()
    }

    #[invariant]
    pub fn inv_readonly_req_version(&self) -> bool {
        forall |rid: ReqId| #[trigger] self.readonly_reqs.contains_key(rid) && self.readonly_reqs[rid] is Req
            ==> self.readonly_reqs[rid]->version <= self.version
    }




    init!{
        initialize() {
            init log = Seq::empty();
            init version = 0;
            init readonly_reqs = Map::empty();
            init update_reqs = Map::empty();
            init update_resps = Map::empty();
        }
    }




    pub open spec fn nrstate_at_version(&self, version: LogIdx) -> DT::View
        recommends 0 <= version <= self.log.len()
    {
        compute_nrstate_at_version::<DT>(self.log, version)
    }



    transition!{
        readonly_start(label: Label<DT>, rid: ReqId, op: DT::ReadOperation) {
            require label == AsyncLabel::<DT>::Start(rid, InputOperation::Read(op));

            require !pre.readonly_reqs.contains_key(rid);
            require !pre.update_reqs.contains_key(rid);
            require !pre.update_resps.contains_key(rid);

            update readonly_reqs[rid] = ReadReq::<DT::ReadOperation>::Init{ op };
        }
    }

    transition!{
        readonly_read_version(label: Label<DT>, rid: ReqId) {
            require label.is_Internal();

            require pre.readonly_reqs.contains_key(rid);
            require let ReadReq::<DT::ReadOperation>::Init { op } = pre.readonly_reqs[rid];

            update readonly_reqs[rid] = ReadReq::<DT::ReadOperation>::Req { op, version: pre.version };
        }
    }

    transition!{
        readonly_finish(label: Label<DT>, rid: ReqId, version: LogIdx, ret: DT::Response) {
            require label == AsyncLabel::<DT>::End(rid, OutputOperation::Read(ret));

            require pre.readonly_reqs.contains_key(rid);
            require let ReadReq::<DT::ReadOperation>::Req { op, version: current } = pre.readonly_reqs[rid];

            require current <= version <= pre.log.len();
            require version <= pre.version;
            require ret == DT::dispatch_spec(pre.nrstate_at_version(version), op);

            update readonly_reqs = pre.readonly_reqs.remove(rid);
        }
    }






    transition!{
        update_start(label: Label<DT>, rid: ReqId, op: DT::WriteOperation) {
            require label == AsyncLabel::<DT>::Start(rid, InputOperation::Write(op));

            require !pre.readonly_reqs.contains_key(rid);
            require !pre.update_reqs.contains_key(rid);
            require !pre.update_resps.contains_key(rid);

            update update_reqs[rid] = op;
        }
    }

    transition!{
        update_add_op_to_log(label: Label<DT>, rid: ReqId) {
            require label.is_Internal();

            require pre.update_reqs.contains_key(rid);

            update log = pre.log.push(pre.update_reqs[rid]);
            update update_reqs = pre.update_reqs.remove(rid);
            update update_resps = pre.update_resps.insert(rid, UpdateResp(pre.log.len()));
        }
    }

    transition!{
        update_incr_version(label: Label<DT>, new_version: LogIdx) {
            require label.is_Internal();

            require pre.version <= new_version <= pre.log.len();

            update version = new_version;
        }
    }

    transition!{
        update_finish(label: Label<DT>, rid: nat, ret: DT::Response) {
            require label == AsyncLabel::<DT>::End(rid, OutputOperation::Write(ret));

            require pre.update_resps.contains_key(rid);
            let uidx = pre.update_resps[rid].0;

            require uidx < pre.version <= pre.log.len();
            require ret == DT::dispatch_mut_spec(pre.nrstate_at_version(uidx), pre.log[uidx as int]).1;

            update update_resps = pre.update_resps.remove(rid);
        }
    }




    transition!{
        no_op(label: Label<DT>, ) {
            require label.is_Internal();
        }
    }




    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(readonly_start)]
    fn readonly_start_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, op: DT::ReadOperation) { }

    #[inductive(readonly_read_version)]
    fn readonly_read_version_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId) { }

    #[inductive(readonly_finish)]
    fn readonly_finish_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, version: LogIdx, ret: DT::Response) { }

    #[inductive(update_start)]
    fn update_start_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, op: DT::WriteOperation) { }

    #[inductive(update_add_op_to_log)]
    fn update_add_op_to_log_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId) { }

    #[inductive(update_incr_version)]
    fn update_incr_version_inductive(pre: Self, post: Self, label: Label<DT>, new_version: LogIdx) { }

    #[inductive(update_finish)]
    fn update_finish_inductive(pre: Self, post: Self, label: Label<DT>, rid: nat,  ret: DT::Response) { }

    #[inductive(no_op)]
    fn no_op_inductive(pre: Self, post: Self, label: Label<DT>) { }

}}  


pub open spec fn compute_nrstate_at_version<DT: Dispatch>(
    log: Seq<DT::WriteOperation>,
    version: LogIdx,
) -> DT::View
    recommends
        0 <= version <= log.len(),
    decreases version,
{
    if version == 0 {
        DT::init_spec()
    } else {
        DT::dispatch_mut_spec(
            compute_nrstate_at_version::<DT>(log, (version - 1) as nat),
            log[version - 1],
        ).0
    }
}

} 
}

#[macro_use]
pub mod unbounded_log {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::*;

use vstd::map::Map;
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::set::Set;

use crate::Dispatch;

use super::types::*;
use super::utils::*;

verus! {

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
    fn readonly_version_upper_bound_inductive(pre: Self, post: Self, rid: ReqId) { }

    #[inductive(readonly_ready_to_read)]
    fn readonly_ready_to_read_inductive(pre: Self, post: Self, rid: ReqId, node_id: NodeId) {
        match post.local_reads[rid] {
            ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                assert(post.combiner.contains_key(node_id));
                assert(post.local_versions.contains_key(node_id));
                assert(post.replicas.contains_key(node_id));
                assert(version_upper_bound <= post.version_upper_bound);
                assert(version_upper_bound <= post.current_local_version(node_id));
            }
            _ => { }
        };
        assert(post.wf_readstate(post.local_reads[rid]));
    }

    #[inductive(readonly_apply)]
    fn readonly_apply_inductive(pre: Self, post: Self, rid: ReqId) {
        let ret = post.local_reads[rid].get_Done_ret();
        let nid = post.local_reads[rid].get_Done_node_id();
        let vup = post.local_reads[rid].get_Done_version_upper_bound();
        let v = post.local_versions[nid];
        assert(rangeincl(vup, v, post.version_upper_bound));
    }

    #[verifier::external_body]
    pub proof fn add_ticket_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: crate::InputOperation<DT>,
        rid: crate::ReqId,
    )
        requires pre.invariant(),
            crate::add_ticket(pre, post, input, rid),
            rid == get_fresh_nat(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner)
        ensures post.invariant(),
    {
        unimplemented!()
    }

    #[inductive(update_done)]
    fn update_done_inductive(pre: Self, post: Self, rid: ReqId) {
        assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
            match post.combiner[node_id] {
                CombinerState::Placed { queued_ops } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                }
                _ => {}
            }
        }
    }

    #[verifier::external_body]
    pub proof fn consume_stub_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: crate::OutputOperation<DT>,
        rid: crate::ReqId,
    )
        requires pre.invariant(),
            crate::consume_stub(pre, post, output, rid),
        ensures post.invariant(),
    {
        unimplemented!()
    }

    #[inductive(exec_trivial_start)]
    fn exec_trivial_start_inductive(pre: Self, post: Self, node_id: NodeId) {
        concat_LogRangeNoNodeId_LogRangeMatchesQueue(
            Seq::empty(), post.log, 0,
            pre.local_versions[node_id],
            pre.tail,
            post.tail,
            node_id,
            post.local_updates);

        assert(post.wf_combiner_for_node_id(node_id));
    }

    #[inductive(update_place_ops_in_log_one)]
    fn update_place_ops_in_log_one_inductive(pre: Self, post: Self, node_id: NodeId, rid: ReqId) {

        let old_queued_ops = pre.combiner[node_id].get_Placed_queued_ops();
        let op = pre.local_updates[rid].get_Init_op();

        assert(post.wf_combiner_for_node_id(node_id)) by {
            match post.combiner[node_id] {
                CombinerState::Placed{queued_ops} => {
                    LogRangeMatchesQueue_append(old_queued_ops, pre.log, post.log, 0,
                        post.local_versions[node_id], pre.tail,
                        node_id, pre.local_updates, post.local_updates, rid,
                        LogEntry{ op, node_id });
                }
                _ => { }
            }
        }

        assert(post.inv_local_updates_wf(post.local_updates[rid]));

        assert forall |node_id1| #[trigger] post.combiner.contains_key(node_id1)
            && node_id1 != node_id
            implies post.wf_combiner_for_node_id(node_id1)
        by {
            assert(pre.combiner[node_id1] === post.combiner[node_id1]);
            assert(pre.wf_combiner_for_node_id(node_id1));
            match pre.combiner[node_id1] {
                CombinerState::Ready => {
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        post.local_versions[node_id1], pre.tail, node_id1, LogEntry{ op, node_id });
                }
                CombinerState::Placed{queued_ops} => {
                    LogRangeMatchesQueue_append_other_augment(queued_ops, pre.log, post.log,
                        0, post.local_versions[node_id1], pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                }
                CombinerState::LoadedLocalVersion{queued_ops, lversion} => {
                    LogRangeMatchesQueue_append_other_augment(queued_ops, pre.log, post.log,
                        0, lversion, pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                }
                CombinerState::Loop{queued_ops, lversion, idx, tail} => {
                    LogRangeMatchesQueue_append_other(queued_ops, pre.log, post.log,
                        idx, lversion, tail, pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        tail, pre.tail,
                        node_id1, LogEntry{ op, node_id });
                }
                CombinerState::UpdatedVersion{queued_ops, tail} => {
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        tail, pre.tail, node_id1, LogEntry{ op, node_id });
                }
            }
        }

        assert (forall |nid| (#[trigger] pre.replicas.contains_key(nid)) ==> pre.local_versions.contains_key(nid));

        assert forall |nid| (#[trigger] post.replicas.contains_key(nid)) implies
            post.replicas[nid] == compute_nrstate_at_version(post.log, post.current_local_version(nid)) by
        {
            compute_nrstate_at_version_preserves(pre.log, post.log, post.current_local_version(nid));
        }

        assert forall |rid| (#[trigger] post.local_updates.contains_key(rid))
            implies post.update_results_match(post.local_updates[rid]) by
        {
            match post.local_updates[rid] {
                UpdateState::Applied { ret, idx } => {
                    compute_nrstate_at_version_preserves(pre.log, post.log, idx);
                },
                UpdateState::Done { ret, idx } => {
                    compute_nrstate_at_version_preserves(pre.log, post.log, idx);
                },
                _ => {},
            }
        }

        assert forall |rid| (#[trigger] post.local_reads.contains_key(rid))
            implies post.read_results_match(post.local_reads[rid]) by
        {
            match post.local_reads[rid] {
                ReadonlyState::Done { ret, version_upper_bound, op, .. } => {
                    let ver = choose |ver| (#[trigger] rangeincl(version_upper_bound, ver, pre.version_upper_bound)
                        && ret == DT::dispatch_spec(compute_nrstate_at_version(pre.log, ver), op));
                    compute_nrstate_at_version_preserves(pre.log, post.log, ver);
                },
                _ => {},
            }
        }
    }


    #[inductive(exec_load_local_version)]
    fn exec_load_local_version_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_load_global_head)]
    fn exec_load_global_head_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_dispatch_local)]
    fn exec_dispatch_local_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert(post.wf_combiner_for_node_id(node_id)) by {
            LogRangeMatchesQueue_update_change(
                post.combiner[node_id].get_Loop_queued_ops(),
                post.log, post.combiner[node_id].get_Loop_idx(), post.combiner[node_id].get_Loop_lversion(),
                pre.combiner[node_id].get_Loop_tail(), node_id, pre.local_updates, post.local_updates);
        }

        let c = pre.combiner[node_id];
        let rid = c.get_Loop_queued_ops().index(c.get_Loop_idx() as int);
        assert forall |node_id0| #[trigger] post.combiner.contains_key(node_id0) && node_id0 != node_id
            implies post.wf_combiner_for_node_id(node_id0)
        by {
            match pre.combiner[node_id0] {
            CombinerState::Ready => {
            }
            CombinerState::Placed{queued_ops} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, 0, post.local_versions[node_id0], post.tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::LoadedLocalVersion{queued_ops, lversion} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, 0, lversion, post.tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::Loop{queued_ops, idx, lversion, tail} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, idx, lversion, tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::UpdatedVersion{queued_ops, tail} => {
            }
            }
        }
    }

    #[inductive(exec_dispatch_remote)]
    fn exec_dispatch_remote_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_update_version_upper_bound)]
    fn exec_update_version_upper_bound_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert(post.version_upper_bound >= pre.version_upper_bound);

        assert forall |rid| (#[trigger] post.local_reads.contains_key(rid)) implies post.read_results_match(post.local_reads[rid]) by {
            match post.local_reads[rid] {
                ReadonlyState::Done { ret, version_upper_bound, op, .. } => {
                    let ver = choose |ver| (#[trigger] rangeincl(version_upper_bound, ver, pre.version_upper_bound)
                        && ret == DT::dispatch_spec(compute_nrstate_at_version(post.log, ver), op));
                    assert(rangeincl(version_upper_bound, ver, post.version_upper_bound));
                },
                _ => {}
            }
        }
    }

    #[inductive(exec_finish)]
    fn exec_finish_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_finish_no_change)]
    fn exec_finish_no_change_inductive(pre: Self, post: Self, node_id: NodeId) { }


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

#[verifier::external_body]
pub proof fn combiner_request_ids_proof(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    requires
        combiners.dom().finite(),
    decreases combiners.dom().len(),
{
    unimplemented!()
}

pub open spec fn combiner_request_id_fresh(
    combiners: Map<NodeId, CombinerState>,
    rid: ReqId,
) -> bool {
    forall|n| (#[trigger] combiners.contains_key(n)) ==> !combiners[n].queued_ops().contains(rid)
}

#[verifier::external_body]
pub proof fn combiner_request_ids_not_contains(combiners: Map<NodeId, CombinerState>, rid: ReqId)
    requires
        combiners.dom().finite(),
    ensures
        combiner_request_id_fresh(combiners, rid) <==> !combiner_request_ids(combiners).contains(
            rid,
        ),
    decreases combiners.dom().len(),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn combiner_request_ids_finite(combiners: Map<NodeId, CombinerState>)
    requires
        combiners.dom().finite(),
    ensures
        combiner_request_ids(combiners).finite(),
    decreases combiners.dom().len(),
{
    unimplemented!()
}

pub closed spec fn get_fresh_nat(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>) -> nat
    recommends
        reqs.finite() && combiner.dom().finite(),
{
    choose|n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n)
}

#[verifier::external_body]
proof fn max_of_set(s: Set<nat>) -> (r: nat)
    requires
        s.finite(),
    ensures
        forall|x: nat| #[trigger] s.contains(x) ==> x <= r,
    decreases s.len(),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn element_outside_set(s: Set<nat>) -> (r: nat)
    requires
        s.finite(),
    ensures
        !s.contains(r),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn get_fresh_nat_not_in(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>)
    requires
        reqs.finite(),
        combiner.dom().finite(),
    ensures
        !reqs.contains(get_fresh_nat(reqs, combiner)),
        combiner_request_id_fresh(combiner, get_fresh_nat(reqs, combiner)),
{
    unimplemented!()
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

#[verifier::external_body]
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
    unimplemented!()
}

#[verifier::external_body]
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
    unimplemented!()
}

#[verifier::external_body]
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
    unimplemented!()
}

#[verifier::external_body]
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
    unimplemented!()
}

#[verifier::external_body]
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
    unimplemented!()
}

#[verifier::external_body]
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
    unimplemented!()
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

#[verifier::external_body]
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
    unimplemented!()
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

#[verifier::external_body]
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
    unimplemented!()
}

} 
}
pub mod unbounded_log_refines_simplelog {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::prelude::*;

use vstd::map::*;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::seq::Seq;
use vstd::seq_lib::*;

#[cfg(verus_keep_ghost)]
use verus_state_machines_macros::*;

use crate::{Dispatch, InputOperation, OutputOperation, ReqId};

#[cfg(verus_keep_ghost)]
use super::simple_log::{
    compute_nrstate_at_version as s_nrstate_at_version, ReadReq as SReadReq, SimpleLog,
    UpdateResp as SUpdateResp,
};
use super::types::*;
#[cfg(verus_keep_ghost)]
use super::unbounded_log::{
    compute_nrstate_at_version as i_nrstate_at_version, ReadonlyState, UnboundedLog, UpdateState,
};
use super::utils::*;


verus! {

#[verifier::external_body]
#[verifier::reject_recursive_types(DT)]
pub tracked struct RefinementProof<DT: Dispatch> {
    _p: std::marker::PhantomData<DT>,
}

impl<DT: Dispatch> crate::UnboundedLogRefinesSimpleLog<DT> for RefinementProof<DT> {
    closed spec fn interp(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT> {
        interp(s)
    }

    #[verifier::external_body]
    proof fn refinement_inv(vars: UnboundedLog::State<DT>) {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn refinement_init(post: UnboundedLog::State<DT>) {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn refinement_next(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>) {
        unimplemented!()
    }

    open spec fn get_fresh_rid(pre: UnboundedLog::State<DT>) -> ReqId {
        crate::spec::unbounded_log::get_fresh_nat(
            pre.local_updates.dom() + pre.local_reads.dom(),
            pre.combiner,
        )
    }

    #[verifier::external_body]
    proof fn fresh_rid_is_ok(pre: UnboundedLog::State<DT>) {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn refinement_add_ticket(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: InputOperation<DT>,
    ) {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn refinement_consume_stub(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: OutputOperation<DT>,
        rid: ReqId,
    ) {
        unimplemented!()
    }
}

spec fn interp_log<DT: Dispatch>(global_tail: nat, log: Map<nat, LogEntry<DT>>) -> Seq<
    DT::WriteOperation,
> {
    Seq::new(global_tail, |i| log.index(i as nat).op)
}

spec fn interp_readonly_reqs<DT: Dispatch>(local_reads: Map<nat, ReadonlyState<DT>>) -> Map<
    ReqId,
    SReadReq<DT::ReadOperation>,
> {
    Map::new(
        local_reads.dom(),
        |rid|
            match local_reads.index(rid) {
                ReadonlyState::Init { op } => SReadReq::Init { op },
                ReadonlyState::VersionUpperBound { version_upper_bound: idx, op } => SReadReq::Req {
                    op,
                    version: idx,
                },
                ReadonlyState::ReadyToRead { version_upper_bound: idx, op, .. } => SReadReq::Req {
                    op,
                    version: idx,
                },
                ReadonlyState::Done { version_upper_bound: idx, op, .. } => SReadReq::Req {
                    op,
                    version: idx,
                },
            },
    )
}

spec fn interp_update_reqs<DT: Dispatch>(local_updates: Map<LogIdx, UpdateState<DT>>) -> Map<
    LogIdx,
    DT::WriteOperation,
> {
    Map::new(
        local_updates.dom().filter(|rid| local_updates.index(rid).is_Init()),
        |rid|
            match local_updates.index(rid) {
                UpdateState::Init { op } => op,
                _ => arbitrary(),
            },
    )
}

spec fn interp_update_resps<DT: Dispatch>(local_updates: Map<nat, UpdateState<DT>>) -> Map<
    ReqId,
    SUpdateResp,
> {
    Map::new(
        local_updates.dom().filter(|rid| !local_updates.index(rid).is_Init()),
        |rid|
            match local_updates.index(rid) {
                UpdateState::Init { op } => arbitrary(),
                UpdateState::Placed { op, idx } => SUpdateResp(idx),
                UpdateState::Applied { ret, idx } => SUpdateResp(idx),
                UpdateState::Done { ret, idx } => SUpdateResp(idx),
            },
    )
}

spec fn interp<DT: Dispatch>(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT> {
    SimpleLog::State {
        log: interp_log(s.tail, s.log),
        version: s.version_upper_bound,
        readonly_reqs: interp_readonly_reqs(s.local_reads),
        update_reqs: interp_update_reqs(s.local_updates),
        update_resps: interp_update_resps(s.local_updates),
    }
}

#[verifier::external_body]
proof fn refinement_inv<DT: Dispatch>(vars: UnboundedLog::State<DT>)
    requires
        vars.invariant(),
    ensures
        interp(vars).invariant(),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn refinement_init<DT: Dispatch>(post: UnboundedLog::State<DT>)
    requires
        post.invariant(),
        UnboundedLog::State::init(post),
    ensures
        SimpleLog::State::init(interp(post)),
{
    unimplemented!()
}

#[verifier::external_body]
proof fn refinement_next<DT: Dispatch>(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>)
    requires
        pre.invariant(),
        post.invariant(),
        UnboundedLog::State::next_strong(pre, post),
    ensures
        SimpleLog::State::next(interp(pre), interp(post), crate::AsyncLabel::Internal),
{
    unimplemented!()
}

pub open spec fn dummy(lower: nat, mid: nat, upper: nat) -> bool
    recommends
        lower <= upper,
{
    lower <= mid <= upper
}

pub open spec fn dummy2(lower: nat, mid: nat, upper: nat) -> bool
    recommends
        lower < upper,
{
    lower <= mid < upper
}

pub open spec fn version_in_log<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    version: LogIdx,
) -> bool {
    forall|i| 0 <= i < version ==> log.contains_key(i)
}

pub open spec fn result_match<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    output: DT::Response,
    version: LogIdx,
    op: DT::ReadOperation,
) -> bool
    recommends
        version_in_log(log, version),
{
    output == DT::dispatch_spec(i_nrstate_at_version(log, version), op)
}

#[verifier::external_body]
proof fn state_at_version_refines<DT: Dispatch>(
    s_log: Seq<DT::WriteOperation>,
    i_log: Map<LogIdx, LogEntry<DT>>,
    gtail: nat,
    idx: nat,
)
    requires
        forall|i| 0 <= i < gtail ==> i_log.contains_key(i),
        0 <= idx <= s_log.len(),
        idx <= gtail,
        s_log == interp_log(gtail, i_log),
    ensures
        s_nrstate_at_version::<DT>(s_log, idx) == i_nrstate_at_version::<DT>(i_log, idx),
    decreases idx,
{
    unimplemented!()
}

} 
}

#[macro_use]
pub mod cyclicbuffer {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::prelude::*;

use vstd::cell::{CellId, PointsTo};

use verus_state_machines_macros::*;

use crate::Dispatch;

use super::types::*;
use super::unbounded_log::UnboundedLog;
use super::utils::*;

#[cfg(verus_keep_ghost)]
use vstd::prelude::OptionAdditionalFns;


verus! {

pub type LogicalLogIdx = int;

use crate::constants::LOG_SIZE;

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
        assert(post.local_versions.contains_key(node_id));
    }

    #[inductive(advance_tail_start)]
    fn advance_tail_start_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert forall |n| 0 <= n < post.num_replicas as nat implies post.head <= post.local_versions[n] by {
            assert(post.local_versions.contains_key(n));
        }
     }

    #[inductive(advance_tail_abort)]
    fn advance_tail_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(advance_tail_finish)]
    fn advance_tail_finish_inductive(pre: Self, post: Self, node_id: NodeId, new_tail: nat) {
        assert(post.local_versions.contains_key(node_id));

        let mycur_idx = post.combiner[node_id].get_Appending_cur_idx();
        let mytail = post.combiner[node_id].get_Appending_tail();
        assert(mycur_idx == pre.tail);

        let min_local_versions = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);
        map_min_value_smallest(post.local_versions,  (post.num_replicas - 1) as nat);
        assert(mycur_idx >= min_local_versions);
    }

    #[inductive(append_flip_bit)]
    fn append_flip_bit_inductive(pre: Self, post: Self, node_id: NodeId, deposited: StoredType<DT>) {
        assert(post.local_versions.contains_key(node_id));

        let myidx = pre.combiner[node_id].get_Appending_cur_idx();
        let mytail = pre.combiner[node_id].get_Appending_tail();

        let min_local_head = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);
        map_min_value_smallest(post.local_versions, (post.num_replicas - 1) as nat);

        log_entry_idx_wrap_around(min_local_head, post.buffer_size, myidx);

        assert(forall |i| min_local_head <= i < min_local_head + post.buffer_size && i != myidx ==>
            log_entry_is_alive(pre.alive_bits, i, pre.buffer_size) == log_entry_is_alive(post.alive_bits, i, post.buffer_size));

        assert forall |i, j| post.combiner.contains_key(i) && post.combiner.contains_key(j) && i != j
            implies post.combiner[i].no_overlap_with(post.combiner[j]) by {
            assert(pre.combiner[i].no_overlap_with(pre.combiner[j]));
        }

        assert forall |nid| #[trigger] post.combiner.contains_key(nid) implies
            post.combiner_valid(nid, post.combiner[nid]) by
        {
            if nid != node_id {
                assert(pre.combiner[node_id].no_overlap_with(pre.combiner[nid]));
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
        assert(post.local_versions.contains_key(node_id));
        assert forall |i, j| post.combiner.contains_key(i) && post.combiner.contains_key(j) && i != j
        implies post.combiner[i].no_overlap_with(post.combiner[j]) by {
            if (j == node_id && post.combiner[i].is_Appending()) {
                let cur = post.combiner[j].get_Reading_0().get_Guard_cur();
                assert(log_entry_is_alive(post.alive_bits, cur as int, post.buffer_size));
            }
        }
    }

    #[inductive(reader_unguard)]
    fn reader_unguard_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(reader_finish)]
    fn reader_finish_inductive(pre: Self, post: Self, node_id: NodeId) {

        let min_local_versions_pre = map_min_value(pre.local_versions, (pre.num_replicas - 1) as nat);
        let min_local_versions_post = map_min_value(post.local_versions, (post.num_replicas - 1) as nat);

        if min_local_versions_pre != min_local_versions_post {

            map_min_value_smallest(pre.local_versions, (pre.num_replicas - 1) as nat);
            map_min_value_smallest(post.local_versions, (post.num_replicas - 1) as nat);

            assert(forall |i| #[trigger] pre.local_versions.contains_key(i) ==> min_local_versions_pre <= pre.local_versions[i]);
            assert(forall |i| #[trigger] post.local_versions.contains_key(i) ==> min_local_versions_post <= post.local_versions[i]);

            log_entry_alive_wrap_around(post.alive_bits, post.buffer_size, min_local_versions_pre, min_local_versions_post);
            log_entry_alive_wrap_around_helper(post.alive_bits, post.buffer_size, min_local_versions_pre, min_local_versions_post );
        }
    }

    #[inductive(reader_abort)]
    fn reader_abort_inductive(pre: Self, post: Self, node_id: NodeId) { }
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

#[verifier::external_body]
proof fn map_min_value_smallest(m: Map<NodeId, nat>, idx: nat)
    requires
        forall|i| 0 <= i <= idx ==> m.contains_key(i),
    ensures
        forall|n| 0 <= n <= idx as nat ==> map_min_value(m, idx) <= m.index(n),
        map_contains_value(m, map_min_value(m, idx)),
    decreases idx,
{
    unimplemented!()
}

pub open spec fn log_entry_idx(logical: LogicalLogIdx, buffer_size: nat) -> LogIdx
    recommends
        buffer_size == LOG_SIZE,
{
    (logical % (buffer_size as int)) as nat
}

#[verifier::external_body]
pub proof fn log_entry_idx_wrap_around(start: nat, buffer_size: nat, idx: nat)
    requires
        buffer_size == LOG_SIZE,
        start <= idx < start + buffer_size,
    ensures
        forall|i|
            start <= i < start + buffer_size && i != idx ==> log_entry_idx(i, buffer_size)
                != log_entry_idx(idx as int, buffer_size),
{
    unimplemented!()
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

#[verifier::external_body]
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
    unimplemented!()
}

#[verifier::external_body]
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
    unimplemented!()
}

#[verifier(nonlinear)]
#[verifier::external_body]
pub proof fn log_entry_alive_value_wrap_around(i: LogicalLogIdx, buffer_size: nat)
    requires
        buffer_size > 0,
    ensures
        log_entry_alive_value(i, buffer_size) != log_entry_alive_value(
            i + (buffer_size as int),
            buffer_size,
        ),
{
    unimplemented!()
}

} 
}

pub mod flat_combiner {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

use vstd::prelude::*;

use verus_state_machines_macros::*;

use super::types::*;

verus! {

#[is_variant]
pub tracked enum ClientState {
    Idle,
    Waiting(ReqId),
}

#[is_variant]
pub tracked enum SlotState {
    Empty,
    Request(ReqId),
    InProgress(ReqId),
    Response(ReqId),
}

impl SlotState {
    pub open spec fn get_ReqId(&self) -> ReqId {
        match self {
            SlotState::Empty => arbitrary(),
            SlotState::Request(reqid) => *reqid,
            SlotState::InProgress(reqid) => *reqid,
            SlotState::Response(reqid) => *reqid,
        }
    }
}

#[is_variant]
pub tracked enum CombinerState {
    Collecting(Seq<Option<ReqId>>),
    Responding(Seq<Option<ReqId>>, nat),
}

impl CombinerState {
    pub open spec fn req_len(self) -> nat {
        match self {
            CombinerState::Collecting(reqs) => reqs.len(),
            CombinerState::Responding(reqs, _) => reqs.len(),
        }
    }

    pub open spec fn req_is_none(self, tid: nat) -> bool
        recommends
            0 <= tid < self.req_len(),
    {
        match self {
            CombinerState::Collecting(reqs) => reqs[tid as int].is_none(),
            CombinerState::Responding(reqs, _) => reqs[tid as int].is_none(),
        }
    }

    pub open spec fn req_is_some(self, tid: nat) -> bool
        recommends
            0 <= tid < self.req_len(),
    {
        match self {
            CombinerState::Collecting(reqs) => reqs[tid as int].is_some(),
            CombinerState::Responding(reqs, _) => reqs[tid as int].is_some(),
        }
    }
}

tokenized_state_machine! {
FlatCombiner {
    fields {
        #[sharding(constant)]
        pub num_threads: nat,

        #[sharding(map)]
        pub clients: Map<ThreadId, ClientState>,

        #[sharding(map)]
        pub slots: Map<ThreadId, SlotState>,

        #[sharding(variable)]
        pub combiner: CombinerState,
    }


    #[invariant]
    pub fn inv_complete(&self) -> bool {
        &&& (forall |i| self.clients.contains_key(i) <==> i < self.num_threads)
        &&& (forall |i| self.slots.contains_key(i) <==> i < self.num_threads)
    }


    #[invariant]
    pub fn inv_client_slot_empty(&self) -> bool {
        forall |i:nat| #[trigger] self.clients.contains_key(i)
            ==>  (self.clients[i].is_Idle() <==> self.slots[i].is_Empty())
    }

    #[invariant]
    pub fn inv_client_reqids(&self) -> bool {
        forall |i:nat| #[trigger] self.clients.contains_key(i) && self.clients[i].is_Waiting()
            ==> self.clients[i].get_Waiting_0() == self.slots[i].get_ReqId()
    }

    #[invariant]
    pub fn inv_combiner_elements(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                elems.len() <= self.num_threads
            },
            CombinerState::Responding(elems, idx) => {
                &&& elems.len() == self.num_threads
                &&& idx <= elems.len()
            },
        }
    }

    pub open spec fn slot_in_progress(slots: Map<nat, SlotState>, tid: nat) -> bool
        recommends slots.contains_key(tid)
    {
        slots[tid].is_InProgress()
    }

    #[invariant]
    pub fn inv_combiner_slots_not_in_progress(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                &&& (forall |i: nat| 0 <= i < elems.len() && elems[i as int].is_none()
                    ==> !(#[trigger] self.slots[i]).is_InProgress()) 
                &&& (forall |i: nat| elems.len() <= i < self.num_threads ==> !self.slots[i].is_InProgress())
            },
            CombinerState::Responding(elems, idx) => {
                &&& (forall |i: nat| 0 <= i < elems.len() && elems[i as int].is_none()
                    ==> !(#[trigger] self.slots[i]).is_InProgress()) 
                &&& (forall |i: nat| 0 <= i < idx ==> !self.slots[i].is_InProgress())
            },
        }
    }

    #[invariant]
    pub fn inv_combiner_request_ids(&self) -> bool {
        match self.combiner {
            CombinerState::Collecting(elems) => {
                forall |i:nat| (0 <= i < elems.len() && elems[i as int].is_some())
                    ==> (#[trigger] self.slots[i]).is_InProgress() && (#[trigger] self.slots[i]).get_InProgress_0() == elems[i as int].unwrap()
            },
            CombinerState::Responding(elems, idx) => {
                forall |i:nat| idx <= i < elems.len() && elems[i as int].is_some()
                   ==> (#[trigger] self.slots[i]).is_InProgress() && (#[trigger] self.slots[i]).get_InProgress_0() == elems[i as int].unwrap()
            },
        }
    }






    init!{
        initialize(num_threads: nat) {
            init num_threads = num_threads;

            init clients = Map::new(Set::range(0, num_threads), |i| ClientState::Idle);
            init slots = Map::new(Set::range(0, num_threads), |i| SlotState::Empty);

            init combiner = CombinerState::Collecting(Seq::empty());
        }
    }




    transition!{
        combiner_collect_empty() {
            require(pre.combiner.is_Collecting());

            let tid = pre.combiner.get_Collecting_0().len();

            have slots >= [ tid => let (SlotState::Empty { .. } | SlotState::Response { .. }) ];

            update combiner = CombinerState::Collecting(pre.combiner.get_Collecting_0().push(Option::None));
        }
    }


    transition!{
        combiner_collect_request() {
            require(pre.combiner.is_Collecting());

            let tid = pre.combiner.get_Collecting_0().len();

            remove slots -= [ tid => let SlotState::Request(rid) ];
            add    slots += [ tid => SlotState::InProgress(rid) ];

            update combiner = CombinerState::Collecting(pre.combiner.get_Collecting_0().push(Option::Some(rid)));
        }
    }


    property!{
        pre_combiner_collect_request() {
            require(pre.combiner.is_Collecting());
            let idx = pre.combiner.get_Collecting_0().len();
            require(idx < pre.num_threads);
            have slots >= [ idx => let slot_state ];

            assert(!slot_state.is_InProgress());
        }
    }



    transition!{
        combiner_responding_start() {
            require(pre.combiner.is_Collecting());
            require(pre.combiner.get_Collecting_0().len() == pre.num_threads);

            update combiner = CombinerState::Responding(pre.combiner.get_Collecting_0(), 0);
        }
    }

    transition!{
        combiner_responding_empty() {
            require(pre.combiner.is_Responding());
            let tid = pre.combiner.get_Responding_1();

            require(tid < pre.num_threads);
            require(pre.combiner.req_is_none(tid));

            update combiner = CombinerState::Responding(pre.combiner.get_Responding_0(), tid + 1);
        }
    }

    transition!{
        combiner_responding_result() {
            require(pre.combiner.is_Responding());

            let tid = pre.combiner.get_Responding_1();

            require(tid < pre.num_threads);
            require(!pre.combiner.req_is_none(tid));

            update combiner = CombinerState::Responding(pre.combiner.get_Responding_0(), tid + 1);
            remove slots -= [ tid => let r ];
            assert let SlotState::InProgress(rid) = r;
            assert pre.combiner.get_Responding_0()[tid as int].unwrap() == rid;
            add    slots += [ tid => SlotState::Response(rid) ];
        }
    }

    transition!{
        combiner_responding_done() {
            require(pre.combiner.is_Responding());
            require(pre.combiner.get_Responding_1() == pre.num_threads);

            update combiner = CombinerState::Collecting(Seq::empty());
        }
    }




    property!{
        pre_send_request(tid: ThreadId) {

            have clients >= [ tid => let ClientState::Idle ];
            have slots   >= [ tid => let slot_state ];

            assert(slot_state.is_Empty());
        }
    }

    transition!{
        send_request(tid: ThreadId, rid: ReqId) {
            remove clients -= [ tid => let ClientState::Idle ];
            add    clients += [ tid => ClientState::Waiting(rid) ];

            remove slots -= [ tid => let SlotState::Empty ];
            add    slots += [ tid => SlotState::Request(rid) ];
        }
    }

    property!{
        pre_recv_response(tid: ThreadId) {

            have clients >= [ tid => let ClientState::Waiting(rid) ];
            have slots   >= [ tid => let slot_state ];

            assert(!slot_state.is_Empty());
            assert(slot_state.get_ReqId() == rid);
        }
    }

    transition!{
        recv_response(tid: ThreadId, rid: ReqId) {
            remove clients -= [ tid => ClientState::Waiting(rid) ];
            add    clients += [ tid => ClientState::Idle ];

            remove slots -= [ tid => SlotState::Response(rid) ];
            add    slots += [ tid => SlotState::Empty ];
        }
    }




    #[inductive(initialize)]
    fn initialize_inductive(post: Self, num_threads: nat) { }

    #[inductive(combiner_collect_empty)]
    fn combiner_collect_empty_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_collect_request)]
    fn combiner_collect_request_inductive(pre: Self, post: Self) {
        match post.combiner {
            CombinerState::Collecting(elems) => {
                let idx = pre.combiner.get_Collecting_0().len();
                assert(forall |i: nat| 0 <= i < idx
                    ==> Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));
            },
            _ => {}
        }
    }

    #[inductive(combiner_responding_start)]
    fn combiner_responding_start_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_responding_empty)]
    fn combiner_responding_empty_inductive(pre: Self, post: Self) {
        match post.combiner {
            CombinerState::Responding(elems, idx) => {
                assert(!Self::slot_in_progress(pre.slots, (idx - 1) as nat));
            },
            _ => {}
        }
    }

    #[inductive(combiner_responding_result)]
    fn combiner_responding_result_inductive(pre: Self, post: Self) { }

    #[inductive(combiner_responding_done)]
    fn combiner_responding_done_inductive(pre: Self, post: Self) { }

    #[inductive(send_request)]
    fn send_request_inductive(pre: Self, post: Self, tid: ThreadId, rid: ReqId) {
        assert(Self::slot_in_progress(post.slots, tid) == Self::slot_in_progress(pre.slots, tid));
        assert(forall |i: nat| 0 <= i < post.num_threads
            ==> #[trigger] Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));

    }

    #[inductive(recv_response)]
    fn recv_response_inductive(pre: Self, post: Self, tid: ThreadId, rid: ReqId) {
        assert(Self::slot_in_progress(post.slots, tid) == Self::slot_in_progress(pre.slots, tid));
        assert(forall |i: nat| 0 <= i < post.num_threads
            ==> #[trigger] Self::slot_in_progress(post.slots, i) == Self::slot_in_progress(pre.slots, i));
    }

}}  


} 
}

pub mod rwlock {
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{multiset::*, prelude::*};

verus! {

tokenized_state_machine!{
    #[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(T))]
    RwLockSpec<T> {
        fields {
            #[sharding(constant)]
            pub user_inv: ISet<T>,

            #[sharding(constant)]
            pub rc_width: int,

            #[sharding(storage_option)]
            pub storage: Option<T>,

            #[sharding(variable)]
            pub exc_locked: bool,

            #[sharding(map)]
            pub ref_counts: Map<int, int>,

            #[sharding(option)]
            pub exc_pending: Option<int>,

            #[sharding(option)]
            pub exc_guard: Option<()>,

            #[sharding(multiset)]
            pub shared_pending: Multiset<int>,

            #[sharding(multiset)]
            pub shared_guard: Multiset<(int, T)>,
        }

        init!{
            initialize(rc_width: int, init_t: T, user_inv: ISet<T>,) {
                require(0 < rc_width);
                require(user_inv.contains(init_t));
                init rc_width = rc_width;
                init user_inv = user_inv;
                init storage = Option::Some(init_t);
                init exc_locked = false;
                init ref_counts = Map::new(
                    Set::range(0, rc_width),
                    |i| 0,
                );
                init exc_pending = Option::None;
                init exc_guard = Option::None;
                init shared_pending = Multiset::empty();
                init shared_guard = Multiset::empty();
            }
        }

        transition!{
            exc_start() {
                require(!pre.exc_locked);
                update exc_locked = true;
                add exc_pending += Some(0);
            }
        }

        transition!{
            exc_check_count() {
                remove exc_pending -= Some(let r);
                have ref_counts >= [r => 0];

                add exc_pending += Some(r + 1);
            }
        }

        transition!{
            exc_finish() {
                remove exc_pending -= Some(pre.rc_width);
                add exc_guard += Some(());

                birds_eye let x = pre.storage.unwrap();

                withdraw storage -= Some(x);
                assert(pre.user_inv.contains(x));
            }
        }

        transition!{
            exc_release(t: T) {
                require(pre.user_inv.contains(t));
                update exc_locked = false;
                remove exc_guard -= Some(());
                deposit storage += Some(t);
            }
        }

        transition!{
            shared_start(r: int) {
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc + 1];
                add shared_pending += {r};
            }
        }

        transition!{
            shared_abandon(r: int) {
                remove ref_counts -= [r => let rc];
                require(rc > 0);
                add ref_counts += [r => rc - 1];
                remove shared_pending -= {r};
            }
        }

        transition!{
            shared_finish(r: int) {
                require(!pre.exc_locked);
                remove shared_pending -= {r};

                birds_eye let t = pre.storage.unwrap();
                add shared_guard += {(r, t)};

                assert(pre.user_inv.contains(t));
            }
        }

        transition!{
            shared_release(val: (int, T)) {
                remove shared_guard -= {val};

                let r = val.0;
                remove ref_counts -= [r => let rc];
                add ref_counts += [r => rc - 1];

                assert(rc > 0) by {
                    assert(0 <= r < pre.rc_width);
                    assert(pre.shared_guard.count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).count(val) > 0);
                    assert(Self::filter_r(pre.shared_guard, r).len() > 0);
                    assert(pre.ref_counts.index(r) > 0);
                };
            }
        }

        property!{
            do_guard(val: (int, T)) {
                have shared_guard >= {val};
                guard storage >= Some(val.1);
            }
        }

        property!{
            rc_not_zero_guard(r: int) {
                have shared_pending >= {r};
                have ref_counts >= [r => let rc];
                assert(rc > 0);
            }
        }



        #[invariant]
        pub fn sto_user_inv(&self) -> bool {
            self.storage matches Some(storage) ==>
                self.user_inv.contains(storage)
        }

        #[invariant]
        pub fn ref_counts_domain(&self) -> bool {
            &&& 0 < self.rc_width
            &&& forall |i: int| 0 <= i < self.rc_width <==> self.ref_counts.dom().contains(i)
        }

        #[invariant]
        pub fn exc_inv(&self) -> bool {
            &&& self.exc_locked <==> (self.exc_pending.is_some() || self.exc_guard.is_some())
            &&& self.storage.is_some() <==> self.exc_guard.is_none()
            &&& if let Option::Some(cur_r) = self.exc_pending {
                &&& 0 <= cur_r <= self.rc_width
                &&& self.exc_guard.is_none()
                &&& forall |x| self.shared_guard.count(x) > 0 ==> !(0 <= x.0 < cur_r)
            } else {
                true
            }
        }

        #[invariant]
        pub fn shared_pending_in_range(&self) -> bool {
            forall |r| self.shared_pending.count(r) > 0 ==> (0 <= r < self.rc_width)
        }

        #[invariant]
        pub fn shared_guard_in_range(&self) -> bool {
            forall |x| self.shared_guard.count(x) > 0 ==> (0 <= x.0 < self.rc_width)
        }

        #[invariant]
        pub fn shared_inv_agree(&self) -> bool {
            forall |v| #[trigger] self.shared_guard.count(v) > 0 ==>
                self.storage === Option::Some(v.1)
        }

        pub closed spec fn filter_r(shared_guard: Multiset<(int, T)>, r: int) -> Multiset<(int, T)> {
            shared_guard.filter(|val: (int, T)| val.0 == r)
        }

        #[invariant]
        pub fn shared_counts_agree(&self) -> bool {
            forall |r| 0 <= r < self.rc_width ==>
                #[trigger] self.ref_counts.index(r) ==
                    self.shared_pending.count(r) as int +
                        Self::filter_r(self.shared_guard, r).len() as int
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, rc_width: int, init_t: T,  user_inv: ISet<T>) {
            assert forall |r| 0 <= r < post.rc_width implies
                #[trigger] post.ref_counts.index(r) ==
                    post.shared_pending.count(r) as int +
                        Self::filter_r(post.shared_guard, r).len() as int
            by {
                assert(post.ref_counts.index(r) == 0);
                assert(post.shared_pending.count(r) == 0);
                assert(Self::filter_r(post.shared_guard, r) =~= Multiset::empty());
                assert(Self::filter_r(post.shared_guard, r).len() == 0);
            }
            assert(post.shared_counts_agree());
        }

        #[inductive(exc_start)]
        fn exc_start_inductive(pre: Self, post: Self) {

        }

        #[inductive(exc_check_count)]
        fn exc_check_count_inductive(pre: Self, post: Self) {
            let prev_r = pre.exc_pending.unwrap();
            assert forall |x| #[trigger] post.shared_guard.count(x) > 0
                && x.0 == prev_r implies false
            by {
                assert(Self::filter_r(post.shared_guard, prev_r).count(x) > 0);
            }
        }

        #[inductive(exc_finish)]
        fn exc_finish_inductive(pre: Self, post: Self) {
        }

        #[inductive(exc_release)]
        fn exc_release_inductive(pre: Self, post: Self, t: T) {

        }

        #[inductive(shared_start)]
        fn shared_start_inductive(pre: Self, post: Self, r: int) { }

        #[inductive(shared_abandon)]
        fn shared_abandon_inductive(pre: Self, post: Self, r: int) { }

        #[inductive(shared_finish)]
        fn shared_finish_inductive(pre: Self, post: Self, r: int) {
            let t = pre.storage.unwrap();

            assert forall |r0| 0 <= r0 < post.rc_width implies
                #[trigger] post.ref_counts.index(r0) ==
                    post.shared_pending.count(r0) as int +
                        Self::filter_r(post.shared_guard, r0).len() as int
            by {
                if r == r0 {
                    assert(pre.shared_pending =~= post.shared_pending.add(Multiset::singleton(r)));
                    assert(Self::filter_r(post.shared_guard, r) =~= Self::filter_r(pre.shared_guard, r).add(Multiset::singleton((r, t))));
                    assert(post.ref_counts.index(r0) ==
                        post.shared_pending.count(r0) as int +
                            Self::filter_r(post.shared_guard, r0).len() as int);
                } else {
                    assert(Self::filter_r(post.shared_guard, r0) =~= Self::filter_r(pre.shared_guard, r0));
                    assert(post.ref_counts.index(r0) ==
                        post.shared_pending.count(r0) as int +
                            Self::filter_r(post.shared_guard, r0).len() as int);
                }
            }
        }

        #[inductive(shared_release)]
        fn shared_release_inductive(pre: Self, post: Self, val: (int, T)) {
            let r = val.0;
            assert forall |r0| 0 <= r0 < post.rc_width implies
                #[trigger] post.ref_counts.index(r0) ==
                    post.shared_pending.count(r0) as int +
                        Self::filter_r(post.shared_guard, r0).len() as int
            by {
                if r0 == r {
                    assert(Self::filter_r(pre.shared_guard, r) =~= Self::filter_r(post.shared_guard, r).add(Multiset::singleton(val)));
                } else {
                    assert(Self::filter_r(post.shared_guard, r0) =~= Self::filter_r(pre.shared_guard, r0));
                }
            }
        }
    }
}

} 
}
}

use crate::spec::simple_log::SimpleLog;
use crate::spec::unbounded_log::UnboundedLog;

pub use crate::exec::context::ThreadToken;
pub use crate::exec::NodeReplicated;

use crate::constants::MAX_REPLICAS;

verus! {

global size_of usize == 8;

pub type ReplicaId = usize;

pub type NodeId = nat;

pub type LogIdx = nat;

pub type ReqId = nat;

pub type ThreadId = nat;

#[verus::trusted]
proof fn theorem_1<DT: Dispatch + Sync>()
    ensures
        implements_SimpleLogRefinesAsynchronousSingleton::<
            DT,
            crate::spec::linearization::RefinementProof,
        >(),
{
}

#[verus::trusted]
proof fn theorem_2<DT: Dispatch + Sync>()
    ensures
        implements_UnboundedLogRefinesSimpleLog::<
            DT,
            crate::spec::unbounded_log_refines_simplelog::RefinementProof<DT>,
        >(),
{
}

#[verus::trusted]
proof fn theorem_3<DT: Dispatch + Sync>()
    ensures
        implements_NodeReplicated::<DT, NodeReplicated<DT>>(),
{
}

#[verus::trusted]
pub trait ThreadTokenT<DT: Dispatch, Replica> {
    spec fn wf(&self, replica: &Replica) -> bool;

    spec fn replica_id_spec(&self) -> nat;
}

#[verus::trusted]
pub trait Dispatch: Sized {
    type ReadOperation: Sized;

    type WriteOperation: Sized + Send;

    type Response: Sized;

    type View;

    spec fn view(&self) -> Self::View;

    fn init() -> (res: Self)
        ensures
            res@ == Self::init_spec(),
    ;

    fn clone_write_op(op: &Self::WriteOperation) -> (res: Self::WriteOperation)
        ensures
            op == res,
    ;

    fn clone_response(op: &Self::Response) -> (res: Self::Response)
        ensures
            op == res,
    ;

    fn dispatch(&self, op: Self::ReadOperation) -> (result: Self::Response)
        ensures
            Self::dispatch_spec(self@, op) == result,
    ;

    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> (result: Self::Response)
        ensures
            Self::dispatch_mut_spec(old(self)@, op) == (final(self)@, result),
    ;

    spec fn init_spec() -> Self::View;

    spec fn dispatch_spec(ds: Self::View, op: Self::ReadOperation) -> Self::Response;

    spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (
        Self::View,
        Self::Response,
    );
}

#[verifier(external_body)]             
#[verus::trusted]
pub struct AffinityFn {
    f: Box<dyn Fn(ReplicaId)>,
}

#[verus::trusted]
impl AffinityFn {
    #[verifier(external_body)]             
    pub fn new(f: impl Fn(ReplicaId) + 'static) -> Self {
        Self { f: Box::new(f) }
    }

    #[verifier(external_body)]             
    pub fn call(&self, rid: ReplicaId) {
        (self.f)(rid)
    }
}

#[verus::trusted]
pub trait NodeReplicatedT<DT: Dispatch + Sync>: Sized {
    type Replica;

    type ReplicaId;

    type TT: ThreadTokenT<DT, Self::Replica>;

    spec fn wf(&self) -> bool;

    spec fn replicas(&self) -> Vec<Box<Self::Replica>>;

    spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT>;

    fn new(num_replicas: usize, chg_mem_affinity: AffinityFn) -> (res: Self)
        requires
            0 < num_replicas && num_replicas <= MAX_REPLICAS,
        ensures
            res.wf() && res.replicas().len() == num_replicas,
    ;

    fn register(&mut self, replica_id: ReplicaId) -> (result: Option<Self::TT>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            result matches Some(r) ==> r.wf(&final(self).replicas()[replica_id as int]),
    ;

    fn execute_mut(
        &self,
        op: DT::WriteOperation,
        tkn: Self::TT,
        ticket: Tracked<UnboundedLog::local_updates<DT>>,
    ) -> (result: Result<
        (DT::Response, Self::TT, Tracked<UnboundedLog::local_updates<DT>>),
        (Self::TT, Tracked<UnboundedLog::local_updates<DT>>),
    >)
        requires
            self.wf(),  
            tkn.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            is_update_ticket(ticket@, op, self.unbounded_log_instance()),
        ensures
            result matches Ok(ok) ==> is_update_stub(
                ok.2@,
                ticket@.key(),
                ok.0,
                self.unbounded_log_instance(),
            ) && ok.1.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            result matches Err(err) ==> err == (tkn, ticket),
    ;

    fn execute(
        &self,
        op: DT::ReadOperation,
        tkn: Self::TT,
        ticket: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (result: Result<
        (DT::Response, Self::TT, Tracked<UnboundedLog::local_reads<DT>>),
        (Self::TT, Tracked<UnboundedLog::local_reads<DT>>),
    >)
        requires
            self.wf(),  
            tkn.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            is_readonly_ticket(ticket@, op, self.unbounded_log_instance()),
        ensures
            result matches Ok(ok) ==> is_readonly_stub(
                ok.2@,
                ticket@.key(),
                ok.0,
                self.unbounded_log_instance(),
            ) && ok.1.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            result matches Err(err) ==> err == (tkn, ticket),
    ;
}

#[verus::trusted]
spec fn implements_NodeReplicated<DT: Dispatch + Sync, N: NodeReplicatedT<DT>>() -> bool {
    true
}

#[verus::trusted]
pub open spec fn is_readonly_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_reads<DT>,
    op: DT::ReadOperation,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    &&& ticket.value().is_Init() && ticket.value().get_Init_op() == op

    &&& ticket.instance_id() == log.id()
}

#[verus::trusted]
pub open spec fn is_readonly_stub<DT: Dispatch>(
    stub: UnboundedLog::local_reads<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    &&& stub.instance_id() == log.id()

    &&& stub.key() == rid
    &&& stub.value().is_Done()
    &&& stub.value().get_Done_ret() == result
}

#[verus::trusted]
pub open spec fn is_update_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_updates<DT>,
    op: DT::WriteOperation,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    &&& ticket.value().is_Init() && ticket.value().get_Init_op() == op

    &&& ticket.instance_id() == log.id()
}

#[verus::trusted]
pub open spec fn is_update_stub<DT: Dispatch>(
    stub: UnboundedLog::local_updates<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    &&& stub.instance_id() == log.id()

    &&& stub.key() == rid
    &&& stub.value().is_Done()
    &&& stub.value().get_Done_ret() == result
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
                    crate::spec::unbounded_log::ReadonlyState::Init { op: read_op },
                ),
                ..pre
            }
        },
        InputOperation::Write(write_op) => {
            post == UnboundedLog::State::<DT> {
                local_updates: pre.local_updates.insert(
                    rid,
                    crate::spec::unbounded_log::UpdateState::Init { op: write_op },
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

#[verus::trusted]
trait UnboundedLogRefinesSimpleLog<DT: Dispatch> {
    spec fn interp(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT>;

    spec fn get_fresh_rid(pre: UnboundedLog::State<DT>) -> ReqId;

    proof fn fresh_rid_is_ok(pre: UnboundedLog::State<DT>)
        requires
            pre.invariant(),
        ensures
            !pre.local_reads.dom().contains(Self::get_fresh_rid(pre)),
            !pre.local_updates.dom().contains(Self::get_fresh_rid(pre)),
    ;

    proof fn refinement_inv(vars: UnboundedLog::State<DT>)
        requires
            vars.invariant(),
        ensures
            Self::interp(vars).invariant(),
    ;

    proof fn refinement_init(post: UnboundedLog::State<DT>)
        requires
            post.invariant(),
            UnboundedLog::State::init(post),
        ensures
            SimpleLog::State::init(Self::interp(post)),
    ;

    proof fn refinement_next(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>)
        requires
            pre.invariant(),
            post.invariant(),
            UnboundedLog::State::next_strong(pre, post),
        ensures
            SimpleLog::State::next(Self::interp(pre), Self::interp(post), AsyncLabel::Internal),
    ;

    proof fn refinement_add_ticket(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: InputOperation<DT>,
    )
        requires
            pre.invariant(),
            add_ticket(pre, post, input, Self::get_fresh_rid(pre)),
        ensures
            post.invariant(),
            SimpleLog::State::next(
                Self::interp(pre),
                Self::interp(post),
                AsyncLabel::Start(Self::get_fresh_rid(pre), input),
            ),
    ;

    proof fn refinement_consume_stub(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: OutputOperation<DT>,
        rid: ReqId,
    )
        requires
            pre.invariant(),
            consume_stub(pre, post, output, rid),
        ensures
            post.invariant(),
            SimpleLog::State::next(
                Self::interp(pre),
                Self::interp(post),
                AsyncLabel::End(rid, output),
            ),
    ;
}

#[verus::trusted]
spec fn implements_UnboundedLogRefinesSimpleLog<
    DT: Dispatch,
    RP: UnboundedLogRefinesSimpleLog<DT>,
>() -> bool {
    true
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

#[is_variant]
#[verus::trusted]
pub enum AsyncLabel<DT: Dispatch> {
    Internal,
    Start(ReqId, InputOperation<DT>),
    End(ReqId, OutputOperation<DT>),
}

state_machine!{ AsynchronousSingleton<DT: Dispatch> {           
    fields {                                                    
        pub state: DT::View,                                    
        pub reqs: Map<ReqId, InputOperation<DT>>,               
        pub resps: Map<ReqId, OutputOperation<DT>>,             
    }                                                           

    pub type Label<DT> = AsyncLabel<DT>;                        

    init!{                                                      
        initialize() {                                          
            init state = DT::init_spec();                       
            init reqs = Map::empty();                           
            init resps = Map::empty();                          
        }                                                       
    }                                                           

    transition!{                                                
        internal_next(label: Label<DT>, rid: ReqId, input: InputOperation<DT>, output: OutputOperation<DT>) {   
            require label.is_Internal();                     
            require pre.reqs.dom().contains(rid);            
            require pre.reqs[rid] == input;                  
            update reqs = pre.reqs.remove(rid);              
            update resps = pre.resps.insert(rid, output);    

            match input {                                    
                InputOperation::Read(read_op) => {           
                    require output === OutputOperation::Read(DT::dispatch_spec(pre.state, read_op));  
                }                                                                           
                InputOperation::Write(write_op) => {                                        
                    let (next_state, out) = DT::dispatch_mut_spec(pre.state, write_op);     
                    require output === OutputOperation::Write(out);                         
                    update state = next_state;                                              
                }                                                                           
            }                                                                               
        }                                                                                   
    }                                                                                       

    transition!{                                        
        no_op(label: Label<DT>) {                       
            require label.is_Internal();                
        }                                               
    }                                                   

    transition!{                                                            
        start(label: Label<DT>, rid: ReqId, input: InputOperation<DT>) {    
            require label == AsyncLabel::<DT>::Start(rid, input);           
            require !pre.reqs.dom().contains(rid);                          
            update reqs = pre.reqs.insert(rid, input);                      
        }                                                                   
    }                                                                       

    transition!{                                                            
        end(label: Label<DT>, rid: ReqId, output: OutputOperation<DT>) {    
            require label == AsyncLabel::<DT>::End(rid, output);            
            require pre.resps.dom().contains(rid);                          
            require pre.resps[rid] == output;                               
            update resps = pre.resps.remove(rid);                           
        }                                                                   
    }                                                                       
}}  


#[is_variant]
#[verus::trusted]
pub enum SimpleLogBehavior<DT: Dispatch> {
    Stepped(SimpleLog::State<DT>, AsyncLabel<DT>, Box<SimpleLogBehavior<DT>>),
    Inited(SimpleLog::State<DT>),
}

#[verus::trusted]
impl<DT: Dispatch> SimpleLogBehavior<DT> {
    pub open spec fn get_last(self) -> SimpleLog::State<DT> {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => post,
            SimpleLogBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => {
                tail.wf() && SimpleLog::State::next(tail.get_last(), post, op)
            },
            SimpleLogBehavior::Inited(post) => { SimpleLog::State::init(post) },
        }
    }
}

#[is_variant]
#[verus::trusted]
pub enum AsynchronousSingletonBehavior<DT: Dispatch> {
    Stepped(
        AsynchronousSingleton::State<DT>,
        AsyncLabel<DT>,
        Box<AsynchronousSingletonBehavior<DT>>,
    ),
    Inited(AsynchronousSingleton::State<DT>),
}

#[verus::trusted]
impl<DT: Dispatch> AsynchronousSingletonBehavior<DT> {
    pub open spec fn get_last(self) -> AsynchronousSingleton::State<DT> {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => post,
            AsynchronousSingletonBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => {
                tail.wf() && AsynchronousSingleton::State::next(tail.get_last(), post, op)
            },
            AsynchronousSingletonBehavior::Inited(post) => {
                AsynchronousSingleton::State::init(post)
            },
        }
    }
}

#[verus::trusted]
pub open spec fn behavior_equiv<DT: Dispatch>(
    a: SimpleLogBehavior<DT>,
    b: AsynchronousSingletonBehavior<DT>,
) -> bool
    decreases a, b,
{
    ||| (a.is_Inited()
        && b.is_Inited())

    ||| (a.is_Stepped() && a.get_Stepped_1().is_Internal() && behavior_equiv(
        *a.get_Stepped_2(),
        b,
    ))

    ||| (b.is_Stepped() && b.get_Stepped_1().is_Internal() && behavior_equiv(
        a,
        *b.get_Stepped_2(),
    ))

    ||| (a.is_Stepped() && b.is_Stepped() && a.get_Stepped_1() == b.get_Stepped_1()
        && behavior_equiv(*a.get_Stepped_2(), *b.get_Stepped_2()))
}

#[verus::trusted]
trait SimpleLogRefinesAsynchronousSingleton<DT: Dispatch> {
    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<
        DT,
    >)
        requires
            a.wf(),
        ensures
            b.wf() && behavior_equiv(a, b),
    ;
}

#[verus::trusted]
spec fn implements_SimpleLogRefinesAsynchronousSingleton<
    DT: Dispatch,
    RP: SimpleLogRefinesAsynchronousSingleton<DT>,
>() -> bool {
    true
}

} 

fn main() {}
