# Verus Proof-Repair Task Manifest

This document catalogues the 53 Verus proof-repair tasks used in the thesis
evaluation. It describes the corpus snapshot and task definitions only;
experimental outcomes, costs, and durations are recorded separately in
[`runs/`](runs/).

## Provenance and task contract

- Repository: [`dybolo/verus-agent-benchmark`](https://github.com/dybolo/verus-agent-benchmark)
- Corpus snapshot: commit [`5797cd0242a268248797a76da5951b367e5c80eb`](https://github.com/dybolo/verus-agent-benchmark/commit/5797cd0242a268248797a76da5951b367e5c80eb)
- Tasks: 53 standalone Rust files in [`tasks/`](tasks/)
- Reference proofs: the corresponding fully verified files in
  [`solutions/base/`](solutions/base/)

[Verus]: https://github.com/verus-lang/verus
[vostd]: https://github.com/asterinas/vostd
[verified-node-replication]: https://github.com/verus-lang/verified-node-replication

Each task contains one designated incomplete proof obligation. The benchmark
prompt requires a solver to add only proof annotations: it must preserve
executable code and existing contracts, must not introduce `admit(...)` or
`assume(...)`, and must preserve existing admits and unrelated proof holes.
Successful solutions are checked with Verus and the Lynette change checker.

Tasks are classified by the feature exercised by the **designated proof
obligation**, rather than every feature used elsewhere in the enclosing source
file. In particular, Cuckoo and FIFO files contain both atomic ghost operations
and tokenized state machines. Cuckoo read/insert/delete tasks require completing
atomic-ghost proof sections, whereas Cuckoo's inductive task and all FIFO tasks
require tokenized-state-machine inductiveness proofs.

## Task-group overview

| Task group | Tasks | Proof style | Source families |
| --- | ---: | --- | --- |
| Atomic-operation proofs | 21 | Complete ghost reasoning around a concrete atomic operation, either with `atomic_with_ghost!` or by opening an invariant with `open_atomic_invariant!`. | Count-to-Two, Cuckoo, Helping, Once, RwLock, statics, wait queue |
| `tokenized_state_machine!` | 32 | Prove that a state-machine transition preserves its invariants. | Cuckoo, CyclicBuffer, distributed RwLock, FIFO, Flat Combining, Unbounded Log |

## Atomic-operation proof tasks (21)

| Task ID | Description | Target proof obligation | Source project | Source module | Task file |
| --- | --- | --- | --- | --- | --- |
| `cuckoo_delete` | Delete a key/value entry while synchronizing ghost state with the atomic update. | Atomic-ghost proof in `MyHashMap::delete` | [Verus](https://github.com/verus-lang/verus) | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_delete.rs`](tasks/cuckoo_delete.rs) |
| `cuckoo_insert` | Insert a key/value entry while synchronizing ghost state with the atomic update. | Atomic-ghost proof in `MyHashMap::insert` | [Verus](https://github.com/verus-lang/verus) | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_insert.rs`](tasks/cuckoo_insert.rs) |
| `cuckoo_read` | Read a key/value entry while maintaining the atomic ghost-state correspondence. | Atomic-ghost proof in `MyHashMap::read` | [Verus](https://github.com/verus-lang/verus) | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_read.rs`](tasks/cuckoo_read.rs) |
| `once_get` | Read an optionally initialized value while recovering the correct ghost permission. | Atomic-ghost proof in `OnceImpl::get` | [vostd](https://github.com/asterinas/vostd) | [`once.rs`](solutions/base/once.rs) | [`once_get.rs`](tasks/once_get.rs) |
| `once_init` | Initialize a one-time cell and establish its initialized ghost state. | Atomic-ghost proof in `OnceImpl::init` | [vostd](https://github.com/asterinas/vostd) | [`once.rs`](solutions/base/once.rs) | [`once_init.rs`](tasks/once_init.rs) |
| `rwlock_readguard_drop` | Release a read guard and return its shared-read resources. | Atomic-ghost proof in `RwLockReadGuard::drop` | [vostd](https://github.com/asterinas/vostd) | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_readguard_drop.rs`](tasks/rwlock_readguard_drop.rs) |
| `rwlock_try_read` | Attempt to acquire a read guard while updating reader-count ghost state. | Atomic-ghost proof in `RwLock::try_read` | [vostd](https://github.com/asterinas/vostd) | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_try_read.rs`](tasks/rwlock_try_read.rs) |
| `rwlock_try_upgrade` | Upgrade an upgradeable read guard to a write guard atomically. | Atomic-ghost proof in `RwLockUpgradeableGuard::try_upgrade` | [vostd](https://github.com/asterinas/vostd) | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_try_upgrade.rs`](tasks/rwlock_try_upgrade.rs) |
| `rwlock_try_upread` | Attempt to acquire an upgradeable read guard. | Atomic-ghost proof in `RwLock::try_upread` | [vostd](https://github.com/asterinas/vostd) | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_try_upread.rs`](tasks/rwlock_try_upread.rs) |
| `rwlock_try_write` | Attempt to acquire a write guard while preserving lock ownership state. | Atomic-ghost proof in `RwLock::try_write` | [vostd](https://github.com/asterinas/vostd) | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_try_write.rs`](tasks/rwlock_try_write.rs) |
| `rwlock_upgradableguard_drop` | Release an upgradeable read guard and restore its permissions. | Atomic-ghost proof in `RwLockUpgradeableGuard::drop` | [vostd](https://github.com/asterinas/vostd) | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_upgradableguard_drop.rs`](tasks/rwlock_upgradableguard_drop.rs) |
| `rwlock_writeguard_drop` | Release a write guard and restore the lock's writable state. | Atomic-ghost proof in `RwLockWriteGuard::drop` | [vostd](https://github.com/asterinas/vostd) | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_writeguard_drop.rs`](tasks/rwlock_writeguard_drop.rs) |
| `statics_get` | Lazily initialize and retrieve a static value. | Atomic-ghost proof in `Lazy::get` | [Verus](https://github.com/verus-lang/verus) | [`statics.rs`](solutions/base/statics.rs) | [`statics_get.rs`](tasks/statics_get.rs) |
| `wait_enqueue` | Enqueue a waiter while keeping the atomic queue-length mirror consistent. | Atomic-ghost proof in `WaitQueue::enqueue` | [vostd](https://github.com/asterinas/vostd) | [`wait.rs`](solutions/base/wait.rs) | [`wait_enqueue.rs`](tasks/wait_enqueue.rs) |
| `wait_wake_all` | Wake all queued waiters while decrementing the mirrored count. | Atomic-ghost proof in `WaitQueue::wake_all` | [vostd](https://github.com/asterinas/vostd) | [`wait.rs`](solutions/base/wait.rs) | [`wait_wake_all.rs`](tasks/wait_wake_all.rs) |
| `wait_wake_one` | Wake one queued waiter while decrementing the mirrored count. | Atomic-ghost proof in `WaitQueue::wake_one` | [vostd](https://github.com/asterinas/vostd) | [`wait.rs`](solutions/base/wait.rs) | [`wait_wake_one.rs`](tasks/wait_wake_one.rs) |
| `count_to_two_read_x` | Read the shared counter after both one-shot events have completed. | Logical-atomic proof in `CounterSharedState::read_x` | [Verus](https://github.com/verus-lang/verus) | [`count_to_two.rs`](solutions/base/count_to_two.rs) | [`count_to_two_read_x.rs`](tasks/count_to_two_read_x.rs) |
| `count_to_two_thread_routine` | Increment the counter and complete the caller's one-shot event. | Logical-atomic proof in `thread_routine` | [Verus](https://github.com/verus-lang/verus) | [`count_to_two.rs`](solutions/base/count_to_two.rs) | [`count_to_two_thread_routine.rs`](tasks/count_to_two_thread_routine.rs) |
| `helping_try_cancel_two_flips` | Cancel two pending flip operations through the helping protocol. | Logical-atomic proof in `try_cancel_two_flips` | [Verus](https://github.com/verus-lang/verus) | [`helping.rs`](solutions/base/helping.rs) | [`helping_try_cancel_two_flips.rs`](tasks/helping_try_cancel_two_flips.rs) |
| `helping_try_handshake` | Complete a handshake in the helping protocol. | Logical-atomic proof in `try_handshake` | [Verus](https://github.com/verus-lang/verus) | [`helping.rs`](solutions/base/helping.rs) | [`helping_try_handshake.rs`](tasks/helping_try_handshake.rs) |
| `helping_try_simple_flip` | Complete a simple flip in the helping protocol. | Logical-atomic proof in `try_simple_flip` | [Verus](https://github.com/verus-lang/verus) | [`helping.rs`](solutions/base/helping.rs) | [`helping_try_simple_flip.rs`](tasks/helping_try_simple_flip.rs) |

## `tokenized_state_machine!` tasks (32)

| Task ID | Description | Target proof obligation | Source project | Source module | Task file |
| --- | --- | --- | --- | --- | --- |
| `cuckoo_inductive` | Establish a Cuckoo state-machine transition invariant. | Cuckoo transition inductiveness proof | [Verus] | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_inductive.rs`](tasks/cuckoo_inductive.rs) |
| `cyclicbuffer_advance_head_finish_inductive` | Show that finishing head advancement preserves CyclicBuffer invariants. | `advance_head_finish_inductive` | [verified-node-replication] | [`cyclicbuffer.rs`](solutions/base/cyclicbuffer.rs) | [`cyclicbuffer_advance_head_finish_inductive.rs`](tasks/cyclicbuffer_advance_head_finish_inductive.rs) |
| `cyclicbuffer_advance_tail_finish_inductive` | Show that finishing tail advancement preserves CyclicBuffer invariants. | `advance_tail_finish_inductive` | [verified-node-replication] | [`cyclicbuffer.rs`](solutions/base/cyclicbuffer.rs) | [`cyclicbuffer_advance_tail_finish_inductive.rs`](tasks/cyclicbuffer_advance_tail_finish_inductive.rs) |
| `cyclicbuffer_advance_tail_start_inductive` | Show that starting tail advancement preserves CyclicBuffer invariants. | `advance_tail_start_inductive` | [verified-node-replication] | [`cyclicbuffer.rs`](solutions/base/cyclicbuffer.rs) | [`cyclicbuffer_advance_tail_start_inductive.rs`](tasks/cyclicbuffer_advance_tail_start_inductive.rs) |
| `cyclicbuffer_append_flip_bit_inductive` | Show that appending and flipping a bit preserves CyclicBuffer invariants. | `append_flip_bit_inductive` | [verified-node-replication] | [`cyclicbuffer.rs`](solutions/base/cyclicbuffer.rs) | [`cyclicbuffer_append_flip_bit_inductive.rs`](tasks/cyclicbuffer_append_flip_bit_inductive.rs) |
| `cyclicbuffer_reader_finish_inductive` | Show that finishing a reader operation preserves CyclicBuffer invariants. | `reader_finish_inductive` | [verified-node-replication] | [`cyclicbuffer.rs`](solutions/base/cyclicbuffer.rs) | [`cyclicbuffer_reader_finish_inductive.rs`](tasks/cyclicbuffer_reader_finish_inductive.rs) |
| `cyclicbuffer_reader_guard_inductive` | Show that granting a reader guard preserves CyclicBuffer invariants. | `reader_guard_inductive` | [verified-node-replication] | [`cyclicbuffer.rs`](solutions/base/cyclicbuffer.rs) | [`cyclicbuffer_reader_guard_inductive.rs`](tasks/cyclicbuffer_reader_guard_inductive.rs) |
| `dist_rwlock_exc_check_count_inductive` | Show that the exclusive-lock count check preserves distributed RwLock invariants. | `exc_check_count_inductive` | [Verus] | [`dist_rwlock.rs`](solutions/base/dist_rwlock.rs) | [`dist_rwlock_exc_check_count_inductive.rs`](tasks/dist_rwlock_exc_check_count_inductive.rs) |
| `dist_rwlock_initialize_inductive` | Establish the distributed RwLock initial state invariants. | `initialize_inductive` | [Verus] | [`dist_rwlock.rs`](solutions/base/dist_rwlock.rs) | [`dist_rwlock_initialize_inductive.rs`](tasks/dist_rwlock_initialize_inductive.rs) |
| `dist_rwlock_shared_finish_inductive` | Show that completing shared acquisition preserves distributed RwLock invariants. | `shared_finish_inductive` | [Verus] | [`dist_rwlock.rs`](solutions/base/dist_rwlock.rs) | [`dist_rwlock_shared_finish_inductive.rs`](tasks/dist_rwlock_shared_finish_inductive.rs) |
| `dist_rwlock_shared_release_inductive` | Show that releasing a shared lock preserves distributed RwLock invariants. | `shared_release_inductive` | [Verus] | [`dist_rwlock.rs`](solutions/base/dist_rwlock.rs) | [`dist_rwlock_shared_release_inductive.rs`](tasks/dist_rwlock_shared_release_inductive.rs) |
| `fifo_consume_end_inductive` | Show that ending consumer reservation preserves FIFO state-machine invariants. | `consume_end_inductive` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_consume_end_inductive.rs`](tasks/fifo_consume_end_inductive.rs) |
| `fifo_consume_start_inductive` | Show that starting consumer reservation preserves FIFO state-machine invariants. | `consume_start_inductive` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_consume_start_inductive.rs`](tasks/fifo_consume_start_inductive.rs) |
| `fifo_dequeue` | Prove the FIFO dequeue operation respects the state-machine invariants. | State-machine proof for `dequeue` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_dequeue.rs`](tasks/fifo_dequeue.rs) |
| `fifo_enqueue` | Prove the FIFO enqueue operation respects the state-machine invariants. | State-machine proof for `enqueue` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_enqueue.rs`](tasks/fifo_enqueue.rs) |
| `fifo_initialize_inductive` | Establish the FIFO queue's initial state-machine invariants. | `initialize_inductive` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_initialize_inductive.rs`](tasks/fifo_initialize_inductive.rs) |
| `fifo_produce_end_inductive` | Show that ending producer reservation preserves FIFO state-machine invariants. | `produce_end_inductive` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_produce_end_inductive.rs`](tasks/fifo_produce_end_inductive.rs) |
| `fifo_produce_start_inductive` | Show that starting producer reservation preserves FIFO state-machine invariants. | `produce_start_inductive` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_produce_start_inductive.rs`](tasks/fifo_produce_start_inductive.rs) |
| `flat_combine_client_recv_inductive` | Show that receiving a client response preserves Flat Combining invariants. | `client_recv_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_client_recv_inductive.rs`](tasks/flat_combine_client_recv_inductive.rs) |
| `flat_combine_client_send_inductive` | Show that sending a client request preserves Flat Combining invariants. | `client_send_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_client_send_inductive.rs`](tasks/flat_combine_client_send_inductive.rs) |
| `flat_combine_combiner_go_to_collecting_inductive` | Show that moving the combiner to collecting preserves invariants. | `combiner_go_to_collecting_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_combiner_go_to_collecting_inductive.rs`](tasks/flat_combine_combiner_go_to_collecting_inductive.rs) |
| `flat_combine_combiner_go_to_responding_inductive` | Show that moving the combiner to responding preserves invariants. | `combiner_go_to_responding_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_combiner_go_to_responding_inductive.rs`](tasks/flat_combine_combiner_go_to_responding_inductive.rs) |
| `flat_combine_combiner_recv_inductive` | Show that receiving a combiner request preserves invariants. | `combiner_recv_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_combiner_recv_inductive.rs`](tasks/flat_combine_combiner_recv_inductive.rs) |
| `flat_combine_combiner_send_inductive` | Show that sending a combiner response preserves invariants. | `combiner_send_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_combiner_send_inductive.rs`](tasks/flat_combine_combiner_send_inductive.rs) |
| `flat_combine_combiner_send_skip_inductive` | Show that skipping a combiner send preserves invariants. | `combiner_send_skip_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_combiner_send_skip_inductive.rs`](tasks/flat_combine_combiner_send_skip_inductive.rs) |
| `flat_combine_combiner_skip_inductive` | Show that skipping a combiner step preserves invariants. | `combiner_skip_inductive` | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_combiner_skip_inductive.rs`](tasks/flat_combine_combiner_skip_inductive.rs) |
| `unbounded_log_exec_dispatch_local_inductive` | Show that local dispatch preserves Unbounded Log invariants. | `exec_dispatch_local_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_exec_dispatch_local_inductive.rs`](tasks/unbounded_log_exec_dispatch_local_inductive.rs) |
| `unbounded_log_exec_trivial_start_inductive` | Show that starting trivial execution preserves Unbounded Log invariants. | `exec_trivial_start_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_exec_trivial_start_inductive.rs`](tasks/unbounded_log_exec_trivial_start_inductive.rs) |
| `unbounded_log_exec_update_version_upper_bound_inductive` | Show that updating the version upper bound preserves Unbounded Log invariants. | `exec_update_version_upper_bound_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_exec_update_version_upper_bound_inductive.rs`](tasks/unbounded_log_exec_update_version_upper_bound_inductive.rs) |
| `unbounded_log_readonly_apply_inductive` | Show that applying a read-only request preserves Unbounded Log invariants. | `readonly_apply_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_readonly_apply_inductive.rs`](tasks/unbounded_log_readonly_apply_inductive.rs) |
| `unbounded_log_update_done_inductive` | Show that completing an update preserves Unbounded Log invariants. | `update_done_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_update_done_inductive.rs`](tasks/unbounded_log_update_done_inductive.rs) |
| `unbounded_log_update_place_ops_in_log_one_inductive` | Show that placing an update operation in the log preserves Unbounded Log invariants. | `update_place_ops_in_log_one_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_update_place_ops_in_log_one_inductive.rs`](tasks/unbounded_log_update_place_ops_in_log_one_inductive.rs) |
