# Verus Proof-Repair Task Manifest

This document catalogues the 75 focused Verus proof-repair tasks and the 17
full-file tasks. It describes the corpus snapshot and task definitions only;
experimental outcomes, costs, and durations are recorded separately in
[`runs/`](runs/).

## Provenance and task contract

- Repository: [`dybolo/verus-agent-benchmark`](https://github.com/dybolo/verus-agent-benchmark)
- Original corpus snapshot: commit [`52efc533a234df3d534b53acdb3888cb60d765d1`](https://github.com/dybolo/verus-agent-benchmark/commit/52efc533a234df3d534b53acdb3888cb60d765d1)
- Focused tasks: 75 standalone Rust files in [`tasks/`](tasks/)
- Full-file tasks: 17 standalone Rust files in [`full_tasks/`](full_tasks/)
- Reference proofs: the corresponding fully verified files in
  [`solutions/base/`](solutions/base/)

[Verus]: https://github.com/verus-lang/verus
[vostd]: https://github.com/asterinas/vostd
[verified-node-replication]: https://github.com/verus-lang/verified-node-replication
[verified-memory-allocator]: https://github.com/verus-lang/verified-memory-allocator

Each focused task contains a designated repair scope, usually one function.
`cuckoo_inductive` covers four transition-inductiveness proofs, and the unified
`wait` task covers the three queue operations. A
full-file task instead removes the repair annotations for all selected proof
obligations in one source module, so a solver must repair the module as a
whole. The benchmark prompt requires a solver to add only proof annotations:
it must preserve executable code and existing contracts, must not introduce
`admit(...)` or `assume(...)`, and must preserve existing admits and unrelated
proof holes.
Successful solutions are checked with Verus and the Lynette change checker.

Tasks are classified by the feature exercised by the **designated proof
obligation**, rather than every feature used elsewhere in the enclosing source
file. In particular, Cuckoo and FIFO files contain both atomic ghost operations
and tokenized state machines. Cuckoo read/insert/delete and FIFO enqueue/dequeue
tasks require completing atomic-ghost proof sections, whereas Cuckoo's inductive
task and FIFO's inductive tasks require tokenized-state-machine inductiveness
proofs.

## Task-group overview

| Task group | Tasks | Proof style | Source families |
| --- | ---: | --- | --- |
| Atomic-operation proofs | 42 | Complete ghost reasoning around a concrete atomic operation, either with `atomic_with_ghost!` or by opening an invariant with `open_atomic_invariant!`. | Context, Count-to-Two, Cuckoo, FIFO, Helping, Log, Once, Replica, RwLock, statics, verified memory allocator, wait queue |
| `tokenized_state_machine!` | 33 | Prove that a state-machine transition preserves its invariants. | Cuckoo, CyclicBuffer, distributed RwLock, FIFO, Flat Combining, Unbounded Log, verified memory allocator |
| Full-file repairs | 17 | Repair all selected missing proof annotations in a self-contained source module; a file may combine both focused proof styles and auxiliary proof lemmas. | Context, Count-to-Two, Cuckoo, CyclicBuffer, distributed RwLock, FIFO, Flat Combining, Helping, Log, Once, Replica, RwLock, Unbounded Log, verified memory allocator |

The focused and full-file groups are separate benchmark modes, not 92
independent obligations. Run the focused corpus with `python3 benchmark.py`
and the full-file corpus with
`python3 benchmark.py --task-directory full_tasks`. Agent/model filters and
parallelism flags apply to either mode. A valid repair must pass both the Verus
check (`--rlimit 30`) and the Lynette change checker; a completed attempt alone
does not establish success.

## Follow-up task sets

Two smaller sets select tasks for follow-up runs based on earlier results. They
reuse IDs from the main corpus and do not add new task IDs to the manifest.

| Directory | Count | Task IDs |
| --- | ---: | --- |
| [`tasks_2/`](tasks_2/) | 7 | `free_free_block_mt`, `helping_try_handshake`, `log_append`, `rwlock_readguard_drop`, `rwlock_try_read`, `rwlock_try_upgrade`, `rwlock_try_upread` |
| [`full_tasks_2/`](full_tasks_2/) | 7 | `cuckoo_full`, `cyclicbuffer_full`, `free_full`, `helping_full`, `linked_list_full`, `log_full`, `rwlock_full` |

Select these with `--task-directory tasks_2` or
`--task-directory full_tasks_2`. The tables below describe the main `tasks/` and
`full_tasks/` corpora.

## Task metadata

The dashboard reads all 92 task IDs from
[`task_metadata.csv`](streamlit_app/src/streamlit_app/task_metadata.csv).
Its columns describe the designated repair scope:

| Column | Meaning |
| --- | --- |
| `task_id` | Task filename without `.rs`, including `_full` for full-file tasks. |
| `proof_style` | `atomic-operation`, `tokenized_state_machine!`, or `full-file`. |
| `source_module` | Reference filename under `solutions/base/`. |
| `method_lines` | Nonempty reference lines in the explicitly selected function ranges, including signatures, contracts, and delimiters; summed for tasks with multiple targets. |
| `atomic_operations` | Textual occurrences of `atomic_with_ghost!`, `open_atomic_invariant!`, and `try_open_atomic_update!` within those ranges. |
| `missing_code_lines` | Nonempty reference lines absent from the task within those ranges; replacement lines are subtracted per diff block, with a minimum of zero. Unrelated omitted functions are excluded. |

These line counts include any comments still present and delimiter-only lines.
They measure the reference repair scope, not the number of lines an agent must
produce or runtime atomic operations. The canonical metadata uses `tasks/` and
`full_tasks/`, rather than recalculating sizes from the follow-up sets.

Regenerate all three numeric columns with:

```bash
python3 scripts/update_task_method_sizes.py
```

The updater uses validated, inclusive reference-function ranges in its
`TASK_SPECS`; changes to source layout require updating those ranges. The legacy
`scripts/update_task_missing_lines.py` command invokes the same updater.

## Full-file proof tasks (17)

The `_full` suffix is part of each task ID. Unlike the focused files below,
these tasks can contain multiple missing proof bodies or proof blocks. Their
reference proof is the corresponding module in [`solutions/base/`](solutions/base/).

| Task ID | Scope | Source project | Source module | Task file |
| --- | --- | --- | --- | --- |
| `context_full` | Repair the complete client context module. | [verified-node-replication] | [`context.rs`](solutions/base/context.rs) | [`context_full.rs`](full_tasks/context_full.rs) |
| `count_to_two_full` | Repair the complete Count-to-Two logical-atomic example. | [Verus] | [`count_to_two.rs`](solutions/base/count_to_two.rs) | [`count_to_two_full.rs`](full_tasks/count_to_two_full.rs) |
| `cuckoo_full` | Repair the complete Cuckoo hash-map module, including its state-machine and atomic proofs. | [Verus] | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_full.rs`](full_tasks/cuckoo_full.rs) |
| `cyclicbuffer_full` | Repair all selected CyclicBuffer invariant-preservation proofs. | [verified-node-replication] | [`cyclicbuffer.rs`](solutions/base/cyclicbuffer.rs) | [`cyclicbuffer_full.rs`](full_tasks/cyclicbuffer_full.rs) |
| `dist_rwlock_full` | Repair the complete distributed RwLock state-machine proof. | [Verus] | [`dist_rwlock.rs`](solutions/base/dist_rwlock.rs) | [`dist_rwlock_full.rs`](full_tasks/dist_rwlock_full.rs) |
| `fifo_full` | Repair the complete FIFO module, including its state-machine and atomic proofs. | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_full.rs`](full_tasks/fifo_full.rs) |
| `flat_combine_full` | Repair all selected Flat Combining invariant-preservation proofs. | [verified-node-replication] | [`flat_combine.rs`](solutions/base/flat_combine.rs) | [`flat_combine_full.rs`](full_tasks/flat_combine_full.rs) |
| `free_full` | Repair the complete allocator free-path proof. | [verified-memory-allocator] | [`free.rs`](solutions/base/free.rs) | [`free_full.rs`](full_tasks/free_full.rs) |
| `helping_full` | Repair the complete logical-atomic helping example. | [Verus] | [`helping.rs`](solutions/base/helping.rs) | [`helping_full.rs`](full_tasks/helping_full.rs) |
| `linked_list_full` | Repair the complete allocator linked-list module. | [verified-memory-allocator] | [`linked_list.rs`](solutions/base/linked_list.rs) | [`linked_list_full.rs`](full_tasks/linked_list_full.rs) |
| `log_full` | Repair the complete replicated-log module. | [verified-node-replication] | [`log.rs`](solutions/base/log.rs) | [`log_full.rs`](full_tasks/log_full.rs) |
| `once_full` | Repair the complete one-time initialization module. | [vostd] | [`once.rs`](solutions/base/once.rs) | [`once_full.rs`](full_tasks/once_full.rs) |
| `replica_full` | Repair the complete node-replica module. | [verified-node-replication] | [`replica.rs`](solutions/base/replica.rs) | [`replica_full.rs`](full_tasks/replica_full.rs) |
| `rwlock_full` | Repair the complete concurrent RwLock module. | [vostd] | [`rwlock.rs`](solutions/base/rwlock.rs) | [`rwlock_full.rs`](full_tasks/rwlock_full.rs) |
| `tokens_full` | Repair the complete allocator token state-machine module. | [verified-memory-allocator] | [`tokens.rs`](solutions/base/tokens.rs) | [`tokens_full.rs`](full_tasks/tokens_full.rs) |
| `types_full` | Repair the selected auxiliary allocator type proofs. | [verified-memory-allocator] | [`types.rs`](solutions/base/types.rs) | [`types_full.rs`](full_tasks/types_full.rs) |
| `unbounded_log_full` | Repair all selected Unbounded Log invariant-preservation proofs. | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_full.rs`](full_tasks/unbounded_log_full.rs) |

## Atomic-operation proof tasks (42)

| Task ID | Description | Target proof obligation | Source project | Source module | Task file |
| --- | --- | --- | --- | --- | --- |
| `cuckoo_delete` | Delete a key/value entry while synchronizing ghost state with the atomic update. | Atomic-ghost proof in `MyHashMap::delete` | [Verus](https://github.com/verus-lang/verus) | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_delete.rs`](tasks/cuckoo_delete.rs) |
| `cuckoo_insert` | Insert a key/value entry while synchronizing ghost state with the atomic update. | Atomic-ghost proof in `MyHashMap::insert` | [Verus](https://github.com/verus-lang/verus) | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_insert.rs`](tasks/cuckoo_insert.rs) |
| `cuckoo_read` | Read a key/value entry while maintaining the atomic ghost-state correspondence. | Atomic-ghost proof in `MyHashMap::read` | [Verus](https://github.com/verus-lang/verus) | [`cuckoo.rs`](solutions/base/cuckoo.rs) | [`cuckoo_read.rs`](tasks/cuckoo_read.rs) |
| `fifo_dequeue` | Dequeue an item while synchronizing the FIFO's consumer state with atomic ghost tokens. | Atomic-ghost proof in `Consumer::dequeue` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_dequeue.rs`](tasks/fifo_dequeue.rs) |
| `fifo_enqueue` | Enqueue an item while synchronizing the FIFO's producer state with atomic ghost tokens. | Atomic-ghost proof in `Producer::enqueue` | [Verus] | [`fifo.rs`](solutions/base/fifo.rs) | [`fifo_enqueue.rs`](tasks/fifo_enqueue.rs) |
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
| `wait` | Repair the queue-length ghost updates when waking all waiters, waking one waiter, and enqueueing a waiter. | Atomic-ghost proofs in `WaitQueue::{wake_all,wake_one,enqueue}` | [vostd](https://github.com/asterinas/vostd) | [`wait.rs`](solutions/base/wait.rs) | [`wait.rs`](tasks/wait.rs) |
| `count_to_two_read_x` | Read the shared counter after both one-shot events have completed. | Logical-atomic proof in `CounterSharedState::read_x` | [Verus](https://github.com/verus-lang/verus) | [`count_to_two.rs`](solutions/base/count_to_two.rs) | [`count_to_two_read_x.rs`](tasks/count_to_two_read_x.rs) |
| `count_to_two_thread_routine` | Increment the counter and complete the caller's one-shot event. | Logical-atomic proof in `thread_routine` | [Verus](https://github.com/verus-lang/verus) | [`count_to_two.rs`](solutions/base/count_to_two.rs) | [`count_to_two_thread_routine.rs`](tasks/count_to_two_thread_routine.rs) |
| `helping_try_cancel_two_flips` | Cancel two pending flip operations through the helping protocol. | Logical-atomic proof in `try_cancel_two_flips` | [Verus](https://github.com/verus-lang/verus) | [`helping.rs`](solutions/base/helping.rs) | [`helping_try_cancel_two_flips.rs`](tasks/helping_try_cancel_two_flips.rs) |
| `helping_try_handshake` | Complete a handshake in the helping protocol. | Logical-atomic proof in `try_handshake` | [Verus](https://github.com/verus-lang/verus) | [`helping.rs`](solutions/base/helping.rs) | [`helping_try_handshake.rs`](tasks/helping_try_handshake.rs) |
| `helping_try_simple_flip` | Complete a simple flip in the helping protocol. | Logical-atomic proof in `try_simple_flip` | [Verus](https://github.com/verus-lang/verus) | [`helping.rs`](solutions/base/helping.rs) | [`helping_try_simple_flip.rs`](tasks/helping_try_simple_flip.rs) |
| `context_enqueue_op` | Enqueue a write operation while synchronizing the client and log ghost state. | Atomic-ghost proof in `Context::enqueue_op` | [verified-node-replication] | [`context.rs`](solutions/base/context.rs) | [`context_enqueue_op.rs`](tasks/context_enqueue_op.rs) |
| `context_dequeue_response` | Dequeue a response while recovering the client and update ghost state. | Atomic-ghost proof in `Context::dequeue_response` | [verified-node-replication] | [`context.rs`](solutions/base/context.rs) | [`context_dequeue_response.rs`](tasks/context_dequeue_response.rs) |
| `log_append` | Append a batch of requests while updating log and cyclic-buffer ghost state. | Atomic-ghost proof in `NrLog::append` | [verified-node-replication] | [`log.rs`](solutions/base/log.rs) | [`log_append.rs`](tasks/log_append.rs) |
| `log_find_min_local_version` | Find the minimum local version while maintaining read-version ghost state. | Atomic-ghost proof in `NrLog::find_min_local_version` | [verified-node-replication] | [`log.rs`](solutions/base/log.rs) | [`log_find_min_local_version.rs`](tasks/log_find_min_local_version.rs) |
| `log_execute` | Execute log operations while maintaining unbounded-log and cyclic-buffer ghost state. | Atomic-ghost proof in `NrLog::execute` | [verified-node-replication] | [`log.rs`](solutions/base/log.rs) | [`log_execute.rs`](tasks/log_execute.rs) |
| `log_advance_head` | Advance the log head while synchronizing garbage-collection ghost state. | Atomic-ghost proof in `NrLog::advance_head` | [verified-node-replication] | [`log.rs`](solutions/base/log.rs) | [`log_advance_head.rs`](tasks/log_advance_head.rs) |
| `log_is_replica_synced_for_reads` | Check whether a replica is synchronized for reads while updating read-state ghost permissions. | Atomic-ghost proof in `NrLog::is_replica_synced_for_reads` | [verified-node-replication] | [`log.rs`](solutions/base/log.rs) | [`log_is_replica_synced_for_reads.rs`](tasks/log_is_replica_synced_for_reads.rs) |
| `replica_acquire_combiner_lock` | Acquire the combiner lock while synchronizing lock ghost state. | Atomic-ghost proof in `Replica::acquire_combiner_lock` | [verified-node-replication] | [`replica.rs`](solutions/base/replica.rs) | [`replica_acquire_combiner_lock.rs`](tasks/replica_acquire_combiner_lock.rs) |
| `replica_collect_thread_ops` | Collect thread operations while moving their permissions into the combiner state. | Atomic-ghost proof in `Replica::collect_thread_ops` | [verified-node-replication] | [`replica.rs`](solutions/base/replica.rs) | [`replica_collect_thread_ops.rs`](tasks/replica_collect_thread_ops.rs) |
| `replica_distribute_thread_resps` | Distribute thread responses while returning response and update ghost permissions. | Atomic-ghost proof in `Replica::distribute_thread_resps` | [verified-node-replication] | [`replica.rs`](solutions/base/replica.rs) | [`replica_distribute_thread_resps.rs`](tasks/replica_distribute_thread_resps.rs) |
| `replica_release_combiner_lock` | Release the combiner lock while restoring its ghost state. | Atomic-ghost proof in `Replica::release_combiner_lock` | [verified-node-replication] | [`replica.rs`](solutions/base/replica.rs) | [`replica_release_combiner_lock.rs`](tasks/replica_release_combiner_lock.rs) |
| `free_free` | Free an allocated block while preserving allocator ownership and ghost state. | Proof in `free` | [verified-memory-allocator] | [`free.rs`](solutions/base/free.rs) | [`free_free.rs`](tasks/free_free.rs) |
| `free_free_block_mt` | Free a block through the multi-threaded free path while maintaining allocator state. | Proof in `free_block_mt` | [verified-memory-allocator] | [`free.rs`](solutions/base/free.rs) | [`free_free_block_mt.rs`](tasks/free_free_block_mt.rs) |
| `linked_list_atomic_insert_block` | Atomically add a block to a linked free list while transferring its ghost resources. | Atomic-ghost proof in `LLAtomic::atomic_insert_block` | [verified-memory-allocator] | [`linked_list.rs`](solutions/base/linked_list.rs) | [`linked_list_atomic_insert_block.rs`](tasks/linked_list_atomic_insert_block.rs) |
| `linked_list_check_is_good` | Check a linked list's delayed-free state while updating its checked-state token. | Atomic-ghost proof in `LLAtomic::check_is_good` | [verified-memory-allocator] | [`linked_list.rs`](solutions/base/linked_list.rs) | [`linked_list_check_is_good.rs`](tasks/linked_list_check_is_good.rs) |
| `linked_list_enable` | Enable a linked free list and establish its delayed-free state. | Atomic-ghost proof in `LLAtomic::enable` | [verified-memory-allocator] | [`linked_list.rs`](solutions/base/linked_list.rs) | [`linked_list_enable.rs`](tasks/linked_list_enable.rs) |
| `linked_list_take` | Take all blocks from a linked free list while preserving its list invariant. | Atomic-ghost proof in `LLAtomic::take` | [verified-memory-allocator] | [`linked_list.rs`](solutions/base/linked_list.rs) | [`linked_list_take.rs`](tasks/linked_list_take.rs) |
| `linked_list_take_` | Take a nonempty linked free list while retaining its delay-state metadata. | Atomic-ghost proof in `LLAtomic::take` | [verified-memory-allocator] | [`linked_list.rs`](solutions/base/linked_list.rs) | [`linked_list_take_.rs`](tasks/linked_list_take_.rs) |
| `linked_list_try_use_delayed_free` | Attempt to claim a linked list's delayed-free state atomically. | Atomic-ghost proof in `LLAtomic::try_use_delayed_free` | [verified-memory-allocator] | [`linked_list.rs`](solutions/base/linked_list.rs) | [`linked_list_try_use_delayed_free.rs`](tasks/linked_list_try_use_delayed_free.rs) |
| `types_disable` | Disable a page's atomic heap pointer and recover its heap-of-page token. | Atomic-ghost proof in `AtomicHeapPtr::disable` | [verified-memory-allocator] | [`types.rs`](solutions/base/types.rs) | [`types_disable.rs`](tasks/types_disable.rs) |
| `types_get_heap` | Read a page's owning heap while proving that it agrees with the local thread state. | Atomic-ghost proof in `PagePtr::get_heap` | [verified-memory-allocator] | [`types.rs`](solutions/base/types.rs) | [`types_get_heap.rs`](tasks/types_get_heap.rs) |

## `tokenized_state_machine!` tasks (33)

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
| `tokens_page_destroy_block_tokens_inductive` | Show that destroying a page's block tokens preserves allocator token invariants. | `page_destroy_block_tokens_inductive` | [verified-memory-allocator] | [`tokens.rs`](solutions/base/tokens.rs) | [`tokens_page_destroy_block_tokens_inductive.rs`](tasks/tokens_page_destroy_block_tokens_inductive.rs) |
| `tokens_page_mk_block_tokens_inductive` | Show that creating a page's block tokens preserves allocator token invariants. | `page_mk_block_tokens_inductive` | [verified-memory-allocator] | [`tokens.rs`](solutions/base/tokens.rs) | [`tokens_page_mk_block_tokens_inductive.rs`](tasks/tokens_page_mk_block_tokens_inductive.rs) |
| `tokens_reserve_uniq_identifier_inductive` | Show that reserving a unique allocator identifier preserves token invariants. | `reserve_uniq_identifier_inductive` | [verified-memory-allocator] | [`tokens.rs`](solutions/base/tokens.rs) | [`tokens_reserve_uniq_identifier_inductive.rs`](tasks/tokens_reserve_uniq_identifier_inductive.rs) |
| `unbounded_log_exec_trivial_start_inductive` | Show that starting trivial execution preserves Unbounded Log invariants. | `exec_trivial_start_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_exec_trivial_start_inductive.rs`](tasks/unbounded_log_exec_trivial_start_inductive.rs) |
| `unbounded_log_exec_update_version_upper_bound_inductive` | Show that updating the version upper bound preserves Unbounded Log invariants. | `exec_update_version_upper_bound_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_exec_update_version_upper_bound_inductive.rs`](tasks/unbounded_log_exec_update_version_upper_bound_inductive.rs) |
| `unbounded_log_readonly_apply_inductive` | Show that applying a read-only request preserves Unbounded Log invariants. | `readonly_apply_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_readonly_apply_inductive.rs`](tasks/unbounded_log_readonly_apply_inductive.rs) |
| `unbounded_log_update_done_inductive` | Show that completing an update preserves Unbounded Log invariants. | `update_done_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_update_done_inductive.rs`](tasks/unbounded_log_update_done_inductive.rs) |
| `unbounded_log_update_place_ops_in_log_one_inductive` | Show that placing an update operation in the log preserves Unbounded Log invariants. | `update_place_ops_in_log_one_inductive` | [verified-node-replication] | [`unbounded_log.rs`](solutions/base/unbounded_log.rs) | [`unbounded_log_update_place_ops_in_log_one_inductive.rs`](tasks/unbounded_log_update_place_ops_in_log_one_inductive.rs) |
