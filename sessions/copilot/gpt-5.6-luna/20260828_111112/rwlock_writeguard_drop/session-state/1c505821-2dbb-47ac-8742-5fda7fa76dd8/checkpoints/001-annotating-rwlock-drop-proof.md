<overview>
The user asked for proof annotations to be added to `/workspace/task_env/rwlock_writeguard_drop.rs` so Verus can verify it, with the annotated result written to `/workspace/task_env/rwlock_writeguard_drop_verified.rs`. Constraints included preserving executable code and existing contracts/admits, adding no `admit`/`assume` or external-body axioms, and running both Verus and Lynette on the original and generated files. The approach was to inspect the failing `RwLockWriteGuard::drop` atomic ghost block, study the local vstd resource and atomic APIs, then iteratively add ghost-state transitions and proof assertions.
</overview>

<history>
1. The user requested complete Verus proof annotations and a separately named verified file.
   - Inspected the original file, especially the `RwLockWriteGuard::drop` implementation around lines 2987–3003.
   - Ran Verus on the original file. It reported 57 verified functions and one error: the invariant could not be shown at the end of the `atomic_with_ghost!` block for `fetch_and(!WRITER)`.
   - Attempted to run Lynette on the original file, but initially used the wrong invocation; Lynette requires both an origin file and a changed file.

2. The investigation focused on understanding the ghost resource transition.
   - Read the `RwPerms` invariant and the `RwLockWriteGuard` fields.
   - Examined local `/workspace/vstd/atomic_ghost.rs` documentation and macro implementation, confirming that the ghost block must transform the invariant from the old atomic value/state to the new state.
   - Examined resource APIs for `SumResource`, `Count`, `CountResource`, `OneRightKnowledge`, and related split/join/take/put methods.

3. A copy was created at `/workspace/task_env/rwlock_writeguard_drop_verified.rs`.
   - Added proof code attempting to return the write-held ghost state to the read-side state:
     - validation calls,
     - joining the write-side knowledge token,
     - converting the core token from right to left,
     - reconstructing a fractional permission,
     - splitting read permissions,
     - rebuilding the read guard token and upgradeable-reader token.
   - Iteratively adjusted code in response to Verus type errors and failed preconditions.

4. Verification iterations produced partial progress but never reached a successful proof.
   - Initial added code referenced an unavailable `core_token` variable; corrected to use `g.core_token`.
   - A type mismatch showed that `CountResource::alloc_from_empty` expected a `Count<PointsTo<T>>`, not a `OneLeftKnowledge`; changed the construction to derive a `Count` by taking the left resource and splitting it.
   - Verus then reported failed preconditions for `change_to_left` and for taking the right side of `read_guard_token`.
   - Added assertions and validation calls, but several assertions about `is_right`, `is_resource_owner`, `has_resource`, and token fractions failed.
   - The most recent Verus run still failed in the `drop` proof, with an assertion that `g.core_token.is_right()` could not be established and consequently the `change_to_left` precondition was not met.

5. The user then requested a detailed conversation summary for checkpointing.
   - No further code changes or tool calls were made after that request.
</history>

<work_done>
Files created or modified:
- `/workspace/task_env/rwlock_writeguard_drop_verified.rs`
  - Created as a copy of the original.
  - Added experimental proof annotations only inside the `RwLockWriteGuard::drop` ghost block.
  - The file is not currently verified successfully.
- `/workspace/task_env/rwlock_writeguard_drop.rs`
  - Not modified.
  - Original Verus result remains one invariant-proof error.
- No files were deleted.

Completed:
- [x] Located the sole original Verus failure.
- [x] Inspected relevant local vstd definitions and resource APIs.
- [x] Created the requested output file.
- [ ] Finish the proof annotations.
- [ ] Obtain a clean Verus verification result for the generated file.
- [ ] Run Lynette correctly on both original and generated files and fix any illegal changes.
</work_done>

<technical_details>
- The failing code is the atomic ghost operation:
  `self.inner.lock => fetch_and(!WRITER); update prev -> next;`
- The atomic ghost macro assumes the old invariant and requires the ghost state to satisfy the invariant for the new value before the block ends.
- The `RwPerms` invariant encodes:
  - writer activity through `g.core_token.is_right()` and the `WRITER` bit,
  - read activity through `g.read_guard_token`,
  - upgradeable-reader state through `g.upreader_guard_token`,
  - the relation between reader count bits, failed attempts, and active tokens.
- `RwLockWriteGuard` owns:
  - `tracked_perm: Tracked<PointsTo<T>>`,
  - `tracked_token: Tracked<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>>`.
- Existing resource APIs relevant to the intended transition include:
  - `SumResource::join_one_right_knowledge`,
  - `SumResource::change_to_left`,
  - `SumResource::take_resource_left` / `put_resource_left`,
  - `SumResource::split_one_left_owner`,
  - `Count::new`, `Count::split`,
  - `CountResource::alloc_from_empty`,
  - `Sum::tracked_take_right`.
- The write token is a `OneRightKnowledge`, so joining it into `g.core_token` changes knowledge/fraction state but does not necessarily make `g.core_token.is_resource_owner()` true. This was a key source of failed assertions.
- The original invariant may imply the writer state from the atomic `prev` value, but Verus did not automatically derive the needed bit relationship in the attempted proof. An explicit lemma/assertion likely needs to connect:
  - `prev & WRITER != 0`,
  - `g.core_token.is_right()`,
  - the writer-side resource ownership/state.
- The attempted proof also incorrectly assumed the read guard token was immediately `Right`; this requires proving from the invariant that when a writer is active, `g.read_guard_token` is `Right`.
- Warnings about `#[verus_verify]`/`#[verus_spec]` inside `verus!` blocks are pre-existing style warnings and were not the verification failure.
- The local Verus installation is available via the `verus` command.
- Lynette usage discovered from its error message: it requires two positional arguments, an origin file and a changed file, e.g.:
  `lynette /workspace/task_env/rwlock_writeguard_drop.rs /workspace/task_env/rwlock_writeguard_drop_verified.rs`
- No `admit(...)` or `assume(...)` was added. Existing `external_body`/`unimplemented!()` proof holes were preserved.
</technical_details>

<important_files>
- `/workspace/task_env/rwlock_writeguard_drop.rs`
  - Original source requiring verification.
  - Main relevant section: `RwLockWriteGuard::drop` around lines 2986–3003.
  - The `RwPerms` invariant is around lines 2562–2731.
  - Resource helper definitions occupy much of the earlier file, especially `SumResource`, `Count`, and `CountResource`.
- `/workspace/task_env/rwlock_writeguard_drop_verified.rs`
  - Requested output file.
  - Current experimental proof annotations are in the `drop` ghost block around lines 3000–3020.
  - Current state: does not pass Verus.
- `/workspace/vstd/atomic_ghost.rs`
  - Documents and implements `atomic_with_ghost!`.
  - Important behavior is around lines 295–313 and macro implementations around lines 531–551.
- `/workspace/vstd/rwlock.rs`
  - A separate vstd rwlock implementation viewed for conceptual context, especially its release transition and invariant structure.
</important_files>

<next_steps>
Remaining work:
- Rework the ghost transition in `RwLockWriteGuard::drop` from the actual invariant facts rather than relying on failed assertions.
- Prove or expose the necessary relationships between `prev`, `next`, the `WRITER` bit, `g.core_token`, and `g.read_guard_token`.
- Determine the exact expected post-state after clearing `WRITER`; likely restore the core token and read-token state using the existing `SumResource` and `CountResource` APIs while preserving the correct ownership/fraction structure.
- Re-run Verus after each targeted adjustment until it reports no errors.
- Run Lynette with both files after Verus succeeds, then correct any illegal executable/spec/contract changes it reports.
- Confirm the original file remains unchanged and all existing proof holes remain intact.
</next_steps>