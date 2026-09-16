#!/usr/bin/env python3
"""Update task metadata with non-empty line counts for hard-coded methods."""

from __future__ import annotations

import csv
import re
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
METADATA_PATH = ROOT / "streamlit_app" / "src" / "streamlit_app" / "task_metadata.csv"
METHOD_LINES_COLUMN = "method_lines"


@dataclass(frozen=True)
class Target:
    """A function's name and inclusive line range in its base source module."""

    name: str
    start_line: int
    end_line: int


@dataclass(frozen=True)
class TaskSpec:
    source_module: str
    targets: tuple[Target, ...]


@dataclass(frozen=True)
class TaskSize:
    task_id: str
    method_lines: int
    targets: tuple[str, ...]


# These ranges intentionally identify the current functions directly. If a base
# source file moves, validation fails and this table must be updated explicitly.
TASK_SPECS: dict[str, TaskSpec] = {
    "context_dequeue_response": TaskSpec("context.rs", (Target("dequeue_response", 287, 350),)),
    "context_enqueue_op": TaskSpec("context.rs", (Target("enqueue_op", 230, 285),)),
    "context_full": TaskSpec("context.rs", (Target("enqueue_op", 230, 285), Target("dequeue_response", 287, 350))),
    "count_to_two_full": TaskSpec("count_to_two.rs", (Target("read_x", 266, 294), Target("thread_routine", 297, 325))),
    "count_to_two_read_x": TaskSpec("count_to_two.rs", (Target("read_x", 266, 294),)),
    "count_to_two_thread_routine": TaskSpec("count_to_two.rs", (Target("thread_routine", 297, 325),)),
    "cuckoo_delete": TaskSpec("cuckoo.rs", (Target("delete", 1231, 1358),)),
    "cuckoo_full": TaskSpec("cuckoo.rs", (Target("delete_key_value_inductive", 818, 836), Target("update_key_value_inductive", 839, 857), Target("insert_key_value_inductive", 860, 878), Target("swing_inductive", 881, 899), Target("read", 1123, 1229), Target("delete", 1231, 1358), Target("insert", 1360, 1833))),
    "cuckoo_inductive": TaskSpec("cuckoo.rs", (Target("delete_key_value_inductive", 818, 836), Target("update_key_value_inductive", 839, 857), Target("insert_key_value_inductive", 860, 878), Target("swing_inductive", 881, 899))),
    "cuckoo_insert": TaskSpec("cuckoo.rs", (Target("insert", 1360, 1833),)),
    "cuckoo_read": TaskSpec("cuckoo.rs", (Target("read", 1123, 1229),)),
    "cyclicbuffer_advance_head_finish_inductive": TaskSpec("cyclicbuffer.rs", (Target("advance_head_finish_inductive", 552, 554),)),
    "cyclicbuffer_advance_tail_finish_inductive": TaskSpec("cyclicbuffer.rs", (Target("advance_tail_finish_inductive", 567, 577),)),
    "cyclicbuffer_advance_tail_start_inductive": TaskSpec("cyclicbuffer.rs", (Target("advance_tail_start_inductive", 557, 561),)),
    "cyclicbuffer_append_flip_bit_inductive": TaskSpec("cyclicbuffer.rs", (Target("append_flip_bit_inductive", 580, 606),)),
    "cyclicbuffer_full": TaskSpec("cyclicbuffer.rs", (Target("advance_head_finish_inductive", 552, 554), Target("advance_tail_start_inductive", 557, 561), Target("advance_tail_finish_inductive", 567, 577), Target("append_flip_bit_inductive", 580, 606), Target("reader_guard_inductive", 618, 627), Target("reader_finish_inductive", 633, 649))),
    "cyclicbuffer_reader_finish_inductive": TaskSpec("cyclicbuffer.rs", (Target("reader_finish_inductive", 633, 649),)),
    "cyclicbuffer_reader_guard_inductive": TaskSpec("cyclicbuffer.rs", (Target("reader_guard_inductive", 618, 627),)),
    "dist_rwlock_exc_check_count_inductive": TaskSpec("dist_rwlock.rs", (Target("exc_check_count_inductive", 207, 214),)),
    "dist_rwlock_full": TaskSpec("dist_rwlock.rs", (Target("initialize_inductive", 184, 199), Target("exc_check_count_inductive", 207, 214), Target("shared_finish_inductive", 229, 260), Target("shared_release_inductive", 263, 283))),
    "dist_rwlock_initialize_inductive": TaskSpec("dist_rwlock.rs", (Target("initialize_inductive", 184, 199),)),
    "dist_rwlock_shared_finish_inductive": TaskSpec("dist_rwlock.rs", (Target("shared_finish_inductive", 229, 260),)),
    "dist_rwlock_shared_release_inductive": TaskSpec("dist_rwlock.rs", (Target("shared_release_inductive", 263, 283),)),
    "fifo_consume_end_inductive": TaskSpec("fifo.rs", (Target("consume_end_inductive", 313, 348),)),
    "fifo_consume_start_inductive": TaskSpec("fifo.rs", (Target("consume_start_inductive", 306, 310),)),
    "fifo_dequeue": TaskSpec("fifo.rs", (Target("dequeue", 523, 571),)),
    "fifo_enqueue": TaskSpec("fifo.rs", (Target("enqueue", 471, 519),)),
    "fifo_full": TaskSpec("fifo.rs", (Target("initialize_inductive", 266, 272), Target("produce_start_inductive", 276, 294), Target("produce_end_inductive", 297, 303), Target("consume_start_inductive", 306, 310), Target("consume_end_inductive", 313, 348), Target("enqueue", 471, 519), Target("dequeue", 523, 571))),
    "fifo_initialize_inductive": TaskSpec("fifo.rs", (Target("initialize_inductive", 266, 272),)),
    "fifo_produce_end_inductive": TaskSpec("fifo.rs", (Target("produce_end_inductive", 297, 303),)),
    "fifo_produce_start_inductive": TaskSpec("fifo.rs", (Target("produce_start_inductive", 276, 294),)),
    "flat_combine_client_recv_inductive": TaskSpec("flat_combine.rs", (Target("client_recv_inductive", 223, 232),)),
    "flat_combine_client_send_inductive": TaskSpec("flat_combine.rs", (Target("client_send_inductive", 188, 201),)),
    "flat_combine_combiner_go_to_collecting_inductive": TaskSpec("flat_combine.rs", (Target("combiner_go_to_collecting_inductive", 398, 404),)),
    "flat_combine_combiner_go_to_responding_inductive": TaskSpec("flat_combine.rs", (Target("combiner_go_to_responding_inductive", 381, 387),)),
    "flat_combine_combiner_recv_inductive": TaskSpec("flat_combine.rs", (Target("combiner_recv_inductive", 256, 268),)),
    "flat_combine_combiner_send_inductive": TaskSpec("flat_combine.rs", (Target("combiner_send_inductive", 333, 348),)),
    "flat_combine_combiner_send_skip_inductive": TaskSpec("flat_combine.rs", (Target("combiner_send_skip_inductive", 367, 378),)),
    "flat_combine_combiner_skip_inductive": TaskSpec("flat_combine.rs", (Target("combiner_skip_inductive", 284, 294),)),
    "flat_combine_full": TaskSpec("flat_combine.rs", (Target("client_send_inductive", 188, 201), Target("client_recv_inductive", 223, 232), Target("combiner_recv_inductive", 256, 268), Target("combiner_skip_inductive", 284, 294), Target("combiner_send_inductive", 333, 348), Target("combiner_send_skip_inductive", 367, 378), Target("combiner_go_to_responding_inductive", 381, 387), Target("combiner_go_to_collecting_inductive", 398, 404))),
    "free_free": TaskSpec("free.rs", (Target("free", 13002, 13127),)),
    "free_free_block_mt": TaskSpec("free.rs", (Target("free_block_mt", 13197, 13405),)),
    "free_full": TaskSpec("free.rs", (Target("free", 13002, 13127), Target("free_block_mt", 13197, 13405))),
    "helping_full": TaskSpec("helping.rs", (Target("try_cancel_two_flips", 203, 255), Target("try_simple_flip", 257, 315), Target("try_handshake", 317, 413))),
    "helping_try_cancel_two_flips": TaskSpec("helping.rs", (Target("try_cancel_two_flips", 203, 255),)),
    "helping_try_handshake": TaskSpec("helping.rs", (Target("try_handshake", 317, 413),)),
    "helping_try_simple_flip": TaskSpec("helping.rs", (Target("try_simple_flip", 257, 315),)),
    "linked_list_atomic_insert_block": TaskSpec("linked_list.rs", (Target("atomic_insert_block", 11057, 11123),)),
    "linked_list_check_is_good": TaskSpec("linked_list.rs", (Target("check_is_good", 11374, 11427),)),
    "linked_list_enable": TaskSpec("linked_list.rs", (Target("enable", 11295, 11341),)),
    "linked_list_full": TaskSpec("linked_list.rs", (Target("atomic_insert_block", 11057, 11123), Target("take", 11126, 11165), Target("enable", 11295, 11341), Target("check_is_good", 11374, 11427), Target("try_use_delayed_free", 11430, 11485), Target("take", 11488, 11542))),
    "linked_list_take": TaskSpec("linked_list.rs", (Target("take", 11126, 11165),)),
    "linked_list_take_": TaskSpec("linked_list.rs", (Target("take", 11488, 11542),)),
    "linked_list_try_use_delayed_free": TaskSpec("linked_list.rs", (Target("try_use_delayed_free", 11430, 11485),)),
    "log_advance_head": TaskSpec("log.rs", (Target("advance_head", 1427, 1552),)),
    "log_append": TaskSpec("log.rs", (Target("append", 1101, 1423),)),
    "log_execute": TaskSpec("log.rs", (Target("execute", 1606, 1905),)),
    "log_find_min_local_version": TaskSpec("log.rs", (Target("find_min_local_version", 1907, 1962),)),
    "log_full": TaskSpec("log.rs", (Target("is_replica_synced_for_reads", 1000, 1039), Target("append", 1101, 1423), Target("advance_head", 1427, 1552), Target("execute", 1606, 1905), Target("find_min_local_version", 1907, 1962))),
    "log_is_replica_synced_for_reads": TaskSpec("log.rs", (Target("is_replica_synced_for_reads", 1000, 1039),)),
    "once_full": TaskSpec("once.rs", (Target("init", 183, 227), Target("get", 229, 257))),
    "once_get": TaskSpec("once.rs", (Target("get", 229, 257),)),
    "once_init": TaskSpec("once.rs", (Target("init", 183, 227),)),
    "replica_acquire_combiner_lock": TaskSpec("replica.rs", (Target("acquire_combiner_lock", 2545, 2586),)),
    "replica_collect_thread_ops": TaskSpec("replica.rs", (Target("collect_thread_ops", 2744, 2877),)),
    "replica_distribute_thread_resps": TaskSpec("replica.rs", (Target("distribute_thread_resps", 2879, 3012),)),
    "replica_full": TaskSpec("replica.rs", (Target("acquire_combiner_lock", 2545, 2586), Target("release_combiner_lock", 2589, 2606), Target("collect_thread_ops", 2744, 2877), Target("distribute_thread_resps", 2879, 3012))),
    "replica_release_combiner_lock": TaskSpec("replica.rs", (Target("release_combiner_lock", 2589, 2606),)),
    "rwlock_full": TaskSpec("rwlock.rs", (Target("try_read", 2855, 2907), Target("try_write", 2910, 2956), Target("try_upread", 2958, 3012), Target("drop", 3114, 3138), Target("drop", 3205, 3240), Target("try_upgrade", 3298, 3378), Target("drop", 3395, 3421))),
    "rwlock_readguard_drop": TaskSpec("rwlock.rs", (Target("drop", 3114, 3138),)),
    "rwlock_try_read": TaskSpec("rwlock.rs", (Target("try_read", 2855, 2907),)),
    "rwlock_try_upgrade": TaskSpec("rwlock.rs", (Target("try_upgrade", 3298, 3378),)),
    "rwlock_try_upread": TaskSpec("rwlock.rs", (Target("try_upread", 2958, 3012),)),
    "rwlock_try_write": TaskSpec("rwlock.rs", (Target("try_write", 2910, 2956),)),
    "rwlock_upgradableguard_drop": TaskSpec("rwlock.rs", (Target("drop", 3395, 3421),)),
    "rwlock_writeguard_drop": TaskSpec("rwlock.rs", (Target("drop", 3205, 3240),)),
    "statics_get": TaskSpec("statics.rs", (Target("get", 75, 135),)),
    "tokens_full": TaskSpec("tokens.rs", (Target("page_mk_block_tokens_inductive", 1447, 1461), Target("page_destroy_block_tokens_inductive", 1514, 1530), Target("page_disable_inductive", 1533, 1547), Target("page_destroy_tokens_inductive", 1550, 1567), Target("reserve_uniq_identifier_inductive", 1580, 1595))),
    "tokens_page_destroy_block_tokens_inductive": TaskSpec("tokens.rs", (Target("page_destroy_block_tokens_inductive", 1514, 1530),)),
    "tokens_page_mk_block_tokens_inductive": TaskSpec("tokens.rs", (Target("page_mk_block_tokens_inductive", 1447, 1461),)),
    "tokens_reserve_uniq_identifier_inductive": TaskSpec("tokens.rs", (Target("reserve_uniq_identifier_inductive", 1580, 1595),)),
    "types_disable": TaskSpec("types.rs", (Target("disable", 1971, 1990),)),
    "types_full": TaskSpec("types.rs", (Target("disable", 1971, 1990), Target("get_heap", 3518, 3541))),
    "types_get_heap": TaskSpec("types.rs", (Target("get_heap", 3518, 3541),)),
    "unbounded_log_exec_dispatch_local_inductive": TaskSpec("unbounded_log.rs", (Target("exec_dispatch_local_inductive", 974, 1006),)),
    "unbounded_log_exec_trivial_start_inductive": TaskSpec("unbounded_log.rs", (Target("exec_trivial_start_inductive", 865, 875),)),
    "unbounded_log_exec_update_version_upper_bound_inductive": TaskSpec("unbounded_log.rs", (Target("exec_update_version_upper_bound_inductive", 1012, 1025),)),
    "unbounded_log_full": TaskSpec("unbounded_log.rs", (Target("initialize_inductive", 722, 744), Target("readonly_ready_to_read_inductive", 751, 763), Target("readonly_apply_inductive", 766, 772), Target("update_done_inductive", 814, 829), Target("exec_trivial_start_inductive", 865, 875), Target("update_place_ops_in_log_one_inductive", 878, 964), Target("exec_dispatch_local_inductive", 974, 1006), Target("exec_update_version_upper_bound_inductive", 1012, 1025))),
    "unbounded_log_readonly_apply_inductive": TaskSpec("unbounded_log.rs", (Target("readonly_apply_inductive", 766, 772),)),
    "unbounded_log_update_done_inductive": TaskSpec("unbounded_log.rs", (Target("update_done_inductive", 814, 829),)),
    "unbounded_log_update_place_ops_in_log_one_inductive": TaskSpec("unbounded_log.rs", (Target("update_place_ops_in_log_one_inductive", 878, 964),)),
    "wait": TaskSpec("wait.rs", (Target("wake_one", 254, 283), Target("wake_all", 286, 318), Target("enqueue", 326, 346))),
}


def read_metadata(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(encoding="utf-8", newline="") as metadata_file:
        reader = csv.DictReader(metadata_file)
        fieldnames = list(reader.fieldnames or [])
        rows = list(reader)
    required = {"task_id", "source_module"}
    missing = required - set(fieldnames)
    if missing:
        raise ValueError(f"{path}: missing columns: {', '.join(sorted(missing))}")
    return fieldnames, rows


def count_target_lines(lines: list[str], target: Target, source_path: Path) -> int:
    if target.start_line < 1 or target.end_line < target.start_line or target.end_line > len(lines):
        raise ValueError(
            f"{source_path}: invalid range {target.start_line}-{target.end_line} "
            f"for {target.name}"
        )
    declaration = lines[target.start_line - 1]
    if re.search(rf"\bfn\s+{re.escape(target.name)}\b", declaration) is None:
        raise ValueError(
            f"{source_path}:{target.start_line}: expected function {target.name!r}; "
            "the hard-coded line range is stale"
        )
    if not lines[target.end_line - 1].rstrip().endswith("}"):
        raise ValueError(
            f"{source_path}:{target.end_line}: expected the closing line of {target.name!r}; "
            "the hard-coded line range is stale"
        )
    return sum(bool(line.strip()) for line in lines[target.start_line - 1 : target.end_line])


def calculate_all_sizes(
    rows: list[dict[str, str]], root: Path = ROOT
) -> list[TaskSize]:
    metadata_ids = [row.get("task_id", "").strip() for row in rows]
    duplicate_ids = sorted({task_id for task_id in metadata_ids if metadata_ids.count(task_id) > 1})
    if duplicate_ids:
        raise ValueError(f"duplicate metadata task IDs: {', '.join(duplicate_ids)}")

    missing_specs = sorted(set(metadata_ids) - set(TASK_SPECS))
    extra_specs = sorted(set(TASK_SPECS) - set(metadata_ids))
    if missing_specs or extra_specs:
        details = []
        if missing_specs:
            details.append(f"missing task specs: {', '.join(missing_specs)}")
        if extra_specs:
            details.append(f"task specs without metadata: {', '.join(extra_specs)}")
        raise ValueError("; ".join(details))

    source_cache: dict[str, tuple[Path, list[str]]] = {}
    results: list[TaskSize] = []
    for row in rows:
        task_id = row["task_id"].strip()
        spec = TASK_SPECS[task_id]
        metadata_module = row.get("source_module", "").strip()
        if metadata_module != spec.source_module:
            raise ValueError(
                f"{task_id}: metadata names {metadata_module!r}, "
                f"but its hard-coded source module is {spec.source_module!r}"
            )
        if spec.source_module not in source_cache:
            source_path = root / "solutions" / "base" / spec.source_module
            source_cache[spec.source_module] = (
                source_path,
                source_path.read_text(encoding="utf-8").splitlines(),
            )
        source_path, source_lines = source_cache[spec.source_module]
        method_lines = sum(
            count_target_lines(source_lines, target, source_path)
            for target in spec.targets
        )
        results.append(
            TaskSize(task_id, method_lines, tuple(target.name for target in spec.targets))
        )
    return results


def metadata_is_current(rows: list[dict[str, str]], sizes: list[TaskSize]) -> bool:
    expected = {size.task_id: str(size.method_lines) for size in sizes}
    return all(row.get(METHOD_LINES_COLUMN) == expected.get(row.get("task_id", "")) for row in rows)


def write_metadata(
    path: Path,
    fieldnames: list[str],
    rows: list[dict[str, str]],
    sizes: list[TaskSize],
) -> None:
    output_fields = list(fieldnames)
    if METHOD_LINES_COLUMN not in output_fields:
        output_fields.append(METHOD_LINES_COLUMN)
    sizes_by_task = {size.task_id: str(size.method_lines) for size in sizes}
    output_rows = []
    for row in rows:
        output_row = dict(row)
        output_row[METHOD_LINES_COLUMN] = sizes_by_task[row["task_id"].strip()]
        output_rows.append(output_row)
    with path.open("w", encoding="utf-8", newline="") as metadata_file:
        writer = csv.DictWriter(metadata_file, fieldnames=output_fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(output_rows)


def main() -> int:
    fieldnames, rows = read_metadata(METADATA_PATH)
    sizes = calculate_all_sizes(rows)
    write_metadata(METADATA_PATH, fieldnames, rows, sizes)
    print(f"Updated {len(sizes)} tasks in {METADATA_PATH}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
