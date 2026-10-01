#!/usr/bin/env python3
"""Metadata-only resource accounting; never imports or runs a numerical solver.

Schema check (no output files, works while the queue is running):
    python resource_summary.py --self-check
Final report (refuses an unfinished queue unless --allow-incomplete is explicit):
    python resource_summary.py --output resource_report.json
Optional --disk-root PATH may be repeated to measure disjoint additional archives.

All durations are elapsed wall durations, NOT CPU time. Reuse accounting reads
PROCESS/REUSE metadata, never the copied worker's historical elapsed field as a
current solve. Source and parsed JSON bytes are SHA-bound; witness NPZ files are
only stat'ed for disk accounting, never reopened or numerically revalidated here.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import statistics
import sys


SCOPE = (
    "Descriptive shared-container elapsed timing under a recorded 10.2-CPU cgroup "
    "quota, not dedicated-host performance or measured CPU-seconds. No objective "
    "scores or comparative outcomes are calculated. Parallel worker durations "
    "must not be interpreted as sequential queue elapsed time."
)


def utcnow():
    return datetime.now(timezone.utc).isoformat()


def seconds(value):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value) if math.isfinite(value) else None


def stats(values):
    valid = [v for v in values if v is not None]
    return {
        "count": len(valid), "missing_count": len(values) - len(valid),
        "sum": math.fsum(valid) if valid or not values else None, "mean": statistics.mean(valid) if valid else None,
        "median": statistics.median(valid) if valid else None,
        "min": min(valid) if valid else None, "max": max(valid) if valid else None,
    }


def interval(start, finish):
    if not start or not finish:
        return None
    return (datetime.fromisoformat(finish) - datetime.fromisoformat(start)).total_seconds()


class Inputs:
    def __init__(self):
        self.inventory = {}
        self.cache = {}
        self.issues = []

    def issue(self, message, severity="error"):
        self.issues.append({"severity": severity, "message": message})

    def read(self, path, required=True, kind="metadata"):
        path = Path(path).resolve()
        if str(path) in self.cache:
            return self.cache[str(path)]
        if not path.exists():
            if required:
                self.issue(f"Missing {kind}: {path}")
            return None
        with path.open("rb") as f:
            st = os.fstat(f.fileno())
            raw = f.read()
            after = os.fstat(f.fileno())
        if (st.st_size, st.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
            self.issue(f"File changed during read: {path}")
        self.inventory[str(path)] = {
            "path": str(path), "kind": kind, "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(), "mtime_ns": st.st_mtime_ns,
            "stat_bytes": st.st_size,
        }
        self.cache[str(path)] = raw
        return raw

    def json(self, path, required=True):
        raw = self.read(path, required)
        if raw is None:
            return None
        try:
            return json.loads(raw)
        except (ValueError, UnicodeError) as exc:
            self.issue(f"Invalid JSON {path}: {exc}")
            return None

    def changed(self):
        changed = []
        for p, entry in self.inventory.items():
            try:
                st = Path(p).stat()
                if (st.st_size, st.st_mtime_ns) != (entry["stat_bytes"], entry["mtime_ns"]):
                    changed.append(p)
            except OSError:
                changed.append(p)
        return changed


def close(a, b):
    return a is not None and b is not None and math.isclose(a, b, rel_tol=1e-10, abs_tol=1e-6)


def cost_record(process):
    """Partition current work. Historical and nested timing fields are not added."""
    reuse = process.get("reuse_attempt") or {}
    accepted = reuse.get("status") == "accepted"
    numerical = process.get("numerical") or {}
    validation = process.get("validation") or {}
    rejected = bool(reuse) and not accepted
    span = interval(process.get("started_utc"), process.get("finished_utc"))
    row = {
        "audit_id": process["audit_id"], "model": process.get("model"),
        "status": process.get("status"), "accepted_reuse": accepted,
        "rejected_reuse_attempt": rejected,
        "fresh_numerical_seconds": 0.0 if accepted else seconds(numerical.get("wall_seconds")),
        "fresh_validation_seconds": 0.0 if accepted else seconds(validation.get("wall_seconds")),
        "accepted_reuse_copy_hash_seconds": seconds(reuse.get("copy_and_hash_seconds")) if accepted else 0.0,
        "accepted_reuse_validation_seconds": seconds(validation.get("wall_seconds")) if accepted else 0.0,
        "rejected_reuse_attempt_seconds": seconds(reuse.get("attempt_wall_seconds")) if rejected else 0.0,
        "task_recorded_utc_span_seconds": span,
        "numerical_exit": numerical.get("exit"), "validation_exit": validation.get("exit"),
        "numerical_hard_timeout": numerical.get("hard_timeout"),
        "validation_hard_timeout": validation.get("hard_timeout"),
        "error": process.get("error"),
    }
    fields = ["fresh_numerical_seconds", "fresh_validation_seconds",
              "accepted_reuse_copy_hash_seconds", "accepted_reuse_validation_seconds",
              "rejected_reuse_attempt_seconds"]
    known = [row[k] for k in fields if row[k] is not None]
    row["known_current_work_seconds"] = math.fsum(known)
    row["current_timing_fields_missing"] = [k for k in fields if row[k] is None]
    row["bookkeeping_residual_seconds"] = (
        span - row["known_current_work_seconds"]
        if span is not None and not row["current_timing_fields_missing"] else None
    )
    return row


def planning_report(study, inputs):
    status = inputs.json(study / "PLANNING_STATUS.json") or {}
    queue = inputs.json(study / "EXECUTION_QUEUE.json") or {}
    completed = status.get("results", [])
    lookup = {(r["model"], r["arm"]): r for r in completed}
    expected = [(r["model"], r["arm"]) for r in queue.get("jobs", [])]
    if len(lookup) != len(completed):
        inputs.issue("Duplicate planning PROCESS records in PLANNING_STATUS")
    if status.get("completed_processes") != len(completed):
        inputs.issue("Planning status completion count differs from stored records")
    rows, missing = [], []
    for model, arm in expected:
        record = lookup.get((model, arm))
        if record is None:
            missing.append({"model": model, "arm": arm})
            continue
        folder = study / "runs" / model / arm
        disk_record = inputs.json(folder / "PROCESS.json")
        if disk_record != record:
            inputs.issue(f"Planning PROCESS disagrees with status: {model}/{arm}")
        result = inputs.json(folder / "result.json", required=False) or {}
        wall = seconds(record.get("wall_seconds"))
        plan = seconds(result.get("planning_seconds"))
        export = seconds(result.get("export_seconds"))
        baseline = seconds(result.get("end_to_end_seconds")) if arm == "baseline" else None
        internal = baseline if arm == "baseline" else (
            plan + export if plan is not None and export is not None else None)
        overhead = wall - internal if wall is not None and internal is not None else None
        if overhead is not None and overhead < -1e-5:
            inputs.issue(f"Negative planning process overhead: {model}/{arm}: {overhead}")
        rows.append({
            "model": model, "arm": arm, "process_exit": record.get("exit"),
            "process_error": record.get("error"), "result_status": result.get("status", "missing"),
            "result_error": result.get("error"), "process_wall_seconds": wall,
            "planning_seconds": plan, "export_seconds": export,
            "baseline_bundle_end_to_end_seconds": baseline, "process_overhead_seconds": overhead,
        })
    extra = sorted(set(lookup) - set(expected))
    if extra:
        inputs.issue(f"Unexpected planning records: {extra}")
    groups = defaultdict(list)
    for row in rows:
        groups[row["arm"]].append(row)
    fields = ["process_wall_seconds", "planning_seconds", "export_seconds",
              "baseline_bundle_end_to_end_seconds", "process_overhead_seconds"]
    by_arm = {arm: {"runs": len(group),
                    "result_status_counts": dict(Counter(r["result_status"] for r in group)),
                    **{f: stats([r[f] for r in group]) for f in fields}}
              for arm, group in sorted(groups.items())}
    proxy = None
    status_entry = inputs.inventory.get(str((study / "PLANNING_STATUS.json").resolve()))
    if queue.get("started_utc") and status_entry:
        proxy = status_entry["mtime_ns"] / 1e9 - datetime.fromisoformat(queue["started_utc"]).timestamp()
    checks = inputs.json(study / "PLANNING_AUDIT.json", required=False)
    check_report = None
    if checks:
        check_report = {
            "state": checks.get("state"), "workers": checks.get("workers"),
            "checked_runs": checks.get("checked_runs"), "status_counts": checks.get("counts"),
            "measured_queue_elapsed_seconds": seconds(checks.get("seconds")),
            "sum_per_run_checker_wall_seconds": stats([seconds(r.get("seconds")) for r in checks.get("runs", [])]),
            "failures": [{k: r.get(k) for k in ["model", "arm", "status", "checker_exit", "error"]}
                         for r in checks.get("runs", []) if r.get("status") != "passed"],
            "scope": "Separate independent planning-validation queue; its duration is not added to planner construction times.",
        }
    return {
        "state": status.get("state"), "workers": queue.get("workers"),
        "cpus": queue.get("cpus"), "started_utc": queue.get("started_utc"),
        "expected_runs": len(expected), "recorded_runs": len(rows), "missing_runs": missing,
        "measured_queue_elapsed_seconds": None,
        "status_file_write_time_proxy_seconds": proxy,
        "queue_timing_limitation": "Planning queue did not save a finish timestamp or monotonic elapsed duration. The file-mtime proxy is not a measured queue duration and may change if metadata is rewritten.",
        "by_arm": by_arm, "totals": {f: stats([r[f] for r in rows]) for f in fields},
        "failures": [r for r in rows if r["process_exit"] != 0 or r["result_status"] in {"failed", "missing"}],
        "budget_or_other_error_records": [r for r in rows if r["result_error"]],
        "records": rows, "independent_validation": check_report,
        "timing_definitions": {
            "planning_seconds": "Planner internal elapsed time including geometry/targets and optimization, before export.",
            "export_seconds": "Planner internal policy/cut/round archive export time, before final result and FILES serialization.",
            "process_overhead_seconds": "Process wall minus recorded internal planning/export (or baseline bundle): interpreter/import/model loading and unallocated wrapper/final-serialization time; not CPU time.",
            "baseline_bundle": "One shared construction/export run for information, Brier and uniform. Its internal end-to-end duration is charged once; no separate export measurement exists.",
            "time_cap": "Expected budget termination is retained separately from process failure; saved error details are preserved.",
        },
    }


def audit_report(audits, inputs):
    status = inputs.json(audits / "STATUS.json") or {}
    execution = inputs.json(audits / "EXECUTION.json") or {}
    queue = inputs.json(audits / "AUDIT_QUEUE.json") or {}
    inputs.read(audits / "BINDINGS.json")
    final = inputs.json(audits / "FINAL_INPUT_CHECK.json", required=False)
    rows, historical, failures = [], {}, []
    results = status.get("results", [])
    if status.get("completed") != len(results):
        inputs.issue("Audit completed count differs from STATUS result records")
    seen = set()
    for record in results:
        identity = record["audit_id"]
        if identity in seen:
            inputs.issue(f"Duplicate audit completion record: {identity}")
        seen.add(identity)
        task = audits / "tasks" / identity
        if inputs.json(task / "PROCESS.json") != record:
            inputs.issue(f"Audit PROCESS disagrees with STATUS: {identity}")
        row = cost_record(record)
        rows.append(row)
        if row["bookkeeping_residual_seconds"] is not None and row["bookkeeping_residual_seconds"] < -0.02:
            inputs.issue(f"Negative audit bookkeeping residual: {identity}")
        reuse = record.get("reuse_attempt") or {}
        if row["accepted_reuse"]:
            reuse_file = inputs.json(audits / "audits" / identity / "REUSE.json") or {}
            for key, value in reuse.items():
                if reuse_file.get(key) != value:
                    inputs.issue(f"REUSE and PROCESS disagree: {identity}/{key}")
            if record.get("validation") != reuse.get("validation"):
                inputs.issue(f"Aliased reuse validation fields disagree: {identity}")
            actual = row["accepted_reuse_copy_hash_seconds"]
            validation = row["accepted_reuse_validation_seconds"]
            if not close(None if actual is None or validation is None else actual + validation,
                         seconds(reuse.get("current_copy_and_recheck_seconds"))):
                inputs.issue(f"Reuse copy/recheck accounting mismatch: {identity}")
            if (record.get("numerical") or {}).get("mode") != "reused_complete_witnesses":
                inputs.issue(f"Accepted reuse has unexpected numerical mode: {identity}")
            old = str(reuse.get("reused_from") or record.get("reused_from"))
            h = {
                "reused_from": old, "old_audit_id": reuse.get("old_audit_id"),
                "model_sha256": reuse.get("model_sha256"), "exact_E_sha256": reuse.get("exact_E_sha256"),
                "numerical_process_wall_seconds": seconds(reuse.get("historical_numerical_wall_seconds")),
                "validation_process_wall_seconds": seconds(reuse.get("historical_validation_wall_seconds")),
                "worker_internal_elapsed_seconds_included_above": seconds(reuse.get("historical_worker_elapsed_seconds")),
                "validator_internal_elapsed_seconds_included_above": seconds(reuse.get("historical_validation_internal_seconds")),
            }
            if old in historical and historical[old] != h:
                inputs.issue(f"Conflicting metadata for one historical audit: {old}")
            historical[old] = h
        elif reuse:
            inputs.read(task / "REUSE_REJECTION.json", required=False)
        if row["status"] not in {"complete_validated", "partial_validated"}:
            failures.append(row)
    fields = ["fresh_numerical_seconds", "fresh_validation_seconds", "accepted_reuse_copy_hash_seconds",
              "accepted_reuse_validation_seconds", "rejected_reuse_attempt_seconds",
              "known_current_work_seconds", "task_recorded_utc_span_seconds", "bookkeeping_residual_seconds"]
    return {
        "state": status.get("state"), "as_of_utc": status.get("updated_utc"),
        "workers": execution.get("workers"), "cpus": execution.get("cpus"),
        "started_utc": execution.get("started_utc"),
        "measured_queue_elapsed_seconds": seconds(status.get("elapsed_seconds")),
        "queue_elapsed_scope": "Orchestrator monotonic elapsed time at the bound STATUS snapshot, including queue/concurrency/dispatch. Active tasks are not included in the completed-task cost totals.",
        "total_unique_jobs": status.get("total"), "recorded_completed_jobs": len(rows),
        "active_at_snapshot": [{k: r.get(k) for k in ["audit_id", "cpu", "phase", "started_utc"]}
                               for r in status.get("active", [])],
        "status_counts": dict(Counter(r["status"] for r in rows)),
        "endpoint_coverage": {k: status.get(k) for k in ["expected_endpoint_count", "missing_endpoints", "invalid_endpoints"]},
        "accepted_reuse_count": sum(r["accepted_reuse"] for r in rows),
        "rejected_reuse_attempt_count": sum(r["rejected_reuse_attempt"] for r in rows),
        "current_worker_costs": {
            f: stats([r[f] for r in rows
                      if ((not r["accepted_reuse"]) if f.startswith("fresh_")
                          else r["accepted_reuse"] if f.startswith("accepted_reuse_")
                          else r["rejected_reuse_attempt"] if f == "rejected_reuse_attempt_seconds"
                          else True)]) for f in fields
        },
        "current_timing_incomplete_jobs": [r["audit_id"] for r in rows if r["current_timing_fields_missing"]],
        "historical_accepted_reuse": {
            "unique_prior_audits": len(historical), "records": sorted(historical.values(), key=lambda x: x["reused_from"]),
            "numerical_process_wall_seconds": stats([r["numerical_process_wall_seconds"] for r in historical.values()]),
            "validation_process_wall_seconds": stats([r["validation_process_wall_seconds"] for r in historical.values()]),
            "scope": "Prior solve/check costs deduplicated by source audit directory, separately from this corrected queue. Nested worker/validator internal fields are included in those process walls, not added. The prior run used 36 workers under the same 10.2-CPU quota; these are throttled elapsed timings, not algorithmic CPU costs.",
        },
        "failures": failures, "records": rows,
        "final_input_check": None if final is None else {k: v for k, v in final.items() if k not in {"frozen_files", "source_sha256"}},
        "queue_sha256_matches_execution": execution.get("queue_sha256") == inputs.inventory.get(str((audits / "AUDIT_QUEUE.json").resolve()), {}).get("sha256"),
        "declared_frozen_inputs": {"queue_file_count": len(queue.get("frozen_files", [])),
                                   "scope": "Queue/binding metadata is hashed here. Their already-recorded model/policy/witness hashes are provenance, not a new content-integrity or numerical audit."},
        "accounting_rules": [
            "One unique acquired-experiment audit is charged once; aliases to multiple endpoints/arms do not duplicate its cost.",
            "Accepted reuse has zero new solver time, explicit historical solve/check cost, and new copy/hash plus validation costs.",
            "PROCESS.validation and reuse_attempt.validation describe the same new call and are counted once.",
            "Copied result.elapsed_seconds is historical and is never used as fresh numerical time.",
            "Rejected reuse attempt elapsed time is charged once, then fresh solve/validation separately; nested rejected-attempt fields are not added again.",
            "All completed failed/partial tasks are retained. Missing timings remain null and known totals are lower bounds on recorded work when timings are missing.",
        ],
    }


def quota_report(study, inputs):
    recorded = inputs.json(study.parent / "RESOURCE_LIMITS.json", required=False)
    base = Path("/sys/fs/cgroup/cpu")
    q = inputs.read(base / "cpu.cfs_quota_us", required=False, kind="live_cgroup_controller")
    p = inputs.read(base / "cpu.cfs_period_us", required=False, kind="live_cgroup_controller")
    live = None
    if q is not None and p is not None:
        quota, period = int(q.strip()), int(p.strip())
        live = {"version": 1, "quota_us": quota, "period_us": period,
                "effective_cpu_capacity": quota / period if quota > 0 and period > 0 else None,
                "observed_utc": utcnow()}
    return {"recorded": recorded, "live": live,
            "live_matches_recorded_10_2_cpus": bool(live and close(live["effective_cpu_capacity"], 10.2)),
            "logical_cpus_visible": os.cpu_count(),
            "scope": "The quota, not visible logical CPU count, caps shared-container CPU capacity. This does not establish exclusive access or measure actual CPU consumption."}


def disk_report(roots, largest_count, exclusions):
    outputs = []
    for root in roots:
        before = utcnow()
        logical, allocated, files, links = 0, 0, 0, 0
        unique_allocated, seen, largest, errors = 0, set(), [], []
        manifest = hashlib.sha256()
        for directory, dirs, names in os.walk(root, followlinks=False):
            dirs.sort()
            names.sort()
            for name in names:
                path = Path(directory) / name
                if str(path.resolve()) in exclusions:
                    continue
                try:
                    st = path.lstat()
                    if path.is_symlink():
                        links += 1
                        continue
                    if not path.is_file():
                        continue
                except OSError as exc:
                    errors.append({"path": str(path), "error": repr(exc)})
                    continue
                files += 1
                logical += st.st_size
                allocated += st.st_blocks * 512
                key = (st.st_dev, st.st_ino)
                if key not in seen:
                    unique_allocated += st.st_blocks * 512
                    seen.add(key)
                item = {"path": str(path), "bytes": st.st_size, "mtime_ns": st.st_mtime_ns}
                manifest.update((json.dumps(item, sort_keys=True) + "\n").encode())
                largest.append(item)
                if len(largest) > 2 * largest_count:
                    largest = sorted(largest, key=lambda r: (-r["bytes"], r["path"]))[:largest_count]
        outputs.append({
            "root": str(root), "started_utc": before, "finished_utc": utcnow(),
            "regular_file_count": files, "skipped_file_symlinks": links,
            "logical_bytes": logical, "allocated_bytes_counting_paths": allocated,
            "allocated_bytes_unique_inodes": unique_allocated,
            "stat_inventory_sha256": manifest.hexdigest(), "errors": errors,
            "largest_files": sorted(largest, key=lambda r: (-r["bytes"], r["path"]))[:largest_count],
            "scope": "Stat-only snapshot before report write; no witness contents read. Directory symlinks are not traversed; file symlinks skipped. Concurrently growing outputs may change during traversal.",
        })
    return outputs


def accounting_self_test():
    accepted = {"audit_id": "reuse", "started_utc": "2026-09-23T00:00:00+00:00",
                "finished_utc": "2026-09-23T00:00:15+00:00", "numerical": {"wall_seconds": 0},
                "validation": {"wall_seconds": 10},
                "reuse_attempt": {"status": "accepted", "copy_and_hash_seconds": 2,
                                  "current_copy_and_recheck_seconds": 12,
                                  "historical_numerical_wall_seconds": 300,
                                  "validation": {"wall_seconds": 10}}}
    a = cost_record(accepted)
    assert a["known_current_work_seconds"] == 12 and a["bookkeeping_residual_seconds"] == 3
    assert a["fresh_numerical_seconds"] == 0 and a["fresh_validation_seconds"] == 0
    rejected = {"audit_id": "reject", "numerical": {"wall_seconds": 20},
                "validation": {"wall_seconds": 4},
                "reuse_attempt": {"status": "rejected_fresh_audit_required", "attempt_wall_seconds": 8,
                                  "copy_and_hash_seconds": 2, "validation": {"wall_seconds": 6}}}
    assert cost_record(rejected)["known_current_work_seconds"] == 32
    missing = cost_record({"audit_id": "failed", "numerical": {"wall_seconds": 2}})
    assert missing["known_current_work_seconds"] == 2 and missing["current_timing_fields_missing"]
    assert stats([1, 2, None])["sum"] == 3 and stats([1, 2, None])["missing_count"] == 1


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--study", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--audits", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--allow-incomplete", action="store_true")
    parser.add_argument("--self-check", action="store_true", help="Read and check live schemas/accounting; print a small summary; write no files.")
    parser.add_argument("--disk-root", action="append", type=Path)
    parser.add_argument("--largest", type=int, default=15)
    args = parser.parse_args()
    if args.largest < 1:
        parser.error("--largest must be positive")
    if args.self_check and args.output:
        parser.error("--self-check writes no files and cannot use --output")
    if not args.self_check and not args.output:
        parser.error("Use --output for a report, or --self-check for a read-only schema check")
    if args.output and args.output.exists():
        parser.error("Output already exists; choose a new path to preserve prior reports")
    accounting_self_test()
    study = args.study.resolve()
    audits = (args.audits or study / "exhaustive_audits").resolve()
    inputs = Inputs()
    for name in ["resource_summary.py", "planner.py", "run_queue.py", "run_audits.py", "audit_worker.py", "validate_audits.py"]:
        inputs.read(study / name, kind="source")
    for name in ["SOURCE_LOCK.json", "MODELS.json", "REPORTING_SCOPE_CORRECTIONS.json"]:
        inputs.read(study / name, required=False)
    planning = planning_report(study, inputs)
    audit = audit_report(audits, inputs)
    resource = quota_report(study, inputs)
    finished = (planning["state"] == "finished" and audit["state"] == "finished"
                and audit["recorded_completed_jobs"] == audit["total_unique_jobs"]
                and not planning["missing_runs"])
    if not finished and not (args.self_check or args.allow_incomplete):
        parser.error("Queues are not finished; use --allow-incomplete only for a labeled provisional report")
    if finished and audit["final_input_check"] is None:
        inputs.issue("Finished audit queue has no FINAL_INPUT_CHECK metadata")
    if not audit["queue_sha256_matches_execution"]:
        inputs.issue("Audit queue hash differs from EXECUTION metadata")
    roots = [p.resolve() for p in (args.disk_root or [study])]
    for i, root in enumerate(roots):
        if not root.is_dir():
            parser.error(f"Disk root is not a directory: {root}")
        for previous in roots[:i]:
            if root == previous or root.is_relative_to(previous) or previous.is_relative_to(root):
                parser.error("Disk roots must be disjoint to avoid double-counting")
    disks = [] if args.self_check else disk_report(roots, args.largest, {str(args.output.resolve())})
    changed = inputs.changed()
    if changed:
        inputs.issue("Inputs changed after snapshot: " + ", ".join(changed), "warning" if not finished else "error")
    errors = [e for e in inputs.issues if e["severity"] == "error"]
    if args.self_check:
        print(json.dumps({
            "schema_check": "passed" if not errors else "failed", "scope": "Read-only live metadata/schema/accounting check, not a final report or witness revalidation.",
            "planning_runs": planning["recorded_runs"], "planning_arms": len(planning["by_arm"]),
            "audit_completed_snapshot": audit["recorded_completed_jobs"],
            "accepted_reuse_snapshot": audit["accepted_reuse_count"],
            "quota_verified_10_2": resource["live_matches_recorded_10_2_cpus"],
            "metadata_and_sources_hashed": len(inputs.inventory), "issues": inputs.issues,
            "self_sha256": inputs.inventory[str((study / "resource_summary.py").resolve())]["sha256"],
        }, indent=2))
        return 1 if errors else 0
    report = {
        "schema": "jw-resource-accounting-v1", "created_utc": utcnow(),
        "status": "schema_errors" if errors else ("complete_snapshot" if finished and not changed else "provisional_snapshot"),
        "scope": SCOPE, "study": str(study), "audits": str(audits),
        "measured_cpu_seconds": None, "planning": planning, "audit": audit,
        "resource_limits": resource, "disk": disks, "issues": inputs.issues,
        "source_and_metadata_inventory": sorted(inputs.inventory.values(), key=lambda r: r["path"]),
        "inputs_changed_during_report": changed,
        "binding_scope": "SHA-256 binds exactly the small metadata/source bytes parsed here. Disk contents and large witness files were not rehashed, and this helper does not certify numerical results.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as f:
        json.dump(report, f, indent=2, sort_keys=True, allow_nan=False)
        f.write("\n")
    print(json.dumps({"report": str(args.output.resolve()), "status": report["status"], "issues": inputs.issues}, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
