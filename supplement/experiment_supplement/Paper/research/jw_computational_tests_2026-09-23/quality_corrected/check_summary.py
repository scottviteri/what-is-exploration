#!/usr/bin/env python3
"""Independently check exported summary CSVs against their frozen source records.

Standard library only: no summarizer, planner, numerical library or solver imports.
This checks reporting and provenance; it does not repeat the numerical witness
audits, turn floating-point bounds into exact certificates, or infer all optima.
Run only after the audit queue and summary are complete. --self-test uses synthetic
records only and neither reads study outcomes nor writes persistent study files.
"""
from __future__ import annotations

import argparse
import collections
import csv
import datetime
import hashlib
import io
import json
import math
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASELINES = ("information", "brier", "uniform")
ADAPTIVE = ("tractability", "hard")
METHOD_ARM = {
    "fixed": "fixed", "tractability": "tractability", "hard": "hard",
    "minimax": "minimax", "information": "baseline", "brier": "baseline",
    "uniform": "baseline", "tractability_average": "tractability",
    "hard_average": "hard",
    **{f"{r}_face{p}": f"{r}_face{p}" for r in ("information", "brier") for p in (0, 1, 5)},
}
MARGIN = 1e-6
AUDIT_TOL = 2e-7


def number(value):
    if value is None or value == "":
        return None
    result = float(value)
    if not math.isfinite(result):
        raise ValueError(f"Nonfinite numeric value: {value!r}")
    return result


def boolean(value):
    if value is True or value == "True":
        return True
    if value is False or value == "False":
        return False
    raise ValueError(f"Not an explicit boolean: {value!r}")


def csv_scalar(value):
    if value is None:
        return ""
    if isinstance(value, (dict, list)):
        return json.dumps(value, sort_keys=True)
    return str(value)


def tail_mass():
    # Sum the original mass of the 128 depth-3 deterministic targets and the
    # three literal uniform-action targets. Do not normalize the retained mass.
    deterministic = 128 * Fraction(1, 2 ** 5 * 2 ** 21)
    uniform = sum((Fraction(1, 2 ** (n + 3) * 3 ** ((4 ** n - 1) // 3))
                   for n in (1, 2, 3)), Fraction(0))
    return Fraction(1, 20) * (1 - deterministic - uniform)


def interval_from_validation(validation):
    lo, hi = number(validation.get("audit_lower")), number(validation.get("audit_upper"))
    if lo is None or hi is None:
        return None
    if lo > hi + AUDIT_TOL or lo < -AUDIT_TOL or hi > 1 + AUDIT_TOL:
        return None
    # This repeats the declared numerical clipping convention, not a proof that
    # an inverted or out-of-range numerical interval is an exact certificate.
    return tuple(max(0.0, min(1.0, x)) for x in sorted((lo, hi)))


def pair_result(arm, baseline):
    if not boolean(arm["comparison_eligible"]) or not boolean(baseline["comparison_eligible"]):
        return "unavailable", None, None
    lo = number(arm["audit_lower"]) - number(baseline["audit_upper"])
    hi = number(arm["audit_upper"]) - number(baseline["audit_lower"])
    result = "win" if hi < -MARGIN else "loss" if lo > MARGIN else "overlap_or_within_margin"
    return result, lo, hi


def expected_keys(queue):
    models = [m["id"] for m in queue["models"]]
    budgets = queue["checkpoints"]
    return {(model, method, int(budget)) for model in models
            for method in METHOD_ARM for budget in budgets}


def endpoint_name(method, budget):
    if method in BASELINES:
        return method
    return ("average_checkpoint_" if method.endswith("_average") else "checkpoint_") + str(budget)


def unique_index(rows, fields):
    result = {}
    for row in rows:
        key = tuple(row[field] for field in fields)
        if key in result:
            raise ValueError(f"Duplicate {fields}: {key}")
        result[key] = row
    return result


class Review:
    def __init__(self):
        self.errors = []
        self.checks = 0
        self.json_cache = {}
        self.hashes = {}

    def require(self, condition, reason):
        self.checks += 1
        if not condition:
            self.errors.append(reason)

    def same(self, actual, expected, reason):
        self.require(actual == expected, reason + f": {actual!r} != {expected!r}")

    def numeric(self, actual, expected, reason, tolerance=1e-12):
        a, b = number(actual), number(expected)
        self.require(a is b if a is None or b is None else abs(a - b) <= tolerance,
                     reason + f": {a!r} != {b!r}")

    def digest(self, path):
        path = Path(path).resolve()
        if not path.exists():
            return None
        h = hashlib.sha256()
        with path.open("rb") as stream:
            for data in iter(lambda: stream.read(1024 * 1024), b""):
                h.update(data)
        self.hashes[str(path)] = h.hexdigest()
        return h.hexdigest()

    def read(self, path, optional=False):
        path = Path(path).resolve()
        if path in self.json_cache:
            return self.json_cache[path]
        if optional and not path.exists():
            return {}
        data = path.read_bytes()
        self.hashes[str(path)] = hashlib.sha256(data).hexdigest()
        self.json_cache[path] = json.loads(data)
        return self.json_cache[path]

    def csv(self, path):
        path = Path(path).resolve()
        data = path.read_bytes()
        self.hashes[str(path)] = hashlib.sha256(data).hexdigest()
        return list(csv.DictReader(io.StringIO(data.decode(), newline="")))


def resolve(path, base):
    p = Path(path)
    return (p if p.is_absolute() else base / p).resolve()


def validate(study, audits, summary):
    review = Review()
    queue = review.read(study / "QUEUE.json")
    model_list = review.read(study / "MODELS.json")["models"]
    models = unique_index(model_list, ("id",))
    frozen = review.read(audits / "AUDIT_QUEUE.json")
    final = review.read(audits / "FINAL_INPUT_CHECK.json")
    status = review.read(audits / "STATUS.json")
    planning_status = review.read(study / "PLANNING_STATUS.json")
    meta = review.read(summary / "summary.json")["metadata"]
    binding_doc = review.read(audits / "BINDINGS.json")
    bindings = unique_index(binding_doc["bindings"], ("model", "arm", "endpoint"))
    raw_rows = review.csv(summary / "endpoints.csv")
    rows = unique_index(raw_rows, ("model", "method", "budget_seconds"))
    processes = review.csv(summary / "planning_processes.csv")
    process_index = unique_index(processes, ("model", "arm"))
    pairs = review.csv(summary / "paired_comparisons.csv")
    pair_index = unique_index(pairs, ("model", "method", "budget_seconds", "baseline"))
    binding_csv = unique_index(review.csv(summary / "all_audit_bindings.csv"),
                               ("model", "arm", "endpoint"))
    expected = expected_keys(queue)
    actual = {(m, method, int(budget)) for m, method, budget in rows}
    expected_bindings = {(m, METHOD_ARM[method], endpoint_name(method, b)) for m, method, b in expected}
    expected_processes = {(m["id"], arm) for m in queue["models"] for arm in queue["arms"]}
    expected_pairs = {(m, method, str(b), baseline) for m, method, b in expected
                      if method not in BASELINES for baseline in BASELINES}

    review.same(len(queue["models"]), 12, "Frozen model count")
    review.same(set(queue["arms"]), set(METHOD_ARM.values()), "Frozen arms")
    review.same(queue["checkpoints"], [2, 10, 40], "Frozen budgets")
    review.same({key[0] for key in models}, {m["id"] for m in queue["models"]}, "Model inventory keys")
    review.same(len(raw_rows), 540, "Endpoint count")
    review.same(actual, expected, "Endpoint key coverage")
    review.same(len(processes), 132, "Process count")
    review.same(set(process_index), expected_processes, "Process key coverage")
    review.same(len(expected_bindings), 468, "Applicable binding count")
    review.same(set(bindings), expected_bindings, "Raw binding coverage")
    review.same(binding_doc.get("expected_endpoint_count"), 468, "Binding manifest expected count")
    review.same(set(binding_csv), set(bindings), "CSV binding coverage")
    review.same(len(pairs), 1296, "Paired row count")
    review.same(set(pair_index), expected_pairs, "Paired key coverage")
    review.same(final.get("status"), "passed", "Final input integrity")
    review.same(final.get("changed_paths", []), [], "Changed audit inputs")
    review.same(final.get("changed_sources", []), [], "Changed audit sources")
    review.same(status.get("state"), "finished", "Audit queue finished")
    review.same(planning_status.get("state"), "finished", "Planning queue finished")
    review.same(meta.get("status"), "final_snapshot", "Summary final snapshot")
    review.same(meta.get("summary_input_changes", []), [], "Summary input changes")
    review.same(meta.get("read_errors", []), [], "Summary read errors")
    review.same(review.digest(study / "summarize.py"), meta.get("summary_source_sha256"), "Summary producer hash")
    review.same(review.digest(study / "REPORT_TEMPLATE.md"), meta.get("template_sha256"), "Report template hash")
    for path, expected_hash in meta.get("input_sha256", {}).items():
        review.same(review.digest(resolve(path, study)), expected_hash, "Summary source snapshot " + path)
    review.same(review.digest(audits / "BINDINGS.json"), frozen["bindings_sha256"], "Frozen binding hash")
    for group in ("frozen_files", "source_sha256"):
        for path, expected_hash in frozen[group].items():
            review.same(review.digest(resolve(path, study)), expected_hash, "Frozen file " + path)
    for key, binding in bindings.items():
        exported = binding_csv.get(key, {})
        for field, value in binding.items():
            review.same(exported.get(field, ""), csv_scalar(value), f"Binding CSV {key}/{field}")
        review.same(exported.get("structurally_not_applicable"), "False", f"Applicable binding {key}")

    for key, process_row in process_index.items():
        folder = study / "runs" / key[0] / key[1]
        process = review.read(folder / "PROCESS.json")
        result = review.read(folder / "result.json", optional=True)
        check = review.read(folder / "PLANNING_CHECK.json")
        review.same(process_row["process_exit"], csv_scalar(process.get("exit")), f"Process exit {key}")
        review.same(process_row["planner_status"], csv_scalar(result.get("status")), f"Planner status {key}")
        review.same(process_row["planning_check"], csv_scalar(check.get("status", "missing")), f"Planning validation {key}")
        review.numeric(process_row["wall_seconds"], process.get("wall_seconds"), f"Process wall time {key}")

    for (mid, method, budget_string), row in rows.items():
        budget = int(budget_string)
        arm = METHOD_ARM[method]
        endpoint = endpoint_name(method, budget)
        tag = f"{mid}/{method}/{budget}"
        folder = study / "runs" / mid / arm
        policy = folder / endpoint / "policy.npz"
        polmeta = review.read(policy.with_suffix(".json"), optional=True)
        runmeta = review.read(folder / "metadata.json", optional=True)
        check = review.read(folder / "PLANNING_CHECK.json")
        binding = bindings[(mid, arm, endpoint)]
        review.same(row["arm"], arm, "Arm " + tag)
        review.same(row["endpoint"], endpoint, "Endpoint " + tag)
        review.same(resolve(row["policy_path"], study), policy.resolve(), "Policy path " + tag)
        review.same(boolean(row["policy_present"]), policy.exists(), "Policy existence " + tag)
        review.same(boolean(row["secondary"]), method.endswith("_average"), "Secondary flag " + tag)
        role = "secondary_realization_average" if method.endswith("_average") else "primary_40s" if budget == 40 else "earlier_checkpoint"
        review.same(row["analysis_role"], role, "Analysis role " + tag)
        review.same(row["planning_check_status"], check.get("status", "missing"), "Planning status " + tag)
        for field in ("available_seconds", "iteration", "selected_lower", "selected_upper", "selected_gap"):
            review.numeric(row[field], polmeta.get(field), field + " " + tag)
        review.numeric(row["baseline_reward"], polmeta.get("reward"), "Baseline reward " + tag)
        review.numeric(row["baseline_optimal_reward"], polmeta.get("optimal_reward"), "Baseline optimum " + tag)

        if arm in ("fixed", *ADAPTIVE):
            tail = polmeta.get("omitted_mass", runmeta.get("omitted_mass"))
            review.require(tail is not None, "Missing weighted tail " + tag)
            if tail is not None:
                review.same(Fraction(tail), tail_mass(), "Original tail " + tag)
                review.same(Fraction(row["omitted_mass"]), tail_mass(), "CSV tail " + tag)
                review.numeric(row["omitted_mass_float"], float(tail_mass()), "Tail float " + tag)
            gap = number(polmeta.get("selected_gap"))
            total = None if gap is None else max(0.0, gap) + float(tail_mass())
            review.numeric(row["selected_gap_plus_omitted_tail"], total, "Gap plus tail " + tag)
            if method.endswith("_average"):
                review.same(row["selected_gap_plus_omitted_tail"], "", "No invented average regret " + tag)
        else:
            review.same(row["omitted_mass"], "", "No rich tail for other objective " + tag)

        face = runmeta.get("face")
        if face:
            for column, field in (("reward_optimum", "maximum"), ("reward_minimum", "minimum"),
                                  ("reward_range", "range"), ("reward_threshold", "threshold"),
                                  ("reward_allowed_slack", "slack"), ("reward_numerical_slack", "numerical_slack")):
                review.numeric(row[column], face.get(field), "Face " + column + " " + tag)
            if polmeta.get("iteration") is not None:
                record = review.read(folder / f"round_{int(polmeta['iteration']):03d}" / "record.json")
                actual_reward = number(record.get("actual_reward"))
                review.numeric(row["actual_reward"], actual_reward, "Actual face reward " + tag)
                review.numeric(row["face_repair_mixture"], record.get("face_repair_mixture"), "Face repair " + tag)
                if actual_reward is not None:
                    review.numeric(row["reward_threshold_shortfall"], max(0.0, face["threshold"] - actual_reward), "Face shortfall " + tag)

        available = number(polmeta.get("available_seconds"))
        aid = binding.get("audit_id")
        av, ar = {}, {}
        if not policy.exists():
            expected_status = "missing_policy"
        elif available is None:
            expected_status = "missing_availability_time"
        elif available > budget:
            expected_status = "late_for_checkpoint"
        elif check.get("status") != "passed":
            expected_status = "planning_validation_" + check.get("status", "missing")
        elif binding.get("status") == "invalid":
            expected_status = "audit_binding_invalid"
        elif not aid:
            expected_status = "audit_not_queued"
        else:
            model = models[(mid,)]
            review.same(review.digest(policy), binding.get("policy_sha256"), "Policy binding " + tag)
            review.same(binding.get("model_sha256"), model["sha256"], "Model binding " + tag)
            review.same(review.digest(resolve(model["path"], study)), model["sha256"], "Model input " + tag)
            if binding.get("policy_metadata_sha256"):
                review.same(review.digest(policy.with_suffix(".json")), binding["policy_metadata_sha256"], "Policy metadata binding " + tag)
            av = review.read(audits / "audits" / aid / "validation.json", optional=True)
            ar = review.read(audits / "audits" / aid / "result.json", optional=True)
            review.same(row["audit_id"], aid, "Audit ID " + tag)
            review.same(row["exact_E_sha256"], binding.get("exact_E_sha256"), "Audit experiment binding " + tag)
            if av.get("status") != "passed":
                expected_status = "audit_validation_" + av.get("status", "pending")
            elif interval_from_validation(av) is None:
                expected_status = "invalid_audit_interval"
            else:
                complete = (ar.get("status") == "complete" and ar.get("complete") is True
                            and av.get("complete") is True and av.get("completed_target_count") == 32768)
                expected_status = "validated_complete" if complete else "validated_partial"
                review.same(boolean(row["audit_complete"]), complete, "Audit completeness " + tag)
                review.same(int(row["audit_completed_targets"]), av["completed_target_count"], "Audit coverage " + tag)
                review.same(int(row["audit_expected_targets"]), 32768, "Audit denominator " + tag)
                for column, value in zip(("audit_lower", "audit_upper"), interval_from_validation(av)):
                    review.numeric(row[column], value, "Validated " + column + " " + tag)
                for column in ("audit_lower", "audit_upper"):
                    review.numeric(row[column.replace("audit_", "audit_raw_")], av[column], "Raw " + column + " " + tag)
                if not complete:
                    review.require(av.get("global_upper_source") in ("universal TV bound", "full-revelation decoder", "complete target uppers and full-revelation upper"), "Partial audit global upper " + tag)
        eligible = expected_status in ("validated_complete", "validated_partial")
        review.same(row["endpoint_status"], expected_status, "Endpoint status " + tag)
        review.same(boolean(row["comparison_eligible"]), eligible, "Comparison eligibility " + tag)
        if not eligible:
            review.same(row["audit_lower"], "", "Unavailable lower " + tag)
            review.same(row["audit_upper"], "", "Unavailable upper " + tag)

    for mid in (m["id"] for m in queue["models"]):
        for baseline in BASELINES:
            copies = [rows[(mid, baseline, str(b))] for b in queue["checkpoints"]]
            for field in ("policy_path", "available_seconds", "baseline_reward", "baseline_optimal_reward"):
                review.same(len({r[field] for r in copies}), 1, f"Reused baseline {mid}/{baseline}/{field}")
            eligible = [r for r in copies if boolean(r["comparison_eligible"])]
            for field in ("audit_id", "audit_lower", "audit_upper", "exact_E_sha256"):
                review.require(len({r[field] for r in eligible}) <= 1, f"Reused baseline audit {mid}/{baseline}/{field}")

    pair_groups = collections.Counter()
    for (mid, method, budget, baseline), pair in pair_index.items():
        arm_row, baseline_row = rows[(mid, method, budget)], rows[(mid, baseline, budget)]
        label, lo, hi = pair_result(arm_row, baseline_row)
        tag = f"{mid}/{method}/{budget}/{baseline}"
        review.same(pair["classification"], label, "Pair classification " + tag)
        review.numeric(pair["difference_lower"], lo, "Pair difference lower " + tag)
        review.numeric(pair["difference_upper"], hi, "Pair difference upper " + tag)
        review.numeric(pair["margin"], MARGIN, "Pair margin " + tag)
        for prefix, source in (("arm", arm_row), ("baseline", baseline_row)):
            for field in ("lower", "upper"):
                review.numeric(pair[f"{prefix}_{field}"], source[f"audit_{field}"], "Pair bound " + tag)
            review.same(pair[f"{prefix}_status"], source["endpoint_status"], "Pair status " + tag)
            review.same(pair[f"{prefix}_audit_id"], source["audit_id"], "Pair identity " + tag)
            review.numeric(pair[f"{prefix}_available_seconds"], source["available_seconds"], "Pair timing " + tag)
        review.numeric(pair["arm_selected_gap"], arm_row["selected_gap"], "Pair planning gap " + tag)
        review.same(pair["arm_omitted_mass"], arm_row["omitted_mass"], "Pair tail " + tag)
        pair_groups[(method, budget, baseline)] += 1
    review.require(all(n == 12 for n in pair_groups.values()), "Twelve settings in every paired denominator")
    review.same(len(pair_groups), 108, "Number of paired denominators")
    review.same(meta.get("endpoint_status_counts"), dict(collections.Counter(r["endpoint_status"] for r in raw_rows)), "Summary coverage totals")
    review.same(meta.get("pair_classification_counts"), dict(collections.Counter(r["classification"] for r in pairs)), "Summary pair totals")
    review.same(Fraction(meta["background_omitted_mass"]), tail_mass(), "Summary tail")

    # Detect changes during the reporting check, retaining the original digest.
    input_hashes = dict(review.hashes)
    for path, old_hash in input_hashes.items():
        review.same(review.digest(path), old_hash, "Input changed while checking " + path)
    return {
        "status": "passed" if not review.errors else "failed",
        "checked_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "checks": review.checks, "errors": review.errors,
        "scientific_endpoint_rows": len(raw_rows), "paired_rows": len(pairs),
        "planning_process_rows": len(processes), "applicable_bindings": len(expected_bindings),
        "input_sha256": input_hashes,
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Independent standard-library reporting/provenance check against frozen raw metadata and previously independently validated numerical intervals. No solvers, witness revalidation, outcome selection, exact arithmetic certification of numerical bounds, or all-optima claim.",
    }


class SyntheticTests(unittest.TestCase):
    def test_grid(self):
        queue = {"models": [{"id": f"m{i}"} for i in range(12)], "checkpoints": [2, 10, 40]}
        keys = expected_keys(queue)
        self.assertEqual(len(keys), 540)
        self.assertEqual(len({(m, METHOD_ARM[method], endpoint_name(method, b)) for m, method, b in keys}), 468)
        self.assertEqual(sum(method not in BASELINES for _, method, _ in keys) * 3, 1296)

    def test_tail(self):
        self.assertEqual(tail_mass(), Fraction(5369266971004237, 109684753201889280))
        self.assertTrue(Fraction(48, 1000) < tail_mass() < Fraction(49, 1000))

    def test_pair_rules(self):
        def row(lo, hi, eligible=True):
            return {"comparison_eligible": str(eligible), "audit_lower": str(lo), "audit_upper": str(hi)}
        self.assertEqual(pair_result(row(.1, .2), row(.3, .4)), ("win", -.30000000000000004, -.09999999999999998))
        self.assertEqual(pair_result(row(.3, .4), row(.1, .2))[0], "loss")
        self.assertEqual(pair_result(row(.1, .3), row(.2, .4))[0], "overlap_or_within_margin")
        self.assertEqual(pair_result(row(.1, .2), row(.2 + MARGIN / 2, .3))[0], "overlap_or_within_margin")
        self.assertEqual(pair_result(row(0, 1), row(.3, .4))[0], "overlap_or_within_margin")
        self.assertEqual(pair_result(row("", "", False), row(.3, .4)), ("unavailable", None, None))

    def test_interval_convention(self):
        def bracket(lo, hi):
            return interval_from_validation({"audit_lower": lo, "audit_upper": hi})
        self.assertEqual(bracket(-1e-10, -.5e-10), (0., 0.))
        self.assertEqual(bracket(1 + 1e-10, 1 + 2e-10), (1., 1.))
        self.assertEqual(bracket(.3 + 1e-9, .3), (.3, .3 + 1e-9))
        self.assertIsNone(bracket(.4, .3))
        self.assertIsNone(bracket(-1e-4, .3))
        self.assertIsNone(bracket(None, .3))
        with self.assertRaises(ValueError):
            bracket(float("nan"), 1)

    def test_duplicate_rejection(self):
        with self.assertRaises(ValueError):
            unique_index([{"id": "same"}, {"id": "same"}], ("id",))

    def test_explicit_types(self):
        self.assertFalse(boolean("False"))
        self.assertTrue(boolean("True"))
        with self.assertRaises(ValueError):
            boolean("")
        self.assertIsNone(number(""))
        with self.assertRaises(ValueError):
            number("inf")

    def test_review_records_corruption(self):
        review = Review()
        review.same("changed", "frozen", "tampered hash")
        review.numeric("0.31", .3, "tampered interval")
        review.numeric("", None, "honest missingness")
        self.assertEqual(review.checks, 3)
        self.assertEqual(len(review.errors), 2)

    def test_json_and_csv_provenance(self):
        # Temporary synthetic fixtures only, deleted on exit.
        with tempfile.TemporaryDirectory(prefix="jw-summary-test-") as temporary:
            root = Path(temporary)
            (root / "fixture.json").write_text('{"value": 3}\n')
            (root / "fixture.csv").write_text('id,value\nsynthetic,3\n')
            review = Review()
            self.assertEqual(review.read(root / "fixture.json"), {"value": 3})
            self.assertEqual(review.csv(root / "fixture.csv"), [{"id": "synthetic", "value": "3"}])
            self.assertEqual(len(review.hashes), 2)
            self.assertEqual(review.digest(root / "absent"), None)

    def test_csv_keeps_multiline_failure_text(self):
        with tempfile.TemporaryDirectory(prefix="jw-summary-test-") as temporary:
            path = Path(temporary) / "failure.csv"
            path.write_text('id,error\nsynthetic,"first line\nsecond line"\n')
            self.assertEqual(Review().csv(path), [{"id": "synthetic", "error": "first line\nsecond line"}])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--study", type=Path, default=HERE)
    parser.add_argument("--audits", type=Path)
    parser.add_argument("--summary", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(SyntheticTests))
        raise SystemExit(0 if result.wasSuccessful() else 1)
    if args.audits is None or args.summary is None:
        parser.error("--audits and --summary are required; run only after both are complete")
    output = args.output or args.summary / "SUMMARY_CHECK.json"
    try:
        report = validate(args.study.resolve(), args.audits.resolve(), args.summary.resolve())
    except Exception as error:
        report = {"status": "failed", "error": repr(error), "scope": "Reporting check stopped; no numerical solver or aggregation was run."}
    output.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "input_sha256"}, indent=2))
    raise SystemExit(0 if report["status"] == "passed" else 1)


if __name__ == "__main__":
    main()
