"""Refresh dated checker bindings after the final replay, without optimizing.

The old reports are retained verbatim. Scientific records must remain identical;
only the hashes of the nineteen replayed CHECK reports may have changed.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())


def write(path, obj):
    path.write_text(json.dumps(obj, indent=2) + "\n")


def main():
    rewards = HERE / "COMPLETE_REWARDS.json"
    previous = read(rewards)
    stale = []
    for section in ("input_sha256", "additional_input_sha256"):
        for path, old_sha in previous[section].items():
            p = Path(path)
            new_sha = sha(p)
            if old_sha != new_sha:
                assert section == "additional_input_sha256"
                assert p.name == "CHECK.json"
                assert p.parent.parent == HERE / "control_audits" or p.parent == HERE / "uniform_audit"
                check = read(p)
                result = p.parent / "result.json"
                assert check["status"] == "passed" and check["result_sha256"] == sha(result)
                assert read(result)["completed_targets"] == 32768
                assert previous[section][str(result)] == sha(result)
                stale.append(dict(path=path, old_sha256=old_sha, new_sha256=new_sha))
    assert len(stale) == 19, "This one-time repair is scoped to Commission 03's nineteen stale bindings."
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d_%H%M%S")
    history = HERE / "binding_history" / stamp
    history.mkdir(parents=True, exist_ok=False)
    files = ["COMPLETE_REWARDS.json", "COMPLETE_COMPARISON.json", "MATCHED_COMPARISON.json",
             "order_completion/MANIFEST.json"]
    before = {}
    for name in files:
        source = HERE / name
        dest = history / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
        before[name] = sha(source)
    subprocess.run([sys.executable, str(HERE / "finish.py")], check=True)
    after = read(rewards)
    for key in previous:
        if key != "additional_input_sha256":
            assert previous[key] == after[key], key
    old_comparison = read(history / "COMPLETE_COMPARISON.json")
    new_comparison = read(HERE / "COMPLETE_COMPARISON.json")
    for key in old_comparison:
        if key != "reward_report_sha256":
            assert old_comparison[key] == new_comparison[key], key
    # The directed diagnostic's job list is unchanged; only its report binding
    # is refreshed. Its original execution manifest remains in binding_history.
    order = HERE / "order_completion/MANIFEST.json"
    obj = read(order)
    assert obj["input_sha256"] == before["COMPLETE_REWARDS.json"]
    obj["input_sha256"] = sha(rewards)
    write(order, obj)
    assert obj["jobs"] == read(history / "order_completion/MANIFEST.json")["jobs"]
    subprocess.run([sys.executable, str(HERE / "finish_matched.py")], check=True)
    old_matched = read(history / "MATCHED_COMPARISON.json")
    new_matched = read(HERE / "MATCHED_COMPARISON.json")
    for key in old_matched:
        if key not in ("input_sha256", "source_sha256"):
            assert old_matched[key] == new_matched[key], key
    checked = 0
    for report in (after, new_matched):
        for section in ("input_sha256", "additional_input_sha256"):
            for path, digest in report.get(section, {}).items():
                assert sha(Path(path)) == digest, path
                checked += 1
    write(HERE / "BINDING_REPAIR.json", dict(
        status="passed", checked_utc=datetime.now(timezone.utc).isoformat(),
        reason="Fresh check replay changed CHECK timestamps, not result files or scientific records.",
        history=str(history.relative_to(HERE)), refreshed_checks=stale,
        original_report_sha256=before,
        current_report_sha256={name: sha(HERE / name) for name in files},
        checked_current_input_bindings=checked,
        records_comparisons_and_directed_jobs_unchanged=True,
        matched_records_unchanged=True, new_optimization=False,
        source_sha256=sha(Path(__file__))))
    print("Refreshed nineteen check bindings; scientific records and directed jobs are unchanged.")


if __name__ == "__main__":
    main()
