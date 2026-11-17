"""Summarize every registered pilot run without selecting successful outcomes.

Reads saved training and independent audits; never trains, changes checkpoints,
or selects a collector using evaluation data. Plots show individual seed runs
and their arithmetic mean, not confidence intervals.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from models import HISTORIES, TARGETS, collector_kernel, target_kernel, true_tables


METHOD_ORDER = ("adversarial", "random", "hardest_uniform", "all_targets")
LABELS = {
    "adversarial": "Learned proposals + hardest",
    "random": "Uniform proposals + random",
    "hardest_uniform": "Uniform proposals + hardest",
    "all_targets": "All targets (extra decoder work)",
}
COLORS = {"adversarial": "#2464a5", "random": "#b94e45",
          "hardest_uniform": "#27916c", "all_targets": "#b38120"}
CASE_LABELS = {"compatible": "Compatible readings", "irreversible": "Irreversible choice",
               "noisy": "Noisy readings"}
TOLERANCE = 1e-7
MATCHED_COUNTERS = ("collector_gradient_steps", "decoder_target_steps", "candidate_queries",
                    "candidate_target_steps", "archive_training_calls")


def read_json(path):
    return json.loads(Path(path).read_text())


def mean_or_none(values):
    return float(np.mean(values)) if values else None


def extrema_or_none(values):
    return {"minimum": float(min(values)), "maximum": float(max(values))} if values else None


def bounds_midpoint(exact):
    return (np.asarray(exact["lower"], dtype=float) + np.asarray(exact["upper"], dtype=float)) / 2


def inspect_run(root, entry, config):
    directory = root / entry["path"]
    trained = read_json(directory / "training.json")
    audits = read_json(directory / "audits.json")
    by_round = {int(a["round"]): a for a in audits}
    true = true_tables(entry["case"])
    noise_counts = np.asarray([int(h[0] == 2) + int(h[2] == 2) for h in HISTORIES]) / 2
    expected_rounds = list(range(int(config["learner"]["rounds"]) + 1))
    checkpoints, selections = [], []
    for checkpoint in trained["checkpoints"]:
        round_id = int(checkpoint["round"])
        audit = by_round[round_id]
        archive = np.asarray(checkpoint["archive"], dtype=int)
        if len(set(archive.tolist())) != len(archive):
            raise ValueError("archive contains repeated target IDs")
        truth, empirical = audit["true"]["exact"], audit["empirical"]["exact"]
        achieved_true = np.asarray(audit["true"]["achieved_archived_decoder_errors"], dtype=float)
        achieved_empirical = np.asarray(audit["empirical"]["achieved_archived_decoder_errors"], dtype=float)
        truth_lower, truth_upper = np.asarray(truth["lower"]), np.asarray(truth["upper"])
        empirical_lower, empirical_upper = np.asarray(empirical["lower"]), np.asarray(empirical["upper"])
        if truth_lower.shape != (27,) or empirical_lower.shape != (27,):
            raise ValueError("audit must retain all 27 deterministic targets")
        if achieved_true.shape != archive.shape or achieved_empirical.shape != archive.shape:
            raise ValueError("archived decoder errors do not match archive IDs")
        if np.any(truth_lower > truth_upper + 1e-9):
            raise ValueError("true audit bounds cross")
        if np.any(achieved_true < truth_lower[archive] - 1e-8):
            raise ValueError("achieved decoder error falls below its audit lower bound")
        policy = np.asarray(checkpoint["policy"], dtype=float)
        E = collector_kernel(true, policy)
        noise_by_world = E @ noise_counts
        model_difference = bounds_midpoint(empirical) - bounds_midpoint(truth)
        gap_low = np.maximum(0, achieved_true - truth_upper[archive])
        gap_high = np.maximum(0, achieved_true - truth_lower[archive])
        empirical_gap_low = np.maximum(0, achieved_empirical - empirical_upper[archive])
        empirical_gap_high = np.maximum(0, achieved_empirical - empirical_lower[archive])
        record = {
            "round": round_id,
            "archive": archive.tolist(),
            "archive_size": int(len(archive)),
            "true_worst_lower": float(truth["worst_lower"]),
            "true_worst_upper": float(truth["worst_upper"]),
            "true_profile_lower": truth_lower.tolist(),
            "true_profile_upper": truth_upper.tolist(),
            "empirical_worst_lower": float(empirical["worst_lower"]),
            "empirical_worst_upper": float(empirical["worst_upper"]),
            "empirical_profile_lower": empirical_lower.tolist(),
            "empirical_profile_upper": empirical_upper.tolist(),
            "model_gap_empirical_minus_true": model_difference.tolist(),
            "model_gap_max_absolute": float(np.abs(model_difference).max()),
            "model_gap_mean_absolute": float(np.abs(model_difference).mean()),
            "true_achieved_decoder_errors_archived": achieved_true.tolist(),
            "empirical_achieved_decoder_errors_archived": achieved_empirical.tolist(),
            "true_max_achieved_decoder_error_archived": float(achieved_true.max()),
            "empirical_max_achieved_decoder_error_archived": float(achieved_empirical.max()),
            "fixed_decoder_error_shift_true_minus_empirical": (achieved_true - achieved_empirical).tolist(),
            "fixed_decoder_error_shift_max_absolute": float(np.abs(achieved_true - achieved_empirical).max()),
            "true_archived_decoder_gap_lower": gap_low.tolist(),
            "true_archived_decoder_gap_upper": gap_high.tolist(),
            "true_max_archived_decoder_gap_lower": float(gap_low.max()),
            "true_max_archived_decoder_gap_upper": float(gap_high.max()),
            "true_mean_archived_decoder_gap_upper": float(gap_high.mean()),
            "empirical_max_archived_decoder_gap_lower": float(empirical_gap_low.max()),
            "empirical_max_archived_decoder_gap_upper": float(empirical_gap_high.max()),
            "empirical_archived_decoder_gap_lower": empirical_gap_low.tolist(),
            "empirical_archived_decoder_gap_upper": empirical_gap_high.tolist(),
            "root_action_probabilities": policy[0].tolist(),
            "root_noise_probability": float(policy[0, 2]),
            "noise_action_fraction_by_world": noise_by_world.tolist(),
            "noise_action_fraction_uniform_world_mean": float(noise_by_world.mean()),
            "counters": checkpoint.get("counters", {}),
            "training_seconds": float(checkpoint.get("training_seconds", 0)),
        }
        checkpoints.append(record)
        candidates = checkpoint.get("candidate_ids", [])
        candidate_errors = checkpoint.get("candidate_errors", [])
        if len(candidates) != len(candidate_errors):
            raise ValueError("candidate IDs/errors differ in length")
        if candidates:
            previous = by_round[round_id - 1]
            ep, tp = previous["empirical"]["exact"], previous["true"]["exact"]
            added = checkpoint.get("added_target")
            for target_id, candidate_error in zip(candidates, candidate_errors):
                target_id, candidate_error = int(target_id), float(candidate_error)
                F = target_kernel(true, target_id)
                world_independent = bool(np.max(np.abs(F - F[0])) <= 1e-12)
                low = candidate_error - float(ep["upper"][target_id])
                high = candidate_error - float(ep["lower"][target_id])
                if high < -1e-8:
                    raise ValueError("candidate error is below previous empirical deficiency")
                selections.append({
                    "round": round_id,
                    "target_id": target_id,
                    "target_tree": list(TARGETS[target_id]),
                    "selected": added is not None and target_id == int(added),
                    "target_world_independent": world_independent,
                    "candidate_empirical_achieved_error": candidate_error,
                    "previous_empirical_deficiency_lower": float(ep["lower"][target_id]),
                    "previous_empirical_deficiency_upper": float(ep["upper"][target_id]),
                    "previous_true_deficiency_lower": float(tp["lower"][target_id]),
                    "previous_true_deficiency_upper": float(tp["upper"][target_id]),
                    "empirical_decoder_fit_gap_lower": max(0.0, low),
                    "empirical_decoder_fit_gap_upper": max(0.0, high),
                    "already_simulable_true_within_tolerance": bool(tp["upper"][target_id] <= TOLERANCE),
                })
    checkpoints.sort(key=lambda d: d["round"])
    complete = [c["round"] for c in checkpoints] == expected_rounds
    selected = [s for s in selections if s["selected"]]
    return {
        **entry,
        "status": "complete" if complete else "incomplete_checkpoints",
        "checkpoint_rounds": [c["round"] for c in checkpoints],
        "checkpoints": checkpoints,
        "candidate_diagnostics": selections,
        "selected_target_count": len(selected),
        "selected_world_independent_targets": sum(s["target_world_independent"] for s in selected),
        "selected_already_simulable_targets": sum(s["already_simulable_true_within_tolerance"] for s in selected),
        "mean_selected_empirical_decoder_fit_gap_upper": mean_or_none([s["empirical_decoder_fit_gap_upper"] for s in selected]),
        "max_selected_empirical_decoder_fit_gap_upper": max((s["empirical_decoder_fit_gap_upper"] for s in selected), default=None),
    }


def paired_comparisons(runs, config):
    lookup = {(r["case"], r["seed"], r["method"]): r for r in runs if r["status"] == "complete"}
    comparisons = []
    for case in config["cases"]:
        for baseline in ("random", "hardest_uniform"):
            if baseline not in config["methods"]:
                continue
            pairs, missing = [], []
            for seed in config["seeds"]:
                left = lookup.get((case, seed, "adversarial"))
                right = lookup.get((case, seed, baseline))
                if left is None or right is None:
                    missing.append(seed)
                    continue
                lvalues = {c["round"]: c["true_worst_upper"] for c in left["checkpoints"]}
                rvalues = {c["round"]: c["true_worst_upper"] for c in right["checkpoints"]}
                last = int(config["learner"]["rounds"])
                differences = [float(lvalues[n] - rvalues[n]) for n in range(1, last + 1)]
                counter_differences = {key: int(left.get("counters", {}).get(key, 0)) - int(right.get("counters", {}).get(key, 0))
                                       for key in MATCHED_COUNTERS}
                pairs.append({"seed": seed,
                              "final_difference": float(lvalues[last] - rvalues[last]),
                              "mean_rounds_1_to_R_difference": mean_or_none(differences),
                              "round_differences_excluding_initial": differences,
                              "matched_counter_differences": counter_differences})
            final = [p["final_difference"] for p in pairs]
            comparisons.append({
                "case": case, "comparison": f"adversarial_minus_{baseline}",
                "sign": "negative favors adversarial; lower true worst-target error is better",
                "pairs": pairs, "missing_or_invalid_pair_seeds": missing,
                "mean_final_difference": mean_or_none(final),
                "mean_rounds_1_to_R_difference": mean_or_none([p["mean_rounds_1_to_R_difference"] for p in pairs]),
                "final_difference_range": extrema_or_none(final),
                "final_wins_ties_losses": {
                    "wins": sum(x < -TOLERANCE for x in final),
                    "ties": sum(abs(x) <= TOLERANCE for x in final),
                    "losses": sum(x > TOLERANCE for x in final),
                },
                "comparison_tolerance": TOLERANCE,
            })
    return comparisons


def group_summaries(runs, config, references):
    groups = []
    for case in config["cases"]:
        for method in config["methods"]:
            selected = [r for r in runs if r["case"] == case and r["method"] == method and r["status"] == "complete"]
            final = [r["checkpoints"][-1] for r in selected]
            floor_ref = references.get(case, {}).get("policy_floor", {})
            optimal_lower, optimal_upper = floor_ref.get("lower"), floor_ref.get("upper")
            counter_keys = sorted({key for r in selected for key in r.get("counters", {})})
            errors = [c["true_worst_upper"] for c in final]
            groups.append({
                "case": case, "method": method,
                "complete_runs": len(selected), "registered_runs": len(config["seeds"]),
                "mean_final_true_worst_upper": mean_or_none(errors),
                "final_true_worst_upper_range": extrema_or_none(errors),
                "mean_final_excess_over_policy_floor_reference_upper": mean_or_none([v - optimal_upper for v in errors]) if optimal_upper is not None else None,
                "mean_final_excess_over_policy_floor_reference_lower": mean_or_none([v - optimal_lower for v in errors]) if optimal_lower is not None else None,
                "mean_final_model_gap_max_absolute": mean_or_none([c["model_gap_max_absolute"] for c in final]),
                "mean_final_max_archived_decoder_gap_upper": mean_or_none([c["true_max_archived_decoder_gap_upper"] for c in final]),
                "mean_final_empirical_max_archived_decoder_gap_upper": mean_or_none([c["empirical_max_archived_decoder_gap_upper"] for c in final]),
                "mean_final_true_max_achieved_decoder_error_archived": mean_or_none([c["true_max_achieved_decoder_error_archived"] for c in final]),
                "mean_final_empirical_max_achieved_decoder_error_archived": mean_or_none([c["empirical_max_achieved_decoder_error_archived"] for c in final]),
                "mean_final_fixed_decoder_error_shift_max_absolute": mean_or_none([c["fixed_decoder_error_shift_max_absolute"] for c in final]),
                "mean_final_noise_action_fraction": mean_or_none([c["noise_action_fraction_uniform_world_mean"] for c in final]),
                "mean_final_root_noise_probability": mean_or_none([c["root_noise_probability"] for c in final]),
                "mean_training_seconds": mean_or_none([float(r.get("training_seconds", 0)) for r in selected]),
                "total_training_seconds": sum(float(r.get("training_seconds", 0)) for r in selected),
                "mean_audit_seconds": mean_or_none([float(r.get("audit_seconds", 0)) for r in selected]),
                "mean_actual_counters": {key: mean_or_none([int(r.get("counters", {}).get(key, 0)) for r in selected]) for key in counter_keys},
                "selected_target_count": sum(r["selected_target_count"] for r in selected),
                "selected_world_independent_targets": sum(r["selected_world_independent_targets"] for r in selected),
                "selected_already_simulable_targets": sum(r["selected_already_simulable_targets"] for r in selected),
            })
    return groups


def plot_curve(ax, runs, method, metric, round_ids, label=True):
    selected = [r for r in runs if r["method"] == method and r["status"] == "complete"]
    if not selected:
        return
    style = "--" if method == "all_targets" else "-"
    values = np.asarray([[next(c[metric] for c in r["checkpoints"] if c["round"] == n) for n in round_ids]
                         for r in selected])
    for row in values:
        ax.plot(round_ids, row, color=COLORS[method], alpha=.18, linewidth=.8, linestyle=style)
    ax.plot(round_ids, values.mean(0), color=COLORS[method], linewidth=2.0, linestyle=style,
            marker="o", markersize=3, label=LABELS[method] if label else None)


def save_figure(fig, output, stem):
    fig.savefig(output / f"{stem}.png", dpi=190, bbox_inches="tight")
    fig.savefig(output / f"{stem}.pdf", bbox_inches="tight")
    plt.close(fig)


def make_figures(summary, output):
    config, runs, references = summary["config"], summary["runs"], summary["references"]
    cases, methods = config["cases"], [m for m in METHOD_ORDER if m in config["methods"]]
    rounds = list(range(int(config["learner"]["rounds"]) + 1))
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                         "axes.titleweight": "bold", "pdf.fonttype": 42})
    fig, axes = plt.subplots(1, len(cases), figsize=(5 * len(cases), 4.4), squeeze=False)
    for ax, case in zip(axes[0], cases):
        case_runs = [r for r in runs if r["case"] == case]
        for method in methods:
            plot_curve(ax, case_runs, method, "true_worst_upper", rounds)
        reference = references.get(case, {}).get("policy_floor")
        if reference:
            ax.axhline(reference["upper"], color="#343434", linestyle=":", linewidth=1.5,
                       label="Best with same action floor")
        ax.set(title=CASE_LABELS.get(case, case), xlabel="Expansion / training round", ylabel="True worst-target simulation error")
        ax.set_xticks(rounds); ax.set_ylim(bottom=0); ax.grid(alpha=.18)
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=min(3, len(labels)), frameon=False,
               bbox_to_anchor=(.5, -.045))
    fig.suptitle("Finite target search: all registered seeds", y=1.01)
    fig.text(.5, -.09, "Faint lines: individual seeds. Thick lines: arithmetic means, not confidence intervals. "
             "All-targets uses extra decoder computation.", ha="center", fontsize=9)
    fig.tight_layout(rect=(0, .085, 1, 1)); save_figure(fig, output, "training_curves")

    seed = config["seeds"][0]
    fig, axes = plt.subplots(1, len(cases), figsize=(5.3 * len(cases), 4.4), squeeze=False)
    target_names = ["".join("LRN"[a] for a in tree) for tree in TARGETS]
    for ax, case in zip(axes[0], cases):
        for method in methods:
            found = [r for r in runs if r["case"] == case and r["method"] == method and r["seed"] == seed and r["status"] == "complete"]
            if found:
                final = found[0]["checkpoints"][-1]
                ax.plot(range(27), final["true_profile_upper"], label=LABELS[method], color=COLORS[method],
                        linewidth=1.5, marker=".", linestyle="--" if method == "all_targets" else "-")
        ax.set_xticks(range(27)); ax.set_xticklabels(target_names, rotation=90, fontsize=7)
        ax.set(title=CASE_LABELS.get(case, case), ylabel="True target simulation error", xlabel="Target tree: initial / after 0 / after 1")
        ax.set_ylim(bottom=0); ax.grid(alpha=.18)
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=2, frameon=False, bbox_to_anchor=(.5, -.055))
    fig.suptitle(f"All 27 final target errors — first registered seed {seed}", y=1.02)
    fig.text(.5, -.095, "L: read left. R: read right. N: request noise. The seed was fixed by manifest order, not selected by performance.",
             ha="center", fontsize=9)
    fig.tight_layout(rect=(0, .08, 1, 1)); save_figure(fig, output, "final_target_profiles")

    fig, axes = plt.subplots(4, len(cases), figsize=(5 * len(cases), 12.4), squeeze=False)
    diagnostics = (("empirical_max_archived_decoder_gap_upper", "Empirical fitted-decoder gap"),
                   ("true_max_archived_decoder_gap_upper", "Deployed decoder gap (true model)"),
                   ("root_noise_probability", "First-action noise probability"),
                   ("noise_action_fraction_uniform_world_mean", "Fraction of actions requesting noise"))
    for column, case in enumerate(cases):
        case_runs = [r for r in runs if r["case"] == case]
        for row, (metric, label) in enumerate(diagnostics):
            ax = axes[row, column]
            for method in methods:
                plot_curve(ax, case_runs, method, metric, rounds)
            ax.set(title=CASE_LABELS.get(case, case) if row == 0 else None, ylabel=label,
                   xlabel="Expansion / training round")
            ax.set_xticks(rounds); ax.set_ylim(bottom=0); ax.grid(alpha=.18)
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=2, frameon=False, bbox_to_anchor=(.5, -.025))
    fig.suptitle("Decoder optimization, model shift, and noise use", y=1.01)
    fig.text(.5, -.055, "Gaps compare the fitted decoder with the optimal decoder for each archived target, then take the maximum.\n"
             "The deployed gap includes fitting and model shift. Noise fraction averages both actions and all worlds; "
             "the second action is irrelevant in the irreversible case.", ha="center", fontsize=9)
    fig.tight_layout(rect=(0, .07, 1, 1)); save_figure(fig, output, "decoder_and_noise")


def fmt(value, digits=6):
    return "missing" if value is None else f"{value:.{digits}f}"


def write_readable(summary, output):
    config = summary["config"]
    lines = ["# Finite adversarial target-search pilot", "", f"Run phase: **{summary['phase']}**.", "",
             f"Input status: {summary['input_status']}; complete analyzed runs: {summary['complete_runs']}/{summary['registered_runs']}.", "",
             "This report retains every registered seed and lists missing or invalid records explicitly. "
             "All three environments were chosen during design. This is model-based training from labelled, resettable-world samples, "
             "with no out-of-class validation. The numerical audits are finite LP evaluations, not formal proofs.", "",
             f"The collector's per-action probability floor is **{config['learner']['probability_floor']}**. "
             "Both unrestricted and floor-matched reference optima are reported. Main methods have matching candidate and collector budgets; "
             "wall time is measured rather than matched. The all-targets diagnostic fits more decoders and is not an equal-compute competitor.", "",
             "## References", "", "| Environment | Unrestricted lower–upper | Action-floor lower–upper |", "| --- | ---: | ---: |"]
    for case, ref in summary["references"].items():
        u, f = ref["unrestricted"], ref["policy_floor"]
        lines.append(f"| {CASE_LABELS.get(case,case)} | {u['lower']:.9f}–{u['upper']:.9f} | {f['lower']:.9f}–{f['upper']:.9f} |")
    lines += ["", "## Final outcomes", "", "| Environment | Method | Runs | Mean true worst error | Root-noise probability | Noise-action fraction |", "| --- | --- | ---: | ---: | ---: | ---: |"]
    for group in summary["groups"]:
        lines.append(f"| {CASE_LABELS.get(group['case'],group['case'])} | {LABELS.get(group['method'],group['method'])} | "
                     f"{group['complete_runs']}/{group['registered_runs']} | {fmt(group['mean_final_true_worst_upper'])} | "
                     f"{fmt(group['mean_final_root_noise_probability'])} | "
                     f"{fmt(group['mean_final_noise_action_fraction'])} |")
    lines += ["", "Root-noise probability concerns the first action. Noise-action fraction averages both actions and all four worlds; "
              "the second action is irrelevant in the irreversible environment. Equal weighting of worlds is used only for this "
              "descriptive noise-use diagnostic; the training objective and simulation audits use worst-world error and no prior.", "", "## Decoder and model diagnostics", "",
              "The empirical fitted-decoder gap compares achieved error with the best decoder for the same empirical model. "
              "The deployed decoder gap makes the same comparison in the true model, so the deployed gap can reflect both "
              "imperfect fitting and empirical-model shift. Each gap is maximized over the archived targets before averaging seeds.", "",
              "| Environment | Method | Empirical fitted-decoder gap | Deployed decoder gap | Empirical achieved loss | True achieved loss | Fixed-decoder loss shift | Optimal-profile model gap |",
              "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for group in summary["groups"]:
        lines.append(f"| {group['case']} | {group['method']} | "
                     f"{fmt(group['mean_final_empirical_max_archived_decoder_gap_upper'])} | "
                     f"{fmt(group['mean_final_max_archived_decoder_gap_upper'])} | "
                     f"{fmt(group['mean_final_empirical_max_achieved_decoder_error_archived'])} | "
                     f"{fmt(group['mean_final_true_max_achieved_decoder_error_archived'])} | "
                     f"{fmt(group['mean_final_fixed_decoder_error_shift_max_absolute'])} | "
                     f"{fmt(group['mean_final_model_gap_max_absolute'])} |")
    lines += ["", "Achieved losses are each seed's largest archived-target error using the actual fitted decoders. "
              "Fixed-decoder loss shift is the largest absolute empirical-versus-true change for those same decoders. "
              "Optimal-profile model gap instead compares the optimal deficiency in each model across all 27 targets. "
              "The optimal-profile gap may be small even when a particular fitted decoder changes substantially between models.", "",
              "## Paired comparisons", "", "Differences are adversarial minus the named control; negative favors adversarial. "
              "The across-round measure averages rounds 1 through the registered final round, excluding initialization. "
              "Wins/ties/losses use tolerance 1e-7 and describe these seeds only.", "",
              "| Environment | Control | Mean final difference | Mean rounds 1–R difference | Wins / ties / losses |", "| --- | --- | ---: | ---: | ---: |"]
    for pair in summary["paired_comparisons"]:
        w = pair["final_wins_ties_losses"]
        lines.append(f"| {CASE_LABELS.get(pair['case'],pair['case'])} | {pair['comparison'].replace('adversarial_minus_', '')} | "
                     f"{fmt(pair['mean_final_difference'])} | {fmt(pair['mean_rounds_1_to_R_difference'])} | {w['wins']} / {w['ties']} / {w['losses']} |")
    lines += ["", "Every seed's signed differences are retained in SUMMARY.json, including losses and missing pairs.", "",
              "## Selection diagnostics", "", "Candidate errors are compared with the previous checkpoint's collector, before adding the candidate. "
              "A target can look difficult because its decoder is undertrained or the empirical model is inaccurate. "
              "An already simulable target need not be pure noise; both counts are therefore retained.", "",
              "| Environment | Method | Selected targets | World-independent targets | Already simulable in true model |", "| --- | --- | ---: | ---: | ---: |"]
    for group in summary["groups"]:
        lines.append(f"| {group['case']} | {group['method']} | {group['selected_target_count']} | "
                     f"{group['selected_world_independent_targets']} | {group['selected_already_simulable_targets']} |")
    lines += ["", "## Actual computation", "", "| Environment | Method | Mean training seconds | Mean decoder-target updates | Mean candidate queries | Mean generator updates |", "| --- | --- | ---: | ---: | ---: | ---: |"]
    for group in summary["groups"]:
        count = group["mean_actual_counters"]
        lines.append(f"| {group['case']} | {group['method']} | {fmt(group['mean_training_seconds'],3)} | "
                     f"{fmt(count.get('decoder_target_steps'),0)} | {fmt(count.get('candidate_queries'),0)} | {fmt(count.get('generator_gradient_steps'),0)} |")
    lines += ["", "## Missing or invalid records", ""]
    if summary["failures"]:
        lines.extend(f"- {record['case']}, seed {record['seed']}, {record['method']}: {record['error']}" for record in summary["failures"])
    else:
        lines.append("None among the registered runs.")
    lines += ["", "## Figures", "", "- `training_curves.png` / `.pdf`: means and all individual seed trajectories; no confidence intervals.",
              "- `final_target_profiles.png` / `.pdf`: all 27 targets for the first registered seed, chosen before outcomes.",
              "- `decoder_and_noise.png` / `.pdf`: empirical and deployed decoder gaps, root-noise probability, and the fraction of noise actions.", "",
              "These results establish no convergence guarantee, approximation guarantee for eventual J_w, or superiority on unseen world classes. "
              "Positive minimax error can be an unavoidable tradeoff. No true-model audit was used to choose targets or update the learner.", ""]
    (output / "RESULTS.md").write_text("\n".join(lines))


def run(input_root, output):
    root, output = Path(input_root).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = read_json(root / "manifest.json")
    config = manifest["config"]
    models_hash = hashlib.sha256(Path(__file__).with_name("models.py").read_bytes()).hexdigest()
    expected_models_hash = manifest.get("source_sha256", {}).get("models.py")
    if expected_models_hash is not None and models_hash != expected_models_hash:
        raise ValueError("Live models.py differs from the registered source; use the frozen study model before recomputing noise metrics")
    summary_path = root / "summary.json"
    completed = read_json(summary_path) if summary_path.exists() else read_json(root / "progress.json")["completed"]
    entries = {(r["case"], r["seed"], r["method"]): r for r in completed}
    runs, failures = [], []
    for case in config["cases"]:
        for seed in config["seeds"]:
            for method in config["methods"]:
                entry = entries.get((case, seed, method))
                if entry is None:
                    failures.append({"case": case, "seed": seed, "method": method, "error": "no completed run entry"})
                    continue
                try:
                    record = inspect_run(root, entry, config)
                    runs.append(record)
                    if record["status"] != "complete":
                        failures.append({"case": case, "seed": seed, "method": method, "error": "missing registered checkpoint rounds"})
                except (ValueError, KeyError, OSError, ArithmeticError) as error:
                    failures.append({"case": case, "seed": seed, "method": method, "error": f"{type(error).__name__}: {error}"})
    references = {}
    for case in config["cases"]:
        path = root / case / "reference.json"
        if path.exists():
            saved = read_json(path)
            references[case] = {name: {key: value for key, value in ref.items() if key in
                                       ("lower", "upper", "value", "duality_gap", "min_action_probability", "feasibility", "certificate_kind")}
                                for name, ref in saved.items()}
    summary = {
        "phase": manifest["phase"], "input_root": str(root),
        "input_status": manifest["status"], "config": config,
        "manifest_sha256": hashlib.sha256((root / "manifest.json").read_bytes()).hexdigest(),
        "training_source_sha256": manifest.get("source_sha256", {}),
        "report_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "report_models_sha256": models_hash,
        "registered_runs": len(config["cases"]) * len(config["seeds"]) * len(config["methods"]),
        "complete_runs": sum(r["status"] == "complete" for r in runs),
        "failures": failures, "references": references, "runs": runs,
        "paired_comparisons": paired_comparisons(runs, config),
        "groups": group_summaries(runs, config, references),
        "figure_seed_rule": "first registered seed in manifest order, irrespective of performance",
        "plots_are_confidence_intervals": False,
        "scope": "Finite, sampled-data model-based training with labelled reset access; all worlds known in design; no unseen-class or eventual-score claim.",
    }
    # Serialization fails rather than silently converting invalid metrics to NaN.
    (output / "SUMMARY.json").write_text(json.dumps(summary, indent=2, allow_nan=False) + "\n")
    compact = {key: value for key, value in summary.items() if key != "runs"}
    compact["detail_location"] = "SUMMARY.json and the per-run training/audit files retain checkpoint arrays; regenerate those files using REPRODUCE.txt."
    (output / "COMPACT_SUMMARY.json").write_text(json.dumps(compact, indent=2, allow_nan=False) + "\n")
    write_readable(summary, output)
    make_figures(summary, output)
    print(f"Analyzed {summary['complete_runs']}/{summary['registered_runs']} registered runs; {len(failures)} missing/invalid records.")
    print(f"Wrote SUMMARY.json, COMPACT_SUMMARY.json, RESULTS.md and three PNG/PDF figures to {output}")
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    run(args.input, args.output)
