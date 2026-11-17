"""Independent semantic checks for the finite adversarial-learning pilot.

Run from this directory with ``python3 test_pilot.py``.  The tests use manually
specified probability laws and the repository's existing dense deficiency LP
as an evaluator independent of the pilot's new channel/oracle implementation.
No claim about optimization success is made merely because these checks pass.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "Experiments" / "src"))
from idexp.lp import deficiency as reference_deficiency

WORLDS = list(itertools.product(range(2), repeat=2))
HISTORIES = list(itertools.product(range(3), range(2), range(3), range(2)))
OUTPUTS = list(itertools.product(range(2), repeat=2))
TARGETS = list(itertools.product(range(3), repeat=3))


def observation_probability(case, world, action, observation, depth):
    """Hand-written environment law, independent of models.py's table builder."""
    if case == "irreversible" and depth == 1:
        return float(observation == 0)
    if action == 2:
        return 0.5
    correct = observation == world[action]
    if case == "noisy":
        return 0.85 if correct else 0.15
    return float(correct)


def manual_collector(case, policy):
    result = np.zeros((4, 36))
    for world_id, world in enumerate(WORLDS):
        for history_id, (a0, o0, a1, o1) in enumerate(HISTORIES):
            result[world_id, history_id] = (
                policy[0, a0]
                * observation_probability(case, world, a0, o0, 0)
                * policy[1 + 2 * a0 + o0, a1]
                * observation_probability(case, world, a1, o1, 1)
            )
    return result


def manual_target(case, target):
    observations = np.zeros((4, 4))
    full_history = np.zeros((4, 36))
    for world_id, world in enumerate(WORLDS):
        for output_id, (o0, o1) in enumerate(OUTPUTS):
            a0, a1 = target[0], target[1 + o0]
            probability = (
                observation_probability(case, world, a0, o0, 0)
                * observation_probability(case, world, a1, o1, 1)
            )
            observations[world_id, output_id] = probability
            full_history[world_id, HISTORIES.index((a0, o0, a1, o1))] = probability
    return observations, full_history


def target_policy(target):
    policy = np.full((7, 3), 1 / 3)
    policy[0] = np.eye(3)[target[0]]
    for observation in range(2):
        policy[1 + 2 * target[0] + observation] = np.eye(3)[target[1 + observation]]
    return policy


def assert_close(actual, expected, tolerance=1e-9):
    if not np.allclose(actual, expected, atol=tolerance, rtol=0):
        raise AssertionError(f"Expected {expected!r}; got {actual!r}")


def check_channels(models):
    rng = np.random.default_rng(73109)
    comparisons = 0
    for case in ["compatible", "irreversible", "noisy"]:
        tables = models.true_tables(case)
        for values in tables.values():
            if isinstance(values, np.ndarray):
                assert np.isfinite(values).all()
        for policy in [np.full((7, 3), 1 / 3), rng.dirichlet(np.ones(3), size=7)]:
            expected = manual_collector(case, policy)
            actual = models.collector_kernel(tables, policy)
            assert_close(actual, expected)
            assert_close(actual.sum(axis=1), np.ones(4))
            comparisons += 1
        for target in TARGETS:
            expected, full = manual_target(case, target)
            assert_close(models.target_kernel(tables, target), expected)
            assert_close(models.collector_kernel(tables, target_policy(target)), full)
            assert_close(expected.sum(axis=1), np.ones(4))
            comparisons += 1
    return {"independent_channel_comparisons": comparisons}


def check_target_history_equivalence(models):
    rng = np.random.default_rng(17203)
    tests = 0
    for case in ["compatible", "irreversible", "noisy"]:
        tables = models.true_tables(case)
        policy = rng.dirichlet(np.ones(3), size=7)
        source = models.collector_kernel(tables, policy)
        for target_id in [0, 5, 13, 19, 26]:
            observations, full = manual_target(case, TARGETS[target_id])
            value_observations = reference_deficiency(source, observations)
            value_full = reference_deficiency(source, full)
            assert_close(value_observations, value_full, 2e-8)
            tests += 1
    return {"independent_LP_history_equivalences": tests}


def check_analytic_examples(models):
    tables = models.true_tables("irreversible")
    left = manual_target("irreversible", (0, 0, 0))[0]
    right = manual_target("irreversible", (1, 1, 1))[0]
    rng = np.random.default_rng(86431)
    losses = []
    for probability_left in [0.0, 0.2, 0.5, 0.8, 1.0]:
        policy = rng.dirichlet(np.ones(3), size=7)
        policy[0] = [probability_left, 1 - probability_left, 0]
        source = models.collector_kernel(tables, policy)
        values = [reference_deficiency(source, left), reference_deficiency(source, right)]
        assert_close(values, [(1 - probability_left) / 2, probability_left / 2])
        losses.append({"left_probability": probability_left, "losses": values})
    compatible = models.true_tables("compatible")
    both_bits = models.collector_kernel(compatible, target_policy((0, 1, 1)))
    for target in TARGETS:
        assert_close(reference_deficiency(both_bits, manual_target("compatible", target)[0]), 0)
    for case in ["compatible", "irreversible", "noisy"]:
        source = manual_collector(case, rng.dirichlet(np.ones(3), size=7))
        noise = manual_target(case, (2, 2, 2))[0]
        assert_close(noise, np.repeat(noise[:1], 4, axis=0))
        assert_close(reference_deficiency(source, noise), 0)
    return {"irreversible_analytic_pairs": losses, "compatible_targets_exact": 27,
            "world_independent_noise_cases": 3}


def check_maximum_tie():
    """A real experiment refinement that the full native maximum does not detect."""
    worlds = list(itertools.product(range(2), repeat=3))
    one_bit = np.array([np.eye(2)[u] for u, v, w in worlds])
    two_bits = np.array([np.eye(4)[2 * u + v] for u, v, w in worlds])
    last_bit = np.array([np.eye(2)[w] for u, v, w in worlds])
    experiments = [one_bit, two_bits, last_bit]
    profiles = [[reference_deficiency(source, target) for target in experiments]
                for source in [one_bit, two_bits]]
    assert_close(profiles, [[0, .5, .5], [0, 0, .5]])
    assert_close(reference_deficiency(two_bits, one_bit), 0)
    assert_close(reference_deficiency(one_bit, two_bits), .5)
    # Recorded randomized startup choices are native targets too. The upper
    # bound remains 1/2 for arbitrary mixtures, checked here on several weights.
    for weights in [[.2, .3, .5], [1/3, 1/3, 1/3], [.7, .1, .2]]:
        target = np.concatenate([weight * kernel for weight, kernel in zip(weights, experiments)], axis=1)
        for source in [one_bit, two_bits]:
            assert reference_deficiency(source, target) <= .5 + 1e-9
    return {"profiles": profiles, "interpretation": "strict refinement; same worst native target error"}


def check_sampled_models(models):
    summaries = []
    for case in ["compatible", "irreversible", "noisy"]:
        first, metadata = models.sample_tables(case, 60311, 8192)
        repeat, repeated_metadata = models.sample_tables(case, 60311, 8192)
        assert metadata == repeated_metadata
        for key in ["first", "second"]:
            assert np.array_equal(first[key], repeat[key])
            counts = np.asarray(metadata[f"{key}_counts"])
            assert_close(counts.reshape(4, -1).sum(1), np.full(4, 8192))
            totals = counts.sum(-1)
            visited = totals > 0
            assert_close(first[key][visited], counts[visited] / totals[visited, None])
            assert_close(first[key][~visited], np.full_like(first[key][~visited], .5))
        # These are seeded mechanics checks, not a statistical confidence claim.
        sample_law = models.collector_kernel(first, np.full((7, 3), 1/3))
        expected = manual_collector(case, np.full((7, 3), 1/3))
        error = float((.5 * np.abs(sample_law - expected).sum(1)).max())
        assert error < .08, (case, error)
        _, other_metadata = models.sample_tables(case, 60312, 8192)
        assert metadata["episodes_sha256"] != other_metadata["episodes_sha256"]
        summaries.append({"case": case, "uniform_collector_TV_to_true_law": error,
                          "episodes": metadata["total_episodes"]})
    return {"sampled_tables": summaries, "identical_seed_replay": True}


def check_oracles(models, oracle):
    rng = np.random.default_rng(415907)
    comparisons = 0
    references = []
    for case in ["compatible", "irreversible", "noisy"]:
        tables = models.true_tables(case)
        policy = rng.dirichlet(np.ones(3), size=7)
        source = manual_collector(case, policy)
        for target_id in [0, 4, 7, 13, 21, 26]:
            target = manual_target(case, TARGETS[target_id])[0]
            expected = reference_deficiency(source, target)
            actual = oracle.deficiency(source, target)
            assert actual["lower"] <= expected + 2e-8
            assert expected <= actual["upper"] + 2e-8
            assert actual["upper"] - actual["lower"] < 1e-7
            assert_close(actual["G"].sum(1), np.ones(36))
            achieved = float((.5 * np.abs(source @ actual["G"] - target).sum(1)).max())
            assert_close(achieved, actual["achieved_error"])
            comparisons += 1
        for floor in [0.0, 0.005]:
            result = oracle.minimax_reference(tables, min_action_probability=floor)
            recovered = result["policy"]
            assert_close(recovered.sum(1), np.ones(7))
            assert recovered.min() >= floor - 1e-10
            profile = [reference_deficiency(manual_collector(case, recovered),
                                           manual_target(case, target)[0])
                       for target in TARGETS]
            assert_close(max(profile), result["upper"], 1e-7)
            assert result["upper"] - result["lower"] < 1e-7
            assert max(result["feasibility"].values()) < 1e-8
            if floor == 0 and case in ["compatible", "irreversible"]:
                expected_optimum = 0 if case == "compatible" else .25
                assert result["lower"] <= expected_optimum + 1e-8
                assert expected_optimum <= result["upper"] + 1e-8
            references.append({"case": case, "floor": floor,
                               "lower": result["lower"], "upper": result["upper"]})
    # Exercise the corrected dual bound away from optimal solver multipliers.
    # min 2x+3y subject to x+y=1, x>=.25, y>=.1 has exact value 2.1.
    from scipy import sparse
    c = np.array([2., 3.])
    aub = sparse.csr_matrix([[-1., 0.], [0., -1.]])
    bub = np.array([-.25, -.1])
    aeq = sparse.csr_matrix([[1., 1.]])
    beq = np.array([1.])
    for _ in range(25):
        arbitrary = SimpleNamespace(
            ineqlin=SimpleNamespace(marginals=rng.normal(0, 4, 2)),
            eqlin=SimpleNamespace(marginals=rng.normal(0, 4, 1)))
        lower, padding = oracle._box_dual_lower(c, aub, bub, aeq, beq, arbitrary)
        assert lower <= 2.1 + 1e-12
        assert padding > 0
    return {"independent_decoder_LP_comparisons": comparisons,
            "reference_collectors": references, "arbitrary_dual_checks": 25}


def _without_timings(value):
    if isinstance(value, dict):
        return {key: _without_timings(item) for key, item in value.items()
                if key not in {"seconds", "training_seconds"}}
    if isinstance(value, (list, tuple)):
        return [_without_timings(item) for item in value]
    if isinstance(value, np.ndarray):
        return value.tolist()
    return value


def check_learner(models, oracle, learner):
    tables, _ = models.sample_tables("noisy", 40113, 512)
    original = {key: value.copy() for key, value in tables.items()}
    config = {"rounds": 2, "candidates": 3, "decoder_steps": 5,
              "collector_steps": 7, "decoder_refit_steps": 5,
              "candidate_steps": 6, "generator_steps": 3}
    records = {}
    # Install fail-fast guards: the learner has everything it needs in the
    # empirical tables. A callback is the only permissible later audit route.
    original_true = models.true_tables
    saved_oracles = {name: getattr(oracle, name)
                     for name in ["deficiency", "audit_policy", "minimax_reference"]}
    def forbidden(*args, **kwargs):
        raise AssertionError("Learner accessed a true model or exact evaluator")
    try:
        models.true_tables = forbidden
        for name in saved_oracles:
            setattr(oracle, name, forbidden)
        for method in ["adversarial", "random", "hardest_uniform"]:
            records[method] = learner.run_training(tables, 771, method, config)
            repeated = learner.run_training(tables, 771, method, config)
            assert _without_timings(records[method]) == _without_timings(repeated)
        def disruptive_callback(checkpoint):
            checkpoint["policy"][:] = np.nan
            checkpoint["decoders"][:] = -100
            checkpoint["archive"].append(999)
            return {"replacement_policy": np.zeros((7, 3))}
        callback_run = learner.run_training(tables, 771, "adversarial", config,
                                           callback=disruptive_callback)
        assert _without_timings(callback_run) == _without_timings(records["adversarial"])
    finally:
        models.true_tables = original_true
        for name, value in saved_oracles.items():
            setattr(oracle, name, value)
    for key in original:
        assert np.array_equal(tables[key], original[key]), "Training mutated supplied tables"
    for method, record in records.items():
        previous = None
        for checkpoint in record["checkpoints"]:
            policy, decoders = checkpoint["policy"], checkpoint["decoders"]
            archive = checkpoint["archive"]
            assert len(archive) == checkpoint["round"] + 1
            assert len(set(archive)) == len(archive)
            assert_close(policy.sum(1), np.ones(7))
            assert policy.min() >= record["config"]["probability_floor"] - 1e-12
            assert_close(decoders.sum(-1), np.ones((len(archive), 36)))
            source = models.collector_kernel(tables, policy)
            target = np.stack([models.target_kernel(tables, target_id) for target_id in archive])
            errors = (.5 * np.abs(np.einsum("wh,thy->twy", source, decoders) - target).sum(-1)).max(-1)
            assert_close(errors, checkpoint["empirical_target_errors"], 1e-11)
            assert_close(errors.max(), checkpoint["empirical_loss"], 1e-11)
            torch_source, torch_targets = learner.empirical_kernels(tables, policy)
            assert_close(torch_source, source)
            assert_close(torch_targets[archive], target)
            if previous is not None:
                candidates = checkpoint["candidate_ids"]
                assert len(candidates) == config["candidates"]
                assert not set(candidates).intersection(previous["archive"])
                assert checkpoint["added_target"] in candidates
                assert archive[:-1] == previous["archive"]
                assert archive[-1] == checkpoint["added_target"]
                if "candidate_decoders" in checkpoint:
                    earlier_source = models.collector_kernel(tables, previous["policy"])
                    candidate_targets = np.stack([models.target_kernel(tables, item) for item in candidates])
                    actual = (.5 * np.abs(np.einsum("wh,thy->twy", earlier_source,
                             checkpoint["candidate_decoders"]) - candidate_targets).sum(-1)).max(-1)
                    assert_close(actual, checkpoint["candidate_errors"], 1e-11)
                else:
                    raise AssertionError("Selection-time candidate decoders were not retained")
                if method in {"adversarial", "hardest_uniform"}:
                    assert checkpoint["added_target"] == candidates[int(np.argmax(checkpoint["candidate_errors"]))]
            previous = checkpoint
    first, second = records["adversarial"], records["random"]
    assert np.array_equal(first["checkpoints"][0]["policy"], second["checkpoints"][0]["policy"])
    assert first["checkpoints"][1]["candidate_ids"] == second["checkpoints"][1]["candidate_ids"]
    for counter, value in first["counters"].items():
        if counter != "generator_gradient_steps":
            assert value == second["counters"][counter], counter
            assert value == records["hardest_uniform"]["counters"][counter], counter
    assert records["hardest_uniform"]["counters"]["generator_gradient_steps"] == 0
    assert_close(records["hardest_uniform"]["checkpoints"][-1]["generator_probabilities"], np.full((3, 3), 1/3))
    assert first["checkpoints"][1]["candidate_ids"] == records["hardest_uniform"]["checkpoints"][1]["candidate_ids"]
    # Random additions have their own RNG stream and never inspect the error
    # values: reconstruct that stream independently from the documented seed.
    random_seed = np.random.SeedSequence(771).spawn(3)[2]
    random_rng = np.random.default_rng(random_seed)
    for checkpoint in second["checkpoints"][1:]:
        candidates = checkpoint["candidate_ids"]
        assert checkpoint["added_target"] == candidates[int(random_rng.integers(len(candidates)))]
    return {"deterministic_replays": 3, "callback_mutation_isolation": True,
            "no_true_model_or_oracle_calls": True,
            "candidate_errors_replayed": True,
            "matched_counters_except_generator": first["counters"],
            "random_additions_independent_of_scores": True,
            "hardest_uniform_uses_argmax_without_generator_updates": True}


def check_saved_results(directory, models, allow_legacy_candidates=False):
    """Replay saved data, policies, decoder scores and both true/empirical audits.

    This uses the older independent dense decoder LP rather than trusting the
    pilot's saved scalar outputs. It checks complete retained cohorts only.
    """
    directory = Path(directory).resolve()
    manifest = json.loads((directory / "manifest.json").read_text())
    assert manifest["status"] == "complete", "Cannot certify an unfinished cohort"
    configuration = manifest["config"]
    summaries = json.loads((directory / "summary.json").read_text())
    expected = set(itertools.product(configuration["cases"], configuration["seeds"], configuration["methods"]))
    actual = {(row["case"], row["seed"], row["method"]) for row in summaries}
    assert actual == expected and len(actual) == len(summaries), "Cohort omitted or duplicated a run"
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    for name, expected_hash in manifest["source_sha256"].items():
        assert digest(directory / "source" / name) == expected_hash, name
    # Replay the frozen sampling code, even if a future task changes the live file.
    spec = importlib.util.spec_from_file_location("pilot_frozen_model_replay", directory / "source" / "models.py")
    frozen_models = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(frozen_models)
    table_cache, profile_cache, pairing = {}, {}, {}
    samples_replayed = 0
    independent_profiles = 0
    independent_lp_values = 0
    checkpoints_checked = 0
    candidates_checked = 0
    legacy_candidate_checkpoints = 0
    runs = []
    worst_bound_discrepancy = 0.0
    def profile(source, targets):
        nonlocal independent_profiles, independent_lp_values
        key = hashlib.sha256(source.tobytes() + targets.tobytes()).hexdigest()
        if key not in profile_cache:
            profile_cache[key] = np.array([reference_deficiency(source, target) for target in targets])
            independent_profiles += 1
            independent_lp_values += len(targets)
        return profile_cache[key]
    for run_number, summary in enumerate(summaries, start=1):
        case, seed, method = summary["case"], summary["seed"], summary["method"]
        run_directory = directory / summary["path"]
        seed_directory = run_directory.parent
        training = json.loads((run_directory / "training.json").read_text())
        audits = json.loads((run_directory / "audits.json").read_text())
        assert training["method"] == method and training["seed"] == seed
        for name, value in configuration["learner"].items():
            assert training["config"][name] == value, (method, name)
        assert len(audits) == len(training["checkpoints"]) == configuration["learner"]["rounds"] + 1
        key = (case, seed)
        if key not in table_cache:
            data_metadata = json.loads((seed_directory / "data.json").read_text())
            with np.load(seed_directory / "empirical_tables.npz") as archive:
                tables = {name: archive[name] for name in ["first", "second"]}
            regenerated, regenerated_metadata = frozen_models.sample_tables(case, data_metadata["seed"], data_metadata["episodes_per_world"])
            assert regenerated_metadata == data_metadata
            for name in regenerated:
                assert np.array_equal(regenerated[name], tables[name])
            table_cache[key] = tables
            samples_replayed += 1
        tables = table_cache[key]
        true_targets = np.stack([manual_target(case, target)[0] for target in TARGETS])
        empirical_targets = np.stack([models.target_kernel(tables, target) for target in TARGETS])
        floor = training["config"]["probability_floor"]
        assert_close(configuration["reference_min_action_probability"], floor)
        previous = None
        for checkpoint, saved_audit in zip(training["checkpoints"], audits):
            round_number = checkpoint["round"]
            assert saved_audit["round"] == round_number
            policy = np.asarray(checkpoint["policy"], dtype=float)
            decoder = np.asarray(checkpoint["decoders"], dtype=float)
            archive = checkpoint["archive"]
            assert policy.shape == (7, 3) and decoder.shape == (len(archive), 36, 4)
            assert np.isfinite(policy).all() and np.isfinite(decoder).all()
            assert_close(policy.sum(1), np.ones(7))
            assert_close(decoder.sum(-1), np.ones((len(archive), 36)))
            assert policy.min() >= floor - 1e-12 and decoder.min() >= 0
            assert len(set(archive)) == len(archive)
            assert len(archive) == (27 if method == "all_targets" else round_number + 1)
            sources = {"true": manual_collector(case, policy),
                       "empirical": models.collector_kernel(tables, policy)}
            for name, targets in [("true", true_targets), ("empirical", empirical_targets)]:
                source = sources[name]
                independently_computed = profile(source, targets)
                bounds = saved_audit[name]["exact"]
                lower, upper = np.asarray(bounds["lower"]), np.asarray(bounds["upper"])
                assert lower.shape == upper.shape == (27,)
                discrepancy = max(float(np.max(lower - independently_computed)),
                                  float(np.max(independently_computed - upper)), 0.0)
                worst_bound_discrepancy = max(worst_bound_discrepancy, discrepancy)
                assert discrepancy < 2e-8, (case, seed, method, round_number, name, discrepancy)
                assert_close(bounds["worst_lower"], lower.max())
                assert_close(bounds["worst_upper"], upper.max())
                achieved = (.5 * np.abs(np.einsum("wh,thy->twy", source, decoder) - targets[archive]).sum(-1)).max(-1)
                assert_close(achieved, saved_audit[name]["achieved_archived_decoder_errors"], 1e-11)
                assert np.min(achieved - independently_computed[archive]) >= -2e-8
                if name == "empirical":
                    assert_close(achieved, checkpoint["empirical_target_errors"], 1e-11)
                    assert_close(achieved.max(), checkpoint["empirical_loss"], 1e-11)
            if previous is not None and method != "all_targets":
                ids = checkpoint["candidate_ids"]
                assert len(set(ids)) == len(ids)
                assert not set(ids).intersection(previous["archive"])
                assert archive[:-1] == previous["archive"]
                assert checkpoint["added_target"] == archive[-1]
                assert archive[-1] in ids
                if "candidate_decoders" in checkpoint:
                    candidate_decoders = np.asarray(checkpoint["candidate_decoders"])
                    old_source = models.collector_kernel(tables, np.asarray(previous["policy"]))
                    candidate_errors = (.5 * np.abs(np.einsum("wh,thy->twy", old_source,
                                        candidate_decoders) - empirical_targets[ids]).sum(-1)).max(-1)
                    assert_close(candidate_errors, checkpoint["candidate_errors"], 1e-11)
                    candidates_checked += len(ids)
                else:
                    assert allow_legacy_candidates, "Saved candidate decoder witnesses are missing"
                    legacy_candidate_checkpoints += 1
                if method in {"adversarial", "hardest_uniform"}:
                    assert archive[-1] == ids[int(np.argmax(checkpoint["candidate_errors"]))]
            previous = checkpoint
            checkpoints_checked += 1
        if method == "random":
            choice_rng = np.random.default_rng(np.random.SeedSequence(int(seed)).spawn(3)[2])
            for checkpoint in training["checkpoints"][1:]:
                ids = checkpoint["candidate_ids"]
                assert checkpoint["added_target"] == ids[int(choice_rng.integers(len(ids)))]
        if method in {"random", "hardest_uniform"}:
            assert training["counters"]["generator_gradient_steps"] == 0
        if method != "all_targets":
            paired = pairing.setdefault(key, [])
            if paired:
                reference = paired[0]
                assert checkpoint["round"] == reference["checkpoints"][-1]["round"]
                assert np.array_equal(training["checkpoints"][0]["policy"], reference["checkpoints"][0]["policy"])
                for name, count in training["counters"].items():
                    if name != "generator_gradient_steps":
                        assert count == reference["counters"][name], name
            paired.append(training)
        runs.append({"case": case, "seed": seed, "method": method,
                     "training_sha256": digest(run_directory / "training.json"),
                     "audits_sha256": digest(run_directory / "audits.json")})
        if run_number % 12 == 0 or run_number == len(summaries):
            print(f"Independent saved-run audit: {run_number}/{len(summaries)}", file=sys.stderr, flush=True)
    # Saved reference policies are independently replayed; this does not promote
    # a numerical dual certificate to an exact rational theorem.
    references_checked = 0
    for case in configuration["cases"]:
        reference_pair = json.loads((directory / case / "reference.json").read_text())
        targets = np.stack([manual_target(case, target)[0] for target in TARGETS])
        for name in ["unrestricted", "policy_floor"]:
            result = reference_pair[name]
            source = manual_collector(case, np.asarray(result["policy"]))
            independently_computed = profile(source, targets)
            assert_close(independently_computed.max(), result["upper"], 1e-7)
            assert result["lower"] <= independently_computed.max() + 1e-8
            assert result["upper"] - result["lower"] < 1e-7
            if name == "unrestricted" and case in {"compatible", "irreversible"}:
                expected_optimum = 0 if case == "compatible" else .25
                assert result["lower"] <= expected_optimum + 1e-8
                assert expected_optimum <= result["upper"] + 1e-8
            references_checked += 1
    return {"directory": str(directory), "phase": configuration["phase"],
            "frozen_source_hashes_verified": True, "sampled_data_strata_replayed": samples_replayed,
            "runs": runs, "checkpoints": checkpoints_checked, "candidate_scores_replayed": candidates_checked,
            "legacy_candidate_witness_checks_skipped": legacy_candidate_checkpoints,
            "independent_source_profiles": independent_profiles, "independent_decoder_LP_values": independent_lp_values,
            "saved_reference_policies_replayed": references_checked,
            "largest_bound_discrepancy": worst_bound_discrepancy,
            "test_source_sha256": digest(Path(__file__)),
            "independent_LP_source_sha256": digest(ROOT / "Experiments" / "src" / "idexp" / "lp.py")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write a machine-readable verification record")
    parser.add_argument("--skip-learning", action="store_true", help="Run channel and numerical-oracle checks only")
    parser.add_argument("--results", type=Path, help="Independently replay a complete saved run directory")
    parser.add_argument("--allow-legacy-candidates", action="store_true", help="Explicitly skip missing candidate witnesses in old development output")
    args = parser.parse_args()
    models = importlib.import_module("models")
    oracle = importlib.import_module("oracle")
    checks = [
        ("channels", lambda: check_channels(models)),
        ("target_history_equivalence", lambda: check_target_history_equivalence(models)),
        ("analytic_examples", lambda: check_analytic_examples(models)),
        ("maximum_tie", check_maximum_tie),
        ("sampled_models", lambda: check_sampled_models(models)),
        ("oracles", lambda: check_oracles(models, oracle)),
    ]
    if not args.skip_learning:
        learner = importlib.import_module("learner")
        checks.append(("learner", lambda: check_learner(models, oracle, learner)))
    if args.results:
        checks.append(("saved_results", lambda: check_saved_results(args.results, models, args.allow_legacy_candidates)))
    record = {"status": "passed", "scope": "independent finite-model semantics; floating-point numerical LP checks", "checks": {}}
    start = time.monotonic()
    for name, check in checks:
        try:
            record["checks"][name] = {"status": "passed", **check()}
        except Exception as error:
            record["status"] = "failed"
            record["checks"][name] = {"status": "failed", "error": repr(error)}
    record["seconds"] = time.monotonic() - start
    output = json.dumps(record, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output, end="")
    raise SystemExit(0 if record["status"] == "passed" else 1)


if __name__ == "__main__":
    main()
