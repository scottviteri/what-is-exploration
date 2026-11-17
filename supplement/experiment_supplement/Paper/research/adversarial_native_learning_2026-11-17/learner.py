"""Sampled-model training for the finite adversarial native-learning pilot.

The only environmental input is a pair of empirical conditional-probability
tables. No true-response or LP/oracle function is imported. The collector and
decoder are world-independent; world indices occur only in the training loss.
Target generation uses a deliberately small factorized categorical model over
the 27 deterministic depth-two observation-contingent policies.

The target-generator update is centered reward-weighted log likelihood on the
sampled candidate batch, with entropy regularization. Reusing that batch and
sampling without replacement means this is a search heuristic, not a claim of
an unbiased policy-gradient estimator. All returned losses are achieved decoder
errors, not certified deficiencies.
"""

from __future__ import annotations

import copy
import itertools
import time
from typing import Any, Callable

import numpy as np
import torch


TARGETS = tuple(itertools.product(range(3), repeat=3))
HISTORIES = tuple(itertools.product(range(3), range(2), range(3), range(2)))
DEFAULT_CONFIG = {
    "rounds": 5,
    "candidates": 4,
    "decoder_steps": 200,
    "collector_steps": 250,
    "decoder_refit_steps": 200,
    "candidate_steps": 250,
    "decoder_lr": 0.08,
    "collector_lr": 0.04,
    "generator_lr": 0.08,
    "generator_steps": 15,
    "generator_entropy": 0.01,
    "exploration": 0.2,
    "probability_floor": 0.005,
    "init_scale": 0.03,
    "lr_final_fraction": 0.15,
}


def resolve_config(config: dict[str, Any] | None) -> dict[str, Any]:
    answer = dict(DEFAULT_CONFIG)
    if config:
        unknown = set(config) - set(answer)
        if unknown:
            raise ValueError(f"Unknown learner config keys: {sorted(unknown)}")
        answer.update(config)
    for name in ("rounds", "candidates", "decoder_steps", "collector_steps",
                 "decoder_refit_steps", "candidate_steps", "generator_steps"):
        if not isinstance(answer[name], (int, np.integer)) or answer[name] < 0:
            raise ValueError(f"{name} must be a nonnegative integer")
        answer[name] = int(answer[name])
    if not 0 <= answer["rounds"] <= 26:
        raise ValueError("rounds must be at most the 26 initially omitted targets")
    if answer["rounds"] and answer["candidates"] < 1:
        raise ValueError("Positive rounds require at least one candidate")
    if not 0 <= answer["exploration"] <= 1:
        raise ValueError("exploration must be in [0,1]")
    if not 0 <= answer["probability_floor"] < 1 / 3:
        raise ValueError("probability_floor is a per-action floor below 1/3")
    if not 0 < answer["lr_final_fraction"] <= 1:
        raise ValueError("lr_final_fraction must be in (0,1]")
    for name in ("decoder_lr", "collector_lr", "generator_lr"):
        if not np.isfinite(answer[name]) or answer[name] <= 0:
            raise ValueError(f"{name} must be positive and finite")
    if answer["init_scale"] < 0 or answer["generator_entropy"] < 0:
        raise ValueError("Initialization scale and entropy coefficient must be nonnegative")
    return answer


class EmpiricalChannels:
    """Differentiable experiment matrices made only from the supplied tables."""

    def __init__(self, tables: dict[str, np.ndarray]):
        first = np.asarray(tables["first"], dtype=np.float64)
        second = np.asarray(tables["second"], dtype=np.float64)
        if first.ndim != 3 or first.shape[1:] != (3, 2):
            raise ValueError("first must have shape (worlds,3,2)")
        if second.shape != (first.shape[0], 3, 2, 3, 2):
            raise ValueError("second must have shape (worlds,3,2,3,2)")
        for name, array in (("first", first), ("second", second)):
            if (not np.isfinite(array).all() or np.min(array) < 0 or
                    not np.allclose(array.sum(-1), 1.0, atol=1e-12, rtol=0)):
                raise ValueError(f"{name} contains invalid probability rows")
        h = np.asarray(HISTORIES, dtype=np.int64)
        self.a0 = torch.tensor(h[:, 0])
        self.o0 = torch.tensor(h[:, 1])
        self.a1 = torch.tensor(h[:, 2])
        self.o1 = torch.tensor(h[:, 3])
        # torch.tensor copies, so optimizers cannot mutate caller-owned tables.
        f = torch.tensor(first, dtype=torch.float64)
        s = torch.tensor(second, dtype=torch.float64)
        self.raw = f[:, self.a0, self.o0] * s[:, self.a0, self.o0, self.a1, self.o1]
        target_columns = []
        for root, after_zero, after_one in TARGETS:
            columns = []
            for obs0, obs1 in itertools.product(range(2), repeat=2):
                action1 = after_zero if obs0 == 0 else after_one
                columns.append(f[:, root, obs0] * s[:, root, obs0, action1, obs1])
            target_columns.append(torch.stack(columns, dim=1))
        self.targets = torch.stack(target_columns, dim=0)  # target, world, output

    def collector(self, policy: torch.Tensor) -> torch.Tensor:
        weights = policy[0, self.a0] * policy[1 + 2 * self.a0 + self.o0, self.a1]
        return self.raw * weights[None, :]


def empirical_kernels(tables: dict[str, np.ndarray], policy: np.ndarray):
    """Return source (world,36), targets (27,world,4) for independent checks."""
    channels = EmpiricalChannels(tables)
    p = torch.tensor(np.asarray(policy), dtype=torch.float64)
    return channels.collector(p).numpy(), channels.targets.numpy()


def _policy(logits: torch.Tensor, floor: float) -> torch.Tensor:
    return floor + (1.0 - 3.0 * floor) * logits.softmax(dim=-1)


def _errors(source: torch.Tensor, decoder: torch.Tensor,
            targets: torch.Tensor) -> torch.Tensor:
    simulated = torch.einsum("wh,thy->twy", source, decoder)
    return (0.5 * (simulated - targets).abs().sum(dim=-1)).amax(dim=-1)


def _set_lr(optimizer: torch.optim.Optimizer, base: float, step: int,
            total: int, final_fraction: float):
    # A fixed linear schedule, unrelated to true errors or audit outputs.
    fraction = step / max(1, total - 1)
    lr = base * (1.0 - (1.0 - final_fraction) * fraction)
    for group in optimizer.param_groups:
        group["lr"] = lr


def _fit_decoders(source: torch.Tensor, targets: torch.Tensor,
                  initial_logits: torch.Tensor, steps: int,
                  config: dict[str, Any]):
    """Independent minimizations batched together; retain each best achieved row bank."""
    logits = torch.nn.Parameter(initial_logits.clone())
    optimizer = torch.optim.Adam([logits], lr=config["decoder_lr"])
    source = source.detach()
    with torch.no_grad():
        best_errors = _errors(source, logits.softmax(-1), targets)
        best = logits.detach().clone()
    for step in range(steps):
        _set_lr(optimizer, config["decoder_lr"], step, steps, config["lr_final_fraction"])
        optimizer.zero_grad(set_to_none=True)
        # Separable target fits: every decoder is trained, even when another
        # target currently determines the collector's maximum loss.
        loss = _errors(source, logits.softmax(-1), targets).mean()
        loss.backward()
        optimizer.step()
        with torch.no_grad():
            current = _errors(source, logits.softmax(-1), targets)
            improved = current < best_errors
            best[improved] = logits.detach()[improved]
            best_errors = torch.minimum(best_errors, current)
    return best, best_errors


def _train_archive(channels: EmpiricalChannels, policy_logits: torch.Tensor,
                   decoder_bank: torch.Tensor, archive: list[int],
                   config: dict[str, Any], counters: dict[str, int]):
    target = channels.targets[archive]
    with torch.no_grad():
        source = channels.collector(_policy(policy_logits, config["probability_floor"]))
    fitted, _ = _fit_decoders(source, target, decoder_bank[archive],
                              config["decoder_steps"], config)
    p = torch.nn.Parameter(policy_logits.clone())
    d = torch.nn.Parameter(fitted.clone())
    opt_p = torch.optim.Adam([p], lr=config["collector_lr"])
    opt_d = torch.optim.Adam([d], lr=config["decoder_lr"])
    with torch.no_grad():
        best_value = _errors(source, d.softmax(-1), target).max().item()
        best_p, best_d = p.detach().clone(), d.detach().clone()
    for step in range(config["collector_steps"]):
        _set_lr(opt_p, config["collector_lr"], step, config["collector_steps"],
                config["lr_final_fraction"])
        _set_lr(opt_d, config["decoder_lr"], step, config["collector_steps"],
                config["lr_final_fraction"])
        # Decoder update cannot differentiate through the frozen collector.
        opt_d.zero_grad(set_to_none=True)
        source = channels.collector(_policy(p, config["probability_floor"])).detach()
        decoder_loss = _errors(source, d.softmax(-1), target).mean()
        decoder_loss.backward()
        opt_d.step()
        # Collector update sees a frozen decoder, including its stochasticity.
        opt_p.zero_grad(set_to_none=True)
        source = channels.collector(_policy(p, config["probability_floor"]))
        collector_loss = _errors(source, d.softmax(-1).detach(), target).max()
        collector_loss.backward()
        opt_p.step()
        with torch.no_grad():
            source = channels.collector(_policy(p, config["probability_floor"]))
            current = _errors(source, d.softmax(-1), target).max().item()
            if current < best_value:
                best_value = current
                best_p, best_d = p.detach().clone(), d.detach().clone()
    # Selection uses only the empirical achieved loss. Each candidate was
    # feasible; no audit/oracle value enters this best-iterate choice.
    with torch.no_grad():
        source = channels.collector(_policy(best_p, config["probability_floor"]))
    fitted, errors = _fit_decoders(source, target, best_d,
                                  config["decoder_refit_steps"], config)
    decoder_bank = decoder_bank.clone()
    decoder_bank[archive] = fitted
    number = len(archive)
    counters["collector_gradient_steps"] += config["collector_steps"]
    decoder_steps = (config["decoder_steps"] + config["collector_steps"] +
                     config["decoder_refit_steps"])
    counters["decoder_optimizer_steps"] += decoder_steps
    counters["decoder_target_steps"] += number * decoder_steps
    counters["archive_training_calls"] += 1
    return best_p, decoder_bank, errors


def _target_probabilities(generator_logits: torch.Tensor,
                          available: list[int], exploration: float) -> np.ndarray:
    with torch.no_grad():
        p = generator_logits.softmax(-1).numpy()
    products = np.array([p[0, TARGETS[i][0]] * p[1, TARGETS[i][1]] *
                         p[2, TARGETS[i][2]] for i in available])
    # Normalize on omitted targets, then mix in uniform exploration there.
    products /= products.sum()
    products = (1.0 - exploration) * products + exploration / len(available)
    return products / products.sum()


def _update_generator(initial_logits: torch.Tensor, ids: list[int],
                      errors: np.ndarray, config: dict[str, Any]):
    logits = torch.nn.Parameter(initial_logits.clone())
    optimizer = torch.optim.Adam([logits], lr=config["generator_lr"])
    actions = torch.tensor([TARGETS[i] for i in ids], dtype=torch.long)
    scores = torch.tensor(errors, dtype=torch.float64)
    centered = scores - scores.mean()
    # Batch normalization avoids making generator learning-rate depend on
    # the absolute scale of the finite losses. A constant batch supplies no
    # directional reward signal.
    advantages = centered / centered.abs().max().clamp(min=1e-8)
    for _ in range(config["generator_steps"]):
        optimizer.zero_grad(set_to_none=True)
        logp = logits.log_softmax(-1)
        log_probability = logp[torch.arange(3)[None, :], actions].sum(-1)
        entropy = -(logp.exp() * logp).sum(-1).mean()
        loss = -(advantages * log_probability).mean() - config["generator_entropy"] * entropy
        loss.backward()
        optimizer.step()
    return logits.detach().clone()


def run_training(tables: dict[str, np.ndarray], seed: int, method: str,
                 config: dict[str, Any] | None = None,
                 callback: Callable[[dict[str, Any]], Any] | None = None):
    """Train and return every archive checkpoint; callbacks cannot affect training.

    ``adversarial``, ``hardest_uniform`` and ``random`` have the same candidate-fit
    and collector update budgets. Only the adversary updates its generator;
    ``hardest_uniform`` retains the hardest uniformly sampled candidate. The
    optional ``all_targets`` diagnostic trains on all targets from the start;
    it is intentionally not compute matched.
    """
    if method not in {"adversarial", "hardest_uniform", "random", "all_targets"}:
        raise ValueError("method must be adversarial, hardest_uniform, random, or all_targets")
    config = resolve_config(config)
    torch.set_num_threads(1)
    begin = time.perf_counter()
    channels = EmpiricalChannels(tables)
    # Disjoint deterministic streams: candidate choices cannot change the
    # initial collector or decoder parameters shared by paired methods.
    seeds = np.random.SeedSequence(int(seed)).spawn(3)
    initialize = np.random.default_rng(seeds[0])
    candidates_rng = np.random.default_rng(seeds[1])
    random_add_rng = np.random.default_rng(seeds[2])
    p_logits = torch.tensor(initialize.normal(0, config["init_scale"], (7, 3)),
                            dtype=torch.float64)
    bank = torch.tensor(initialize.normal(0, config["init_scale"], (27, 36, 4)),
                        dtype=torch.float64)
    generator_logits = torch.zeros((3, 3), dtype=torch.float64)
    archive = list(range(27)) if method == "all_targets" else [0]
    counters = {"collector_gradient_steps": 0, "decoder_optimizer_steps": 0,
                "decoder_target_steps": 0, "candidate_queries": 0,
                "candidate_fit_calls": 0, "candidate_target_steps": 0,
                "generator_gradient_steps": 0, "archive_training_calls": 0}
    checkpoints = []
    for round_number in range(config["rounds"] + 1):
        candidate_ids: list[int] = []
        candidate_errors = np.zeros(0)
        candidate_decoders = np.zeros((0, 36, 4))
        added = None
        if round_number and method != "all_targets":
            available = [i for i in range(27) if i not in archive]
            number = min(config["candidates"], len(available))
            probabilities = (_target_probabilities(generator_logits, available,
                                                    config["exploration"])
                             if method == "adversarial" else
                             np.full(len(available), 1.0 / len(available)))
            candidate_ids = [int(i) for i in candidates_rng.choice(
                available, size=number, replace=False, p=probabilities)]
            with torch.no_grad():
                source = channels.collector(_policy(p_logits, config["probability_floor"]))
            fitted, errors = _fit_decoders(source, channels.targets[candidate_ids],
                                          bank[candidate_ids], config["candidate_steps"], config)
            bank[candidate_ids] = fitted
            candidate_errors = errors.numpy().copy()
            # Preserve the proposal-time witnesses before accepted decoders
            # are refitted against the updated collector and archive.
            candidate_decoders = fitted.softmax(-1).numpy().copy()
            counters["candidate_queries"] += number
            counters["candidate_fit_calls"] += 1
            counters["candidate_target_steps"] += number * config["candidate_steps"]
            counters["decoder_optimizer_steps"] += config["candidate_steps"]
            counters["decoder_target_steps"] += number * config["candidate_steps"]
            if method == "adversarial":
                generator_logits = _update_generator(generator_logits, candidate_ids,
                                                     candidate_errors, config)
                counters["generator_gradient_steps"] += config["generator_steps"]
            if method in {"adversarial", "hardest_uniform"}:
                added = candidate_ids[int(np.argmax(candidate_errors))]
            else:
                # This choice deliberately does not inspect fitted error.
                added = candidate_ids[int(random_add_rng.integers(number))]
            archive.append(added)
        p_logits, bank, errors = _train_archive(channels, p_logits, bank, archive,
                                                config, counters)
        with torch.no_grad():
            policy = _policy(p_logits, config["probability_floor"]).numpy().copy()
            decoder = bank[archive].softmax(-1).numpy().copy()
            generator_probability = generator_logits.softmax(-1).numpy().copy()
        checkpoint = {
            "round": round_number,
            "archive": list(archive),
            "policy": policy,
            "policy_logits": p_logits.numpy().copy(),
            "decoders": decoder,
            "decoder_bank_logits": bank.numpy().copy(),
            "generator_logits": generator_logits.numpy().copy(),
            "generator_probabilities": generator_probability,
            "empirical_target_errors": errors.numpy().copy(),
            "empirical_loss": float(errors.max()),
            "candidate_ids": list(candidate_ids),
            "candidate_errors": candidate_errors,
            "candidate_decoders": candidate_decoders,
            "added_target": added,
            "counters": dict(counters),
            "training_seconds": time.perf_counter() - begin,
        }
        checkpoints.append(checkpoint)
        if callback is not None:
            # Diagnostics receive no live tensor/array alias, and their return
            # value is ignored. They may evaluate true tables without leakage.
            callback(copy.deepcopy(checkpoint))
    return {"method": method, "seed": int(seed), "config": config,
            "checkpoints": checkpoints, "counters": dict(counters),
            "seconds": time.perf_counter() - begin,
            "training_access": "empirical response tables only; world indices in loss, not policy/decoder inputs",
            "generator_update": ("centered reward-weighted log likelihood with entropy regularization"
                                 if method == "adversarial" else "disabled"),
            "policy_floor": "per-action mixture floor; finite pilot parameterization restriction"}
