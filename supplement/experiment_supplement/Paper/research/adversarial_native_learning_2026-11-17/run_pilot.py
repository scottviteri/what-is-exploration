"""Run a frozen finite learned pilot; exact evaluation occurs after each learner returns."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import time

import numpy as np
import scipy
import torch

import learner
import models
import oracle

HERE = Path(__file__).resolve().parent


def plain(x):
    if isinstance(x, np.ndarray):
        return x.tolist()
    if isinstance(x, np.generic):
        return x.item()
    if isinstance(x, Path):
        return str(x)
    if isinstance(x, dict):
        return {str(k): plain(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)):
        return [plain(v) for v in x]
    return x


def save_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(plain(value), indent=2, allow_nan=False) + '\n')
    temporary.replace(path)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def checkpoint_audit(tables, checkpoint):
    """Neither this function nor its outputs are visible to run_training."""
    policy = np.asarray(checkpoint['policy'], dtype=float)
    result = oracle.audit_policy(tables, policy)
    E = models.collector_kernel(tables, policy)
    achieved = []
    for target_id, decoder in zip(checkpoint['archive'], checkpoint['decoders']):
        F = models.target_kernel(tables, models.TARGETS[int(target_id)])
        achieved.append(float((0.5 * np.abs(E @ np.asarray(decoder) - F).sum(axis=1)).max()))
    return {'exact': result, 'achieved_archived_decoder_errors': achieved}


def run(config_path, output):
    config = json.loads(Path(config_path).read_text())
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'manifest.json').exists():
        raise ValueError('Output already has a manifest; use a new directory to preserve previous runs.')
    torch.set_num_threads(1)
    try:
        torch.set_num_interop_threads(1)
    except RuntimeError:
        pass
    # Initialize Torch/Adam before per-method timing without consuming RNG draws.
    warm = torch.nn.Parameter(torch.zeros(1, dtype=torch.float64))
    warm_optimizer = torch.optim.Adam([warm])
    warm.square().sum().backward()
    warm_optimizer.step()
    frozen_names = ['models.py', 'learner.py', 'oracle.py', 'run_pilot.py', 'EXPLAINER.tex']
    source_hashes = {n: sha(HERE / n) for n in frozen_names}
    (output / 'source').mkdir()
    for n in frozen_names:
        shutil.copyfile(HERE / n, output / 'source' / n)
    manifest = {
        'phase': config['phase'], 'config': config, 'config_sha256': sha(config_path),
        'source_sha256': source_hashes,
        'versions': {'python': platform.python_version(), 'numpy': np.__version__,
                     'scipy': scipy.__version__, 'torch': torch.__version__},
        'audit_access': 'Exact true-model audits are performed only after run_training returns; no audit feedback.',
        'status': 'running', 'started_unix': time.time(),
    }
    save_json(output / 'manifest.json', manifest)
    summaries = []
    for case_index, case in enumerate(config['cases']):
        true_tables = models.true_tables(case)
        # Reference computation remains independent of each learner and its input.
        reference = oracle.minimax_reference(true_tables)
        min_probability = config.get('reference_min_action_probability', 0.0)
        floored = oracle.minimax_reference(true_tables, min_action_probability=min_probability)
        case_dir = output / case
        case_dir.mkdir()
        save_json(case_dir / 'reference.json', {'unrestricted': reference, 'policy_floor': floored})
        for seed in config['seeds']:
            data_seed = int(seed) * 100 + case_index + 173
            tables, data_metadata = models.sample_tables(case, data_seed, config['episodes_per_world'])
            seed_dir = case_dir / f'seed_{seed}'
            seed_dir.mkdir()
            np.savez_compressed(seed_dir / 'empirical_tables.npz', **tables)
            save_json(seed_dir / 'data.json', data_metadata)
            for method in config['methods']:
                if any(sha(HERE / n) != h for n, h in source_hashes.items()):
                    raise RuntimeError('Source changed after protocol freeze; retain this run and start a separately labelled run.')
                start = time.perf_counter()
                # Only sampled empirical tables cross this boundary.
                trained = learner.run_training(tables, int(seed), method, config['learner'])
                training_seconds = time.perf_counter() - start
                result_dir = seed_dir / method
                result_dir.mkdir()
                save_json(result_dir / 'training.json', trained)
                audits = []
                for checkpoint in trained['checkpoints']:
                    a = checkpoint_audit(true_tables, checkpoint)
                    empirical_a = checkpoint_audit(tables, checkpoint)
                    audits.append({'round': checkpoint['round'], 'true': a, 'empirical': empirical_a})
                save_json(result_dir / 'audits.json', audits)
                summary = {'case': case, 'seed': seed, 'method': method,
                           'training_seconds': training_seconds,
                           'audit_seconds': time.perf_counter() - start - training_seconds,
                           'path': str(result_dir.relative_to(output)),
                           'counters': trained.get('counters', {})}
                summaries.append(summary)
                save_json(output / 'progress.json', {'completed': summaries})
                print(f'{case} seed={seed} {method}: training {training_seconds:.2f}s; audit complete', flush=True)
    manifest.update(status='complete', finished_unix=time.time(), runs=len(summaries))
    save_json(output / 'manifest.json', manifest)
    save_json(output / 'summary.json', summaries)
    return summaries


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.config, args.output)
