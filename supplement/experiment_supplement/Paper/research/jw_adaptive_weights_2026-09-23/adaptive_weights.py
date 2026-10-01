"""Exact, solver-free bookkeeping for finite approximations to adaptive native loss.

This module proves no solver output correct. Numeric evidence carries its origin;
new mathematical guarantees are stated separately in THEORY.md. No third-party
imports, solver invocation, random experiment, or implicit normalization occurs.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction as F
import hashlib
import json
from math import comb
from typing import Iterable

SCHEMA = 'adaptive-native-v1'
RECORD = 'full-action-observation-history-v1'


def canonical(value):
    if isinstance(value, F):
        return str(value)
    if hasattr(value, '__dataclass_fields__'):
        return canonical(asdict(value))
    if isinstance(value, dict):
        return {str(k): canonical(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [canonical(v) for v in value]
    return value


def digest(value):
    return hashlib.sha256(json.dumps(canonical(value), sort_keys=True,
        separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def rational(x):
    # Floats must be converted explicitly by the numerical bridge. This prevents
    # accidental loss of normalization in the intended mathematical objective.
    if isinstance(x, bool) or isinstance(x, float):
        raise TypeError('Use integers, rational strings, or Fraction, not float/bool')
    return F(x)


def sha256_string(x):
    if not isinstance(x, str) or len(x) != 64 or any(c not in '0123456789abcdef' for c in x):
        raise ValueError('Expected a lowercase SHA256 digest')


@dataclass(frozen=True, order=True)
class RationalTarget:
    """Full-history rational policy table; row order: length then lexicographic (a,o)."""
    actions: int
    observations: int
    depth: int
    denominator: int
    rank: int

    def __post_init__(self):
        if any(type(x) is not int for x in asdict(self).values()):
            raise TypeError('Target indices must be integers')
        if min(self.actions, self.observations, self.denominator) < 1 or self.depth < 0:
            raise ValueError('Nonempty alphabets, positive denominator, nonnegative depth')
        # Implementation safety cap, not a restriction on the paper definition.
        if max(self.actions, self.observations) > 8 or self.depth > 8 or self.denominator > 64 or self.rows > 1024:
            raise ValueError('Prepared metadata size cap; larger families are defined only on paper here')
        if not 0 <= self.rank < self.count:
            raise ValueError('Table rank outside block')

    @property
    def rows(self):
        return sum((self.actions * self.observations)**r for r in range(self.depth))

    @property
    def row_choices(self):
        return comb(self.denominator + self.actions - 1, self.actions - 1)

    @property
    def count(self):
        return self.row_choices ** self.rows

    @property
    def key(self):
        return (f'rational-native-v1/a{self.actions}o{self.observations}/'
                f'n{self.depth}/d{self.denominator}/r{self.rank}')

    @property
    def mass(self):
        return F(1, 2**(self.depth + 1 + self.denominator) * self.count)

    def table(self, max_rows=256):
        """Decode one table, never enumerate a full block; refuse accidental expansion."""
        if self.rows > max_rows:
            raise ValueError('Table expansion exceeds explicit row limit')
        def unrank_composition(rank, total, parts):
            if parts == 1:
                return (total,)
            for first in range(total + 1):
                size = comb(total - first + parts - 2, parts - 2)
                if rank < size:
                    return (first,) + unrank_composition(rank, total - first, parts - 1)
                rank -= size
            raise AssertionError('Composition rank')
        ranks = [0] * self.rows
        remainder = self.rank
        for i in range(self.rows - 1, -1, -1):
            remainder, ranks[i] = divmod(remainder, self.row_choices)
        return tuple(tuple(F(k, self.denominator) for k in
                     unrank_composition(r, self.denominator, self.actions)) for r in ranks)


def background_id(actions, observations):
    return digest({'encoding': 'rational-native-v1', 'actions': actions,
                   'observations': observations, 'block_mass': '2^(-n-1-d)',
                   'table_order': 'lexicographic-compositions-full-history'})


@dataclass(frozen=True)
class Context:
    model_sha256: str
    geometry_sha256: str
    world_order_sha256: str
    collection_horizon: int
    variables: int
    record: str = RECORD
    policy_constraints: str = 'unrestricted-perfect-recall-flow-v1'

    def __post_init__(self):
        if self.policy_constraints != 'unrestricted-perfect-recall-flow-v1':
            raise ValueError('Reward-face constraints are not implemented in this adapter')
        for x in (self.model_sha256, self.geometry_sha256, self.world_order_sha256):
            sha256_string(x)
        if type(self.collection_horizon) is not int or self.collection_horizon < 1:
            raise ValueError('The prepared LP adapter requires collection t >= 1')
        if type(self.variables) is not int or self.variables < 1 or self.record != RECORD:
            raise ValueError('Invalid geometry or source record convention')

    @property
    def identity(self):
        return digest(self)


@dataclass(frozen=True)
class TargetBinding:
    target_id: str
    kernel_sha256: str
    record: str = RECORD

    def __post_init__(self):
        sha256_string(self.kernel_sha256)
        if not self.target_id or self.record not in (RECORD, 'deterministic-observation-tree-v1'):
            raise ValueError('Unknown target record convention')

    @property
    def identity(self):
        return digest(self)


@dataclass(frozen=True)
class Objective:
    context_id: str
    targets: tuple[TargetBinding, ...]
    weights: tuple[F, ...]
    omitted_mass: F
    interpretation: str
    provenance: str
    schema: str = SCHEMA

    def __post_init__(self):
        sha256_string(self.context_id)
        if self.schema != SCHEMA:
            raise ValueError('Unknown objective schema')
        if not self.targets or len(self.targets) != len(self.weights):
            raise ValueError('Nonempty, aligned target/weight vectors required')
        if len({t.target_id for t in self.targets}) != len(self.targets):
            raise ValueError('Duplicate target encoding: aggregate its mass explicitly')
        if any(not isinstance(w, F) or w < 0 for w in self.weights):
            raise ValueError('Weights must be nonnegative exact Fractions')
        if not isinstance(self.omitted_mass, F) or self.omitted_mass < 0:
            raise ValueError('Omitted mass must be a nonnegative exact Fraction')
        if sum(self.weights) + self.omitted_mass != 1:
            raise ValueError('Captured coefficients plus omitted mass must equal one')
        if self.interpretation not in ('finite-library', 'rich-background-truncation'):
            raise ValueError('Unknown mathematical scope')
        if self.interpretation == 'finite-library' and self.omitted_mass:
            raise ValueError('A finite-library objective has no unspecified tail')

    @property
    def identity(self):
        return digest(self)

    def manifest(self):
        return canonical(self) | {'objective_id': self.identity,
            'bounds_scope': 'finite-collection-time', 'eventual_regret_certified': False}

    @classmethod
    def finite(cls, context, targets, weights, provenance='explicit-finite-library'):
        return cls(context.identity, tuple(targets), tuple(map(rational, weights)),
                   F(0), 'finite-library', provenance)

    @classmethod
    def rich(cls, context, bindings, encodings, adaptive, epsilon):
        bindings, encodings = tuple(bindings), tuple(encodings)
        epsilon = rational(epsilon)
        if not 0 < epsilon < 1 or len(bindings) != len(encodings) or not encodings:
            raise ValueError('A nonempty selected set and 0 < epsilon < 1 are required')
        if any(b.target_id != e.key or b.record != RECORD for b, e in zip(bindings, encodings)):
            raise ValueError('Rich randomized targets must retain actions and match encoding')
        alphabets = {(e.actions, e.observations) for e in encodings}
        if len(alphabets) != 1:
            raise ValueError('One fixed interface is required')
        adaptive = {k: rational(v) for k, v in adaptive.items()}
        if any(v < 0 for v in adaptive.values()) or sum(adaptive.values()) != 1:
            raise ValueError('Adaptive part must be a probability distribution')
        if not set(adaptive).issubset({e.key for e in encodings}):
            raise ValueError('Selected set must include the adaptive support')
        captured = sum((e.mass for e in encodings), F(0))
        weights = tuple((1-epsilon)*adaptive.get(e.key, F(0)) + epsilon*e.mass for e in encodings)
        provenance = digest({'background_id': background_id(*next(iter(alphabets))),
                             'epsilon': epsilon, 'adaptive': adaptive})
        return cls(context.identity, bindings, weights, epsilon*(1-captured),
                   'rich-background-truncation', provenance)


@dataclass(frozen=True)
class Cut:
    context_id: str
    target_identity: str
    intercept: F
    slope: tuple[F, ...]
    witness_sha256: str
    provenance: str

    def __post_init__(self):
        for x in (self.context_id, self.target_identity, self.witness_sha256):
            sha256_string(x)
        if not isinstance(self.intercept, F) or any(not isinstance(x, F) for x in self.slope):
            raise ValueError('Cuts use explicit exact rationalized coefficients')
        if not self.provenance:
            raise ValueError('State whether the evidence is exact or numerical')

    def at(self, realization):
        if len(realization) != len(self.slope):
            raise ValueError('Realization dimension mismatch')
        return self.intercept - sum((s*rational(x) for s, x in zip(self.slope, realization)), F(0))


class CutCache:
    """Target-specific affine cuts; no aggregate optimality certificates are cached."""
    def __init__(self, context):
        self.context = context
        self._cuts = {}

    def add(self, target, cut):
        if cut.context_id != self.context.identity or cut.target_identity != target.identity:
            raise ValueError('A cut cannot cross model, geometry, or target bindings')
        if len(cut.slope) != self.context.variables:
            raise ValueError('Cut dimension mismatch')
        self._cuts[digest(cut)] = cut

    def for_objective(self, objective):
        if objective.context_id != self.context.identity:
            raise ValueError('Objective context mismatch')
        indices = {t.identity: i for i, t in enumerate(objective.targets)}
        return [(indices[c.target_identity], c) for c in self._cuts.values()
                if c.target_identity in indices]

    def manifest(self):
        return canonical({'schema': SCHEMA, 'context': self.context,
                          'cuts': list(self._cuts.values()), 'aggregate_bounds': None})

    @classmethod
    def restore(cls, manifest):
        if manifest.get('schema') != SCHEMA or manifest.get('aggregate_bounds') is not None:
            raise ValueError('Unknown cache schema or forbidden cached aggregate bounds')
        result = cls(Context(**manifest['context']))
        for row in manifest['cuts']:
            cut = Cut(row['context_id'], row['target_identity'], F(row['intercept']),
                      tuple(map(F, row['slope'])), row['witness_sha256'], row['provenance'])
            if cut.context_id != result.context.identity or len(cut.slope) != result.context.variables:
                raise ValueError('Corrupt cache context or dimensions')
            result._cuts[digest(cut)] = cut
        return result


@dataclass(frozen=True)
class PolicyIntervals:
    context_id: str
    policy_sha256: str
    intervals: tuple[tuple[str, F, F], ...]  # target identity, lower, upper
    provenance: str

    def __post_init__(self):
        sha256_string(self.context_id)
        sha256_string(self.policy_sha256)
        if len({r[0] for r in self.intervals}) != len(self.intervals):
            raise ValueError('Duplicate target intervals')
        for identity, lo, hi in self.intervals:
            sha256_string(identity)
            if not isinstance(lo, F) or not isinstance(hi, F) or not 0 <= lo <= hi <= 1:
                raise ValueError('Invalid deficiency interval')

    def aggregate(self, objective):
        if objective.context_id != self.context_id:
            raise ValueError('Policy evidence belongs to a different context')
        evidence = {key: (lo, hi) for key, lo, hi in self.intervals}
        if any(t.identity not in evidence for t in objective.targets):
            raise ValueError('A selected target lacks policy evidence')
        lo = sum((w*evidence[t.identity][0] for t, w in zip(objective.targets, objective.weights)), F(0))
        hi = sum((w*evidence[t.identity][1] for t, w in zip(objective.targets, objective.weights)), F(0))
        return lo, hi


@dataclass(frozen=True)
class MasterBound:
    context_id: str
    objective_id: str
    lower: F
    provenance: str


def finite_certificate(objective, policy, master):
    if (master.context_id, master.objective_id) != (objective.context_id, objective.identity):
        raise ValueError('Stale master bound: solve or explicitly transport to final weights')
    lo, hi = policy.aggregate(objective)
    if not isinstance(master.lower, F) or master.lower > hi:
        raise ValueError('Master lower bound exceeds selected feasible upper bound')
    full_hi = min(F(1), hi + objective.omitted_mass)
    return canonical({'schema': SCHEMA, 'objective_id': objective.identity,
        'context_id': objective.context_id, 'policy_sha256': policy.policy_sha256,
        'selected_policy_loss_interval': [lo, hi],
        'full_finite_policy_loss_interval': [lo, full_hi],
        'finite_score_interval': [1-full_hi, 1-lo],
        'full_finite_regret_upper': full_hi - max(F(0), master.lower),
        'eventual_score_lower': 1-full_hi,
        'eventual_regret_upper': None,
        'provenance': [policy.provenance, master.provenance],
        'warning': 'Numerical witnesses remain numerical; no finite-to-eventual rate is supplied'})


def exact_kernel_hash(kernel):
    return digest({'encoding': 'exact-matrix-v1', 'matrix': tuple(tuple(map(rational, r)) for r in kernel)})


def exact_geometry_hash(raw, leaf_index, variables):
    return digest({'encoding': 'exact-cut-geometry-v1', 'raw': tuple(tuple(map(rational, r)) for r in raw),
                   'leaf_index': tuple(leaf_index), 'variables': variables})


def exact_dual_cut(context, target, raw, leaf_index, kernel, alpha, b):
    """Construct a globally valid cut from an exactly feasible finite decoder dual.

    Every syntactic source column is used, even if the incumbent assigned zero
    realization weight. The caller supplies a valid controlled geometry and
    target experiment; this function checks dimensions/probabilities/dual bounds.
    """
    raw = tuple(tuple(map(rational, row)) for row in raw)
    kernel = tuple(tuple(map(rational, row)) for row in kernel)
    alpha = tuple(map(rational, alpha)); b = tuple(tuple(map(rational, row)) for row in b)
    if target.kernel_sha256 != exact_kernel_hash(kernel):
        raise ValueError('Exact target kernel is not the bound kernel')
    if context.geometry_sha256 != exact_geometry_hash(raw, leaf_index, context.variables):
        raise ValueError('Exact source geometry is not the bound geometry')
    q = len(raw)
    if not q or len(kernel) != q or len(alpha) != q or len(b) != q:
        raise ValueError('World count mismatch')
    h, y = len(raw[0]), len(kernel[0])
    if not h or not y or len(leaf_index) != h or any(len(r) != h for r in raw):
        raise ValueError('Source shape mismatch')
    if any(len(r) != y for r in kernel+b):
        raise ValueError('Target or dual shape mismatch')
    if any(x < 0 or x > 1 for row in raw for x in row):
        raise ValueError('Invalid controlled-prefix masses')
    if any(sum(row) != 1 or any(x < 0 for x in row) for row in kernel):
        raise ValueError('Target must be row stochastic')
    if sum(alpha) != 1 or any(a < 0 for a in alpha):
        raise ValueError('Dual world weights must be a distribution')
    if any(not 0 <= b[i][j] <= alpha[i] for i in range(q) for j in range(y)):
        raise ValueError('Infeasible dual witness')
    slopes = [F(0)] * context.variables
    for column, index in enumerate(leaf_index):
        if type(index) is not int or not 0 <= index < context.variables:
            raise ValueError('Bad realization index')
        slopes[index] += max(sum((raw[i][column]*b[i][j] for i in range(q)), F(0)) for j in range(y))
    intercept = sum((kernel[i][j]*b[i][j] for i in range(q) for j in range(y)), F(0))
    return Cut(context.identity, target.identity, intercept, tuple(slopes),
               digest({'alpha': alpha, 'b': b}), 'exact-feasible-dual; geometry assumed')


def coefficient_change_bounds(old, new):
    """Uniform bounds on (new-old) dot d for 0 <= d_j <= 1, no normalization assumed."""
    old, new = tuple(map(rational, old)), tuple(map(rational, new))
    if len(old) != len(new):
        raise ValueError('Align the same target coordinates before comparison')
    change = [n-o for o, n in zip(old, new)]
    return sum((min(F(0), c) for c in change), F(0)), sum((max(F(0), c) for c in change), F(0))


def exact_native_kernel(target, controlled_mass_rows, max_columns=4096):
    """Compile one rational target into its full recorded experiment, without a solver.

    Input rows are controlled-prefix masses ordered lexicographically by the full
    depth-n (action,observation) history. Valid causal masses are a caller premise;
    output stochasticity is checked. Actions are NEVER dropped for random targets.
    """
    size = (target.actions*target.observations)**target.depth
    if size > max_columns:
        raise ValueError('Explicit record expansion exceeds prepared size cap')
    rows = target.table(max_rows=1024)
    histories = [()]; decisions = []
    for _ in range(target.depth):
        decisions.extend(histories)
        histories = [h+((a,o),) for h in histories for a in range(target.actions)
                     for o in range(target.observations)]
    index = {h:i for i,h in enumerate(decisions)}
    policy_weights = []
    for h in histories:
        weight = F(1)
        for step,(a,_) in enumerate(h):
            weight *= rows[index[h[:step]]][a]
        policy_weights.append(weight)
    raw = tuple(tuple(map(rational,row)) for row in controlled_mass_rows)
    if not raw or any(len(row)!=size or any(not 0<=p<=1 for p in row) for row in raw):
        raise ValueError('Invalid controlled-mass matrix shape or entries')
    kernel = tuple(tuple(p*w for p,w in zip(row,policy_weights)) for row in raw)
    if any(sum(row)!=1 for row in kernel):
        raise ValueError('Supplied controlled masses do not yield a stochastic native record')
    return kernel
