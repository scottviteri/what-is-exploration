# Next confirmation: draft, not frozen or launched

The purpose is to test how much of the observed finite capability tradeoff survives
new independent world classes. It is not to secure a favorable native result.
The existing two-seed study is development evidence for choosing this focused
follow-up; its findings must not be described as independent confirmation of this
newly selected presentation.

## Proposed fixed design

1. Eight new independent generator seed families, each at four/eight worlds and
   Dirichlet concentrations 0.2/1/5: 48 paired settings. Select unused seeds by a
   metadata-only scan and a deterministic rule recorded **before** generating
   outcomes. Keep every resulting setting. The next unused consecutive integers
   after the existing seed set are a candidate rule, not seeds frozen here.
2. Same three hidden states, binary interface, known initial state, candidate-model
   access, full-history policies, uniform prior, collection length three, and
   exhaustive four-step target audit. Keep the frozen 131 training targets and
   fixed native coefficients. Do not tune weights on these cases.
3. Main methods: fixed native weights, finite minimax, information, Brier, uniform;
   favorable information/Brier controls at 0/1/5% achievable-range regret. This is
   nine planning jobs per case (two native, six constrained, one combined baseline
   job), producing eleven method endpoints. Adaptive methods are deferred equally
   for all fresh classes, based on the scientific question and mixed existing
   evidence rather than fresh outcomes.
4. Primary confirmation: forty-second endpoints. Save two/ten-second checkpoints
   prospectively, but treat exhaustive validation of all early checkpoints as a
   separately budgeted computational study; do not delay a complete primary audit
   for a large adaptive/early-endpoint sweep. If the early audit extension is run,
   include all its planned settings rather than favorable ones.
5. Primary outcome: paired `A_{3,4}` difference for fixed weights versus ordinary
   Brier and versus the 5%-Brier control. Both comparisons are obligatory. Report
   information, all other controls, and finite minimax in the same table. Describe
   effects within each parameter cell and across independent seed families;
   repeated parameter settings and targets do not inflate replication counts.
   For each comparator, compute the six within-family differences
   `A_baseline - A_fixed`, then their equal-weight arithmetic mean. The primary
   summary is the arithmetic mean of the eight family means, accompanied by all
   eight individual means, their range, and the count positive/negative/unresolved.
   Carry numerical paired intervals through those same linear averages. Report
   all six parameter-cell means separately; the all-setting median is secondary.
   This estimand is the declared uniform parameter mixture, not a natural-world
   population. No statistical-significance test is currently proposed.
6. Repeat the same-time two-direction diagnostic for fixed/minimax versus
   information/Brier/uniform, and actual full-world reward calculations. They are
   now prospectively included, with all pairs retained. This tests whether lower
   scalar error again accompanies a tradeoff rather than dominance.
7. Keep source binding, full target coverage, numerical feasibility/gap checks,
   original failures/recovery, and missing endpoints visible. A timeout gives a
   valid partial lower/global-upper bracket, never the maximum of subset uppers.
   Per-audit cap: 1,800 seconds, matching the completed study. Preserve any
   validated partial witnesses. Recover from supervisor/process interruption by
   replaying the unchanged task once; a numerical-validation failure is not
   silently retried under looser tolerances. One predeclared 3,600-second retry
   applies to every timed-out audit, irrespective of method or current result;
   retain both attempts and their costs. Any still-unfinished audit remains a
   partial bound and unresolved where intervals overlap. Cap the whole campaign
   at 12 hours, preserving the unstarted queue and coverage; this is a resource
   stop, not an effect-based stop. Do not add seeds after an unfavorable result.
   Check disk space against frozen pilot artifact sizes before launching.

## Falsifiable interpretation rules

- Useful positive result: both prespecified cross-family mean improvements have
  numerical intervals strictly above zero,
  with every family-level sign, absolute effect size, reward sacrifice, and extra
  computation visible. Mixed family signs must be described as heterogeneity;
  passing this descriptive sign criterion is not a significance test or a
  claim of superiority on another distribution. There is no retrospective
  practical-effect threshold.
- Useful negative result: gains disappear, reverse, depend sharply on generator
  parameters, or are almost fully reproduced by small posterior reward concessions.
  That would support an empirical ending about objective tradeoffs while opposing
  a broad native-superiority claim.
- Failure of computation/certification: report the unresolved grid and computational
  limits; do not silently drop cases, relax tolerances, or replace exhaustive audits
  with sampled targets while retaining the same claim.
- Same-time incomparability never establishes eventual incomparability. Neither
  favorable nor unfavorable finite experiments refute the paper's eventual-order
  representation theorem.

## Resources and implementation

Use the completed CPU decomposition solver and validated witness checker as frozen
source dependencies. GPUs are not the default: the prior pilots did not establish
reliable speedups at the required tolerances. The container quota is about 10.2 CPU
cores despite 96 visible CPUs. Check actual activity and cgroup limits again before
launch; tentatively use eight single-threaded workers and preserve capacity for
interactive work. Affinity alone does not reserve CPU quota.

At the primary forty-second endpoint there are at most 48 × 11 = 528 distinct
acquired-experiment audits before exact-matrix deduplication. At the completed
study's observed fresh average of about 232 numerical seconds plus 16 validation
seconds, that is roughly 36 single-worker hours, or 4.6 hours at ideal eight-way
parallelism, **before** planning, startup, I/O, long tails, and contention. This is
an order-of-magnitude overnight estimate, not a promised completion time or a claim
that measured process-wall seconds are pure CPU time. Some prior audits exceeded
1,300 seconds. The planning caps add at most roughly 4.8 single-worker hours for
432 jobs, excluding interpreter startup/output; actual static convergence is often
much earlier. Early checkpoints can multiply the evaluation work substantially.

Implement in a new dated directory: frozen protocol → seed/model manifest → copied
source/dependency hashes → complete planning queue → deduplicated primary audit
queue → independent checks → all-case figure/report. Reuse numerical witnesses
only for byte-identical experiments in the same world class, with recorded original
cost and new validation; never transfer a certificate between unrelated seeds.
Ask Missing citations to explain and critique this design before freezing it.

A longer collection horizon is a separate subsequent question. Moving from three
to four collected steps changes policy-space and LP cost; increasing target depth
from four to five increases deterministic binary trees from 32,768 to
2,147,483,648. Exhaustive depth-five enumeration is not a routine scaling option.
It needs another formulation or honest lower/upper certificates, not simply a
longer overnight run.
