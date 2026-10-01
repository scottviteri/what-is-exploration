import Formal.FiniteProbability
import Formal.Hellinger

/-!
# Finite-POMDP model-recovery specialization

Definitions for the retained attained-full-revelation results: finite POMDPs,
initial-observation histories, likelihoods, posteriors, and information
objectives. These are specialization assumptions, not the causal-first
ontology. See `CausalKernel.lean` for that ontology and `Formal/PAPER_SUPPORT.json`
for current claim support. `Formal/STATEMENTS.md` retains the earlier finite-POMDP
draft's numbering and formalization history. Generic finite probability primitives are
re-exported from `FiniteProbability.lean` for import compatibility. General
Hellinger definitions are re-exported from `Hellinger.lean`.

Time zero already includes the standalone observation: `histPrefix 0` is
`(o0, [])`. `CausalHistory` instead starts at `[]`. `POMDPCausalBehavior.lean`
marginalizes o0; it does not preserve policies that can condition on o0.
See the interface-convention table in `Formal/README.md` before crossing layers.
-/

namespace IdExp

open MeasureTheory Finset
open scoped ENNReal

variable {C : Type*} [Fintype C]

/-! ## Finite POMDPs and controlled trace likelihoods -/

/-- A finite POMDP hypothesis over shared action/observation alphabets `A`, `O`.
The hidden-state type is bundled because different hypotheses may
use different state spaces.  Stochasticity is NOT baked in; see `POMDP.Valid`. -/
structure POMDP (A O : Type*) where
  S : Type
  [fintS : Fintype S]
  /-- initial hidden-state law `μᵢ` -/
  init : S → ℝ
  /-- transition kernel `Tᵢᵃ(s' | s)` -/
  trans : A → S → S → ℝ
  /-- emission kernel `Eᵢ(o | s)` -/
  emit : S → O → ℝ

attribute [instance] POMDP.fintS

variable {A O : Type*} [Fintype A] [Fintype O]

/-- Nonnegative, normalized initial, transition and emission distributions. -/
def POMDP.Valid (M : POMDP A O) : Prop :=
  (∀ s, 0 ≤ M.init s) ∧ (∑ s, M.init s = 1) ∧
  (∀ a s s', 0 ≤ M.trans a s s') ∧ (∀ a s, ∑ s', M.trans a s s' = 1) ∧
  (∀ s o, 0 ≤ M.emit s o) ∧ (∀ s, ∑ o, M.emit s o = 1)

/-- A finite history `h_t = (o₀, a₀, o₁, …, a_{t−1}, o_t)`: the
initial observation plus a CHRONOLOGICALLY ordered list of (action, next
observation) steps. -/
abbrev Hist (A O : Type*) := O × List (A × O)

/-- One step of the forward (unnormalized filtering) recursion. -/
noncomputable def stepLik (M : POMDP A O) (f : M.S → ℝ) (ao : A × O) : M.S → ℝ :=
  fun s' => (∑ s, f s * M.trans ao.1 s s') * M.emit s' ao.2

/-- Unnormalized forward state weights after consuming the history. -/
noncomputable def fwd (M : POMDP A O) (o₀ : O) (steps : List (A × O)) : M.S → ℝ :=
  steps.foldl (stepLik M) (fun s => M.init s * M.emit s o₀)

/-- Controlled trace likelihood `ℓᵢ(h_t | a_{0:t−1})`: the
probability of the observation word given the action word, marginalizing the
hidden states. -/
noncomputable def traceLik (M : POMDP A O) (h : Hist A O) : ℝ :=
  ∑ s, fwd M h.1 h.2 s

/-- Controlled behavioral equivalence: equal controlled trace
likelihoods for EVERY finite history. -/
def BehEq (M M' : POMDP A O) : Prop := ∀ h : Hist A O, traceLik M h = traceLik M' h

/-! ## Policies -/

/-- A general randomized nonanticipating policy: a history-indexed distribution
over actions.  With countable histories and finite `A` no measurability
condition is needed. -/
def Policy (A O : Type*) := Hist A O → A → ℝ

def IsPolicy (π : Policy A O) : Prop := ∀ h, (∀ a, 0 ≤ π h a) ∧ ∑ a, π h a = 1

/-- Product of the policy's action probabilities along a history. -/
noncomputable def polWeightAux (π : Policy A O) (o₀ : O) :
    List (A × O) → List (A × O) → ℝ
  | _, [] => 1
  | pre, ao :: rest => π (o₀, pre) ao.1 * polWeightAux π o₀ (pre ++ [ao]) (rest)

noncomputable def polWeight (π : Policy A O) (h : Hist A O) : ℝ :=
  polWeightAux π h.1 [] h.2

/-- Finite-horizon trace probability `P^π_i(H_t = h_t)`. -/
noncomputable def traceProb (π : Policy A O) (M : POMDP A O) (h : Hist A O) : ℝ :=
  polWeight π h * traceLik M h

/-! ## Infinite path laws

The path space is `Ω_∞ = O × (A × O)^ℕ`.  Rather than constructing `P^π_c`
here (Ionescu–Tulcea), the development is PARAMETERIZED by any measure with the
correct finite-dimensional cylinder probabilities (`IsPathLaw`); existence and
uniqueness are stated as theorems in `Formal.Statements`.  This keeps every
statement about path laws independent of the construction route. -/

/-- The infinite path space `Ω_∞`. -/
abbrev Traj (A O : Type*) := O × (ℕ → A × O)

variable [MeasurableSpace A] [MeasurableSpace O]

/-- The cylinder set of trajectories extending a finite history. -/
def cyl (h : Hist A O) : Set (Traj A O) :=
  {ω | ω.1 = h.1 ∧ ∀ (k : ℕ) (hk : k < h.2.length), ω.2 k = h.2[k]'hk}

/-- `μ` is the path law of policy `π` in POMDP `M`: a probability measure on
`Ω_∞` whose cylinder probabilities are the finite-horizon trace probabilities. -/
structure IsPathLaw (π : Policy A O) (M : POMDP A O) (μ : Measure (Traj A O)) :
    Prop where
  isProb : IsProbabilityMeasure μ
  cylinder : ∀ h : Hist A O, μ (cyl h) = ENNReal.ofReal (traceProb π M h)

/-! ## Posteriors, joint law, concentration -/

variable {Θ : Type*} [Fintype Θ]

/-- Class posterior `ρ_t(θ)` after a finite history, as an explicit ratio of
trace likelihoods (policy factors cancel).  On histories of zero
mixture probability this is `0/0 = 0` by Lean's convention — a junk value on a
null set; see STATEMENTS.md. -/
noncomputable def posterior (α : Θ → ℝ) (Ms : Θ → POMDP A O) (h : Hist A O)
    (θ : Θ) : ℝ :=
  α θ * traceLik (Ms θ) h / ∑ θ', α θ' * traceLik (Ms θ') h

/-- The Bayesian joint law `P^π_α(c, dω) = α(c) P^π_c(dω)` on `Θ × Ω_∞`,
assembled from a path-law family. -/
noncomputable def jointLaw [MeasurableSpace Θ] (α : Θ → ℝ)
    (μfam : Θ → Measure (Traj A O)) : Measure (Θ × Traj A O) :=
  Measure.sum fun θ => ENNReal.ofReal (α θ) • (Measure.dirac θ).prod (μfam θ)

/-- T action-observation steps plus the initial observation, retained even at T=0. -/
def histPrefix (T : ℕ) (ω : Traj A O) : Hist A O :=
  (ω.1, List.ofFn fun k : Fin T => ω.2 k)

/-- Posterior concentration on the true class:
`ρ_t(C⋆) → 1` almost surely under the Bayesian joint law. -/
def ConcentratesOnTruth [MeasurableSpace Θ] (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (μfam : Θ → Measure (Traj A O)) : Prop :=
  ∀ᵐ ω ∂ jointLaw α μfam,
    Filter.Tendsto (fun T => posterior α Ms (histPrefix T ω.2) ω.1)
      Filter.atTop (nhds 1)

/-- A policy identifies the (pre-quotiented) family when all its path laws are
pairwise mutually singular.  Quantified over every path-law
family; combined with uniqueness (`pathLaw_unique`) this is equivalent to singularity of any one path-law family. -/
def Identifies (Ms : Θ → POMDP A O) (π : Policy A O) : Prop :=
  ∀ μfam : Θ → Measure (Traj A O), (∀ θ, IsPathLaw π (Ms θ) (μfam θ)) →
    Pairwise fun θ θ' => μfam θ ⟂ₘ μfam θ'

/-- Uniform identifiability: some common policy identifies. -/
def UniformlyIdentifiable (Ms : Θ → POMDP A O) : Prop :=
  ∃ π : Policy A O, IsPolicy π ∧ Identifies Ms π

/-! ## Terminal mutual information -/

variable [DecidableEq A] [DecidableEq O]

/-- All histories of length `T` as a finite set. -/
noncomputable def histSet (A O : Type*) [Fintype A] [Fintype O] [DecidableEq A]
    [DecidableEq O] (T : ℕ) : Finset (Hist A O) :=
  (Finset.univ : Finset (O × (Fin T → A × O))).image fun x => (x.1, List.ofFn x.2)

/-- `I_T = I(C⋆; H_T)`, in the entropy form `H(α) − E[H(ρ_T)]`. -/
noncomputable def infoAt (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O)
    (T : ℕ) : ℝ :=
  ent α - ∑ h ∈ histSet A O T,
    (∑ θ, α θ * traceProb π (Ms θ) h) * ent (posterior α Ms h)

/-- `I_∞ = I(C⋆; H_∞)`, via `I_T ↑ I_∞`
(monotone supremum of the finite-horizon curve). -/
noncomputable def infoInf (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O) : ℝ :=
  ⨆ T, infoAt α Ms π T

end IdExp
