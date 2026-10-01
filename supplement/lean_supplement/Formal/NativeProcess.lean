import Formal.Frontier

/-!
# The finitary process order

The terminal experiment of a policy is not, on an infinite world class, a
uniform approximation to its finite prefixes. The operational comparison used
by the native-test theory therefore orders the *growing processes* directly.

`FinitaryDominates K δ π σ` says that, for every fixed finite prefix of `σ`,
sufficiently late prefixes of `π` approximate it arbitrarily well in the
directed error `δ`. The two elementary facts needed in the paper are proved
below:

* later prefixes make every process dominate itself; and
* a triangle inequality makes finitary dominance transitive.

For Le Cam deficiency, the preorder hypotheses are respectively marginalization of
prefixes and the deficiency triangle inequality. This file also proves native
sufficiency equivalent to greatestness under explicit finite-test universality
and representability hypotheses. `CausalUniversality.lean` now checks the exact
finite causal experiment mixture, deterministic observation/action relabeling, and
the fixed-error decoder implication used to discharge finite-test universality.
The heterogeneous finite-experiment adapter in `IndexedFiniteExperiment.lean`
and `causalExperimentProcess` in `CausalProcess.lean` instantiate this order
without imposing a common signal alphabet.
-/

namespace IdExp

/-- `π` finitarily dominates `σ` when every fixed finite experiment in `σ`'s
prefix chain is approximated arbitrarily well by all sufficiently late
experiments in `π`'s prefix chain. -/
def FinitaryDominates {P X : Type*} (K : P → ℕ → X) (δ : X → X → ℝ)
    (π σ : P) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t → δ (K π t) (K σ n) < ε

/-- A process is finitarily greatest when it dominates every process. -/
def FinitarilyGreatest {P X : Type*} (K : P → ℕ → X) (δ : X → X → ℝ)
    (π : P) : Prop :=
  ∀ σ, FinitaryDominates K δ π σ

/-- Prefix marginalization gives reflexivity of the finitary process order.
For deficiency, a later prefix simulates an earlier prefix with zero error. -/
theorem finitaryDominates_refl {P X : Type*} (K : P → ℕ → X) (δ : X → X → ℝ)
    (hprefix : ∀ π n t, n ≤ t → δ (K π t) (K π n) = 0) (π : P) :
    FinitaryDominates K δ π π := by
  intro n ε hε
  refine ⟨n, fun t hnt => ?_⟩
  rw [hprefix π n t hnt]
  exact hε

/-- The triangle inequality gives transitivity of the finitary process order.
The proof first chooses one sufficiently informative prefix of the middle
process and then a sufficiently late prefix of the first process. -/
theorem finitaryDominates_trans {P X : Type*} (K : P → ℕ → X) (δ : X → X → ℝ)
    (htriangle : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {π σ τ : P} (hπσ : FinitaryDominates K δ π σ)
    (hστ : FinitaryDominates K δ σ τ) :
    FinitaryDominates K δ π τ := by
  intro n ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨s, hs⟩ := hστ n (ε / 2) hhalf
  have hs' : δ (K σ s) (K τ n) < ε / 2 := hs s le_rfl
  obtain ⟨T, hT⟩ := hπσ s (ε / 2) hhalf
  refine ⟨T, fun t ht => ?_⟩
  calc
    δ (K π t) (K τ n) ≤ δ (K π t) (K σ s) + δ (K σ s) (K τ n) :=
      htriangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hT t ht) hs'
    _ = ε := by ring

/-- Under prefix marginalization and a triangle inequality, finitary dominance
is a preorder. We state the two laws explicitly rather than installing a
global instance depending on the chosen process map and directed distance. -/
theorem finitaryDominates_isPreorder {P X : Type*} (K : P → ℕ → X)
    (δ : X → X → ℝ)
    (hprefix : ∀ π n t, n ≤ t → δ (K π t) (K π n) = 0)
    (htriangle : ∀ x y z, δ x z ≤ δ x y + δ y z) :
    (∀ π, FinitaryDominates K δ π π) ∧
      (∀ π σ τ, FinitaryDominates K δ π σ → FinitaryDominates K δ σ τ →
        FinitaryDominates K δ π τ) :=
  ⟨finitaryDominates_refl K δ hprefix,
    fun _ _ _ => finitaryDominates_trans K δ htriangle⟩

/-- Greatest processes are unique up to mutual finitary dominance. -/
theorem finitarilyGreatest_equivalent {P X : Type*} (K : P → ℕ → X)
    (δ : X → X → ℝ) {π σ : P}
    (hπ : FinitarilyGreatest K δ π) (hσ : FinitarilyGreatest K δ σ) :
    FinitaryDominates K δ π σ ∧ FinitaryDominates K δ σ π :=
  ⟨hπ σ, hσ π⟩

/-! ## Finite native-test bridge -/

/-- Native sufficiency stated against a finite test family at every depth.  The convergence is
uniform over the tests at a fixed depth, but the cutoff may depend on depth and tolerance. -/
def NativelySufficient {P X : Type*} {Test : ℕ → Type*}
    (K : P → ℕ → X) (δ : X → X → ℝ) (target : ∀ n, Test n → X) (π : P) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ q, δ (K π t) (target n q) < ε

/-- **Greatest-process characterization from finite-horizon universality.**

`hpolicy` is the universality direction saying that simultaneous simulation of every deterministic
native test at depth `n` simulates every policy prefix at that depth. `hrepresent` says every
deterministic native test is itself a policy prefix. Under these two domain-specific facts and
finiteness of the depth-`n` test family, native sufficiency is exactly greatestness in the finitary
process order.  The reverse direction explicitly takes one common cutoff by summing the finitely
many individual cutoffs. -/
theorem nativelySufficient_iff_finitarilyGreatest_of_finite
    {P X : Type*} {Test : ℕ → Type*} [∀ n, Fintype (Test n)]
    (K : P → ℕ → X) (δ : X → X → ℝ) (target : ∀ n, Test n → X)
    (hpolicy : ∀ (E : X) (σ : P) (n : ℕ) (ε : ℝ), 0 < ε →
      (∀ q, δ E (target n q) < ε) → δ E (K σ n) < ε)
    (hrepresent : ∀ n q, ∃ σ : P, K σ n = target n q) (π : P) :
    NativelySufficient K δ target π ↔ FinitarilyGreatest K δ π := by
  constructor
  · intro hnative σ n ε hε
    obtain ⟨T, hT⟩ := hnative n ε hε
    exact ⟨T, fun t ht => hpolicy (K π t) σ n ε hε (hT t ht)⟩
  · intro hgreat n ε hε
    choose σ hσ using fun q => hrepresent n q
    choose cutoff hcutoff using fun q => hgreat (σ q) n ε hε
    refine ⟨∑ q, cutoff q, fun t ht q => ?_⟩
    have hq : cutoff q ≤ ∑ q, cutoff q := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [← hσ q]
    exact hcutoff q t (hq.trans ht)

end IdExp
