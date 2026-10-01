import Formal.CausalDeficiency
import Formal.IndexedFiniteExperiment

/-!
# The concrete causal finitary process order

NativeProcess.lean proves the greatest-process characterization for chains
whose experiments all inhabit one ambient type. A causal prefix chain has a
different finite signal type at every horizon, so the paper's concrete
specialization uses `IndexedFiniteExperiment` to retain those alphabets.
Reflexivity and transitivity now instantiate the shared abstract theorems.

The wrapper proves that:

* exact prefix marginalization gives reflexivity;
* the finite directed-deficiency triangle inequality gives transitivity; and
* uniform simulation of all deterministic native tests is equivalent to
  being a greatest causal experiment process.

The last equivalence uses the finite-horizon causal universality theorem in
CausalDeficiency.lean in one direction and realizes each deterministic plan
as a valid causal policy in the other.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

/-- A causal policy bundled with its row-stochasticity proof. -/
abbrev ValidCausalPolicy (A O : Type*) [Fintype A] :=
  {π : CausalPolicy A O // IsCausalPolicy π}

/-- Directed deficiency between valid finite experiments is nonnegative.
This elementary fact is useful when an explicit zero-error decoder supplies
the reverse inequality. -/
theorem finiteDeficiency_nonneg_of_valid
    {Θ X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    0 ≤ finiteDeficiency E F := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid E F hE hF)
  rintro c ⟨G, _, herr⟩
  exact (decodeErr_nonneg E F G (Classical.arbitrary Θ)).trans
    (herr (Classical.arbitrary Θ))

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- Causal finitary dominance means that every fixed finite experiment
collected by the second policy is uniformly simulable from all sufficiently
late experiments collected by the first. The signal alphabets may differ
with the two horizons; finite deficiency handles that heterogeneity. -/
def CausalFinitaryDominates
    (Qs : Θ → CausalResponse A O)
    (π ρ : ValidCausalPolicy A O) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
    finiteDeficiency
      (causalFiniteExperiment π.1 Qs t)
      (causalFiniteExperiment ρ.1 Qs n) < ε

/-- A greatest causal experiment process dominates every valid causal policy
in the finitary process preorder. -/
def CausalFinitarilyGreatest
    (Qs : Θ → CausalResponse A O)
    (π : ValidCausalPolicy A O) : Prop :=
  ∀ ρ, CausalFinitaryDominates Qs π ρ

/-- Concrete native sufficiency: at each fixed depth, every deterministic
causal intervention is uniformly simulable from every sufficiently late
experiment collected by the policy. Actions do not appear in the target
signal because a deterministic plan reconstructs them from the observation
word; an existing theorem proves this encoding Blackwell-equivalent to the
full trace. -/
def CausalNativelySufficient
    (Qs : Θ → CausalResponse A O)
    (π : ValidCausalPolicy A O) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ τ : CausalPlan A O n,
    finiteDeficiency
      (causalFiniteExperiment π.1 Qs t)
      (causalPlanObservationExperiment n τ Qs) < ε

/-- The causal experiment chain in the shared heterogeneous experiment type. -/
noncomputable def causalExperimentProcess (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) (n : ℕ) :
    IndexedFiniteExperiment Θ (fun n => CausalFiniteTrace A O n) :=
  ⟨n, ⟨causalFiniteExperiment π.1 Qs n, causalFiniteExperiment_valid π.1 π.2 Qs hQ n⟩⟩

/-- The concrete causal order is definitionally the abstract process order. -/
theorem causalFinitaryDominates_iff_finitaryDominates
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π ρ : ValidCausalPolicy A O) :
    CausalFinitaryDominates Qs π ρ ↔
      FinitaryDominates (causalExperimentProcess Qs hQ) indexedFiniteDeficiency π ρ := Iff.rfl

/-- A later prefix of one valid causal policy has exactly zero deficiency to
an earlier prefix: the decoder simply forgets the extra coordinates. -/
theorem finiteDeficiency_causalPrefix_eq_zero
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {m n : ℕ} (hmn : m ≤ n) :
    finiteDeficiency
      (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs m) = 0 := by
  obtain ⟨G, hG, hEq⟩ :=
    causalFiniteExperiment_prefix_blackwell_of_le π hπ Qs hQ hmn
  have hup :
      finiteDeficiency
        (causalFiniteExperiment π Qs n)
        (causalFiniteExperiment π Qs m) ≤ 0 := by
    apply finiteDeficiency_le_of_decoder
      (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs m) G hG 0
    intro θ
    change finiteTV
      (finiteDecisionLaw (causalFiniteExperiment π Qs n) G θ)
      (causalFiniteExperiment π Qs m θ) ≤ 0
    rw [congrFun hEq θ]
    simp [finiteTV]
  exact le_antisymm hup
    (finiteDeficiency_nonneg_of_valid
      (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs m)
      (causalFiniteExperiment_valid π hπ Qs hQ n)
      (causalFiniteExperiment_valid π hπ Qs hQ m))

/-- Exact causal prefix marginalization makes finitary dominance reflexive. -/
theorem causalFinitaryDominates_refl
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalFinitaryDominates Qs π π := by
  exact finitaryDominates_refl (causalExperimentProcess Qs hQ) indexedFiniteDeficiency
    (fun π _ _ hnt => finiteDeficiency_causalPrefix_eq_zero π.1 π.2 Qs hQ hnt) π

/-- The concrete causal finitary order is transitive. The middle horizon is
chosen first; the heterogeneous deficiency triangle inequality then composes
the two simulations. -/
theorem causalFinitaryDominates_trans
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {π ρ σ : ValidCausalPolicy A O}
    (hπρ : CausalFinitaryDominates Qs π ρ)
    (hρσ : CausalFinitaryDominates Qs ρ σ) :
    CausalFinitaryDominates Qs π σ := by
  exact finitaryDominates_trans (causalExperimentProcess Qs hQ) indexedFiniteDeficiency
    indexedFiniteDeficiency_triangle hπρ hρσ

/-- Reflexivity and transitivity package the causal comparison as the exact
finitary process preorder used in the paper. -/
theorem causalFinitaryDominates_isPreorder
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    (∀ π, CausalFinitaryDominates Qs π π) ∧
      (∀ π ρ σ,
        CausalFinitaryDominates Qs π ρ →
        CausalFinitaryDominates Qs ρ σ →
        CausalFinitaryDominates Qs π σ) :=
  ⟨causalFinitaryDominates_refl Qs hQ,
    fun _ _ _ => causalFinitaryDominates_trans Qs hQ⟩

/-- Greatest causal processes are unique up to mutual finitary dominance. -/
theorem causalFinitarilyGreatest_equivalent
    (Qs : Θ → CausalResponse A O)
    {π ρ : ValidCausalPolicy A O}
    (hπ : CausalFinitarilyGreatest Qs π)
    (hρ : CausalFinitarilyGreatest Qs ρ) :
    CausalFinitaryDominates Qs π ρ ∧
      CausalFinitaryDominates Qs ρ π :=
  ⟨hπ ρ, hρ π⟩

/-- Concrete causal greatest-process characterization.

For an arbitrary nonempty world class of valid causal response kernels, a
policy uniformly simulates every finite deterministic native intervention if
and only if its growing experiment process finitarily dominates every valid
causal policy process.

The forward implication is the exact finite-horizon universality theorem:
the worst deterministic-plan deficiency bounds every behavioral-policy
experiment at that horizon. For the reverse implication, every deterministic
plan is realized by a valid causal policy; finiteness of the plan family gives
one common cutoff by summing its individual cutoffs. -/
theorem causalNativelySufficient_iff_finitarilyGreatest
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      CausalFinitarilyGreatest Qs π := by
  constructor
  · intro hnative ρ n ε hε
    obtain ⟨T, hT⟩ := hnative n ε hε
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨τ, hτ⟩ :=
      exists_causalPlan_eq_nativeDeficiency
        (causalFiniteExperiment π.1 Qs t) Qs n
    have hle :
        finiteDeficiency
          (causalFiniteExperiment π.1 Qs t)
          (causalFiniteExperiment ρ.1 Qs n) ≤
        causalNativeDeficiency
          (causalFiniteExperiment π.1 Qs t) Qs n :=
      finiteDeficiency_causalPolicy_le_native_at_horizon
        (causalFiniteExperiment π.1 Qs t)
        (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
        ρ.1 ρ.2 Qs hQ n
    exact hle.trans_lt (by
      rw [hτ]
      exact hT t ht τ)
  · intro hgreat n ε hε
    classical
    choose cutoff hcutoff using
      fun τ : CausalPlan A O n =>
        hgreat
          (⟨causalPolicyOfPlan n τ,
            isCausalPolicy_causalPolicyOfPlan n τ⟩ :
            ValidCausalPolicy A O)
          n ε hε
    refine ⟨∑ τ, cutoff τ, ?_⟩
    intro t ht τ
    have hτcutoff : cutoff τ ≤ ∑ q, cutoff q := by
      exact Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    rw [finiteDeficiency_causalPlanObservation_eq_full
      (causalFiniteExperiment π.1 Qs t)
      (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
      Qs hQ n τ]
    exact hcutoff τ t (hτcutoff.trans ht)

/-- With only one available action, normalization leaves no policy choice,
even when policies are allowed arbitrary history dependence and randomization. -/
theorem validCausalPolicy_eq_of_subsingleton_action [Subsingleton A]
    (π ρ : ValidCausalPolicy A O) : π = ρ := by
  apply Subtype.ext
  funext h a
  have hsum (f : A → ℝ) : ∑ b, f b = f a := by
    apply Finset.sum_eq_single a
    · intro b _ hba
      exact (hba (Subsingleton.elim b a)).elim
    · simp
  have hp : π.val h a = 1 := by simpa only [hsum] using (π.property h).2
  have hr : ρ.val h a = 1 := by simpa only [hsum] using (ρ.property h).2
  exact hp.trans hr.symm

/-- An actionless interface is always natively sufficient: its unique policy
already runs every native intervention. This does not assert identification
of the world or convergence of any localization risk. -/
theorem causalNativelySufficient_of_subsingleton_action [Subsingleton A]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : CausalNativelySufficient Qs π := by
  apply (causalNativelySufficient_iff_finitarilyGreatest Qs hQ π).2
  intro ρ
  rw [validCausalPolicy_eq_of_subsingleton_action ρ π]
  exact causalFinitaryDominates_refl Qs hQ π

end IdExp
