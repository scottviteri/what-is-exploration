import Formal.CausalObservationPlan
import Formal.CausalBehaviorGeometry
import Formal.CausalProcess

/-!
# Native capability directly on controlled-prefix behaviors

The core causal comparison theorems were originally stated for families of
valid raw response presentations.  `CausalBehavior` is now the canonical
finite-alphabet world carrier, and `CausalBehaviorExperiment` already proves
that all acquired and native experiments are independent of the arbitrary
rows used to present a behavior.

This file exposes the paper's central finite-horizon universality and
greatest-process theorem directly on families of controlled-prefix behaviors.
Its native tests use the literal observation-tree type from
`CausalObservationPlan`; the bridge theorem there proves that this is exactly
the same experiment family as the older full-history plan type.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {A O Θ X : Type*} [Fintype A] [Fintype O] [Fintype X]
  [Nonempty A] [Nonempty O]

/-- A canonical executable presentation of a class of direct behaviors.  It
is used only to transport old theorems; direct definitions below are written
in terms of behavior experiments. -/
noncomputable def causalBehaviorResponsePresentation
    (ps : Θ → CausalBehavior A O) : Θ → CausalResponse A O :=
  fun θ => (ps θ).toResponse

theorem causalBehaviorResponsePresentation_valid
    (ps : Θ → CausalBehavior A O) (θ : Θ) :
    IsCausalResponse (causalBehaviorResponsePresentation ps θ) :=
  (ps θ).toResponse_valid

/-- The direct acquired experiment equals the experiment of the canonical
raw presentation. -/
theorem causalBehaviorFiniteExperiment_eq_toResponse
    (π : CausalPolicy A O) (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorFiniteExperiment π ps n =
      causalFiniteExperiment π (causalBehaviorResponsePresentation ps) n := by
  let Qs := causalBehaviorResponsePresentation ps
  have hQ : ∀ θ, IsCausalResponse (Qs θ) :=
    causalBehaviorResponsePresentation_valid ps
  have h := causalBehaviorFiniteExperiment_ofResponse π Qs hQ n
  simpa [Qs, causalBehaviorResponsePresentation] using h

/-- The direct native experiment of a full-history plan equals the experiment
of the canonical raw presentation. -/
theorem causalBehaviorPlanExperiment_eq_toResponse
    (n : ℕ) (τ : CausalPlan A O n) (ps : Θ → CausalBehavior A O) :
    causalBehaviorPlanExperiment n τ ps =
      causalPlanObservationExperiment n τ
        (causalBehaviorResponsePresentation ps) := by
  let Qs := causalBehaviorResponsePresentation ps
  have hQ : ∀ θ, IsCausalResponse (Qs θ) :=
    causalBehaviorResponsePresentation_valid ps
  have h := causalBehaviorPlanExperiment_ofResponse n τ Qs hQ
  simpa [Qs, causalBehaviorResponsePresentation] using h

/-- The paper's observation-only native experiment equals the corresponding
raw-presentation experiment after embedding its observation tree. -/
theorem causalBehaviorObservationPlanExperiment_eq_toResponse
    {n : ℕ} (σ : CausalObservationPlan A O n)
    (ps : Θ → CausalBehavior A O) :
    CausalObservationPlan.behaviorPlanExperiment σ ps =
      causalPlanObservationExperiment n σ.toCausalPlan
        (causalBehaviorResponsePresentation ps) := by
  rw [CausalObservationPlan.behaviorPlanExperiment_toCausalPlan,
    causalBehaviorPlanExperiment_eq_toResponse]

/-- Every old full-history native plan is represented by an observation-only
plan with exactly the same raw-presentation target experiment. -/
theorem causalBehaviorObservationPlanExperiment_ofCausalPlan_eq_toResponse
    {n : ℕ} (τ : CausalPlan A O n)
    (ps : Θ → CausalBehavior A O) :
    CausalObservationPlan.behaviorPlanExperiment
        (CausalObservationPlan.ofCausalPlan τ) ps =
      causalPlanObservationExperiment n τ
        (causalBehaviorResponsePresentation ps) := by
  rw [CausalObservationPlan.behaviorPlanExperiment_ofCausalPlan,
    causalBehaviorPlanExperiment_eq_toResponse]

/-! ## Direct native geometry bound -/

/-- The randomized-policy inequality in the native-geometry proposition,
stated literally on two controlled-prefix behaviors. -/
theorem causalBehaviorPolicy_tv_le_depthDist
    [DecidableEq A] [DecidableEq O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (n : ℕ) (p q : CausalBehavior A O) :
    finiteTV (causalBehaviorFiniteExperiment π id n p)
        (causalBehaviorFiniteExperiment π id n q) ≤
      causalBehaviorDepthDist n p q := by
  let P : ValidCausalWorld A O := ⟨p.toResponse, p.toResponse_valid⟩
  let Q : ValidCausalWorld A O := ⟨q.toResponse, q.toResponse_valid⟩
  have hraw := causalPolicy_tv_le_nativeDepthDist π hπ n P Q
  have hp :
      causalBehaviorFiniteExperiment π id n p =
        causalFiniteExperiment π Subtype.val n P := by
    funext w
    change causalBehaviorTraceProb π p (List.ofFn w) =
      causalTraceProb π p.toResponse (List.ofFn w)
    rw [causalTraceProb_eq_behaviorTraceProb
        π p.toResponse p.toResponse_valid,
      CausalBehavior.ofResponse_toResponse]
  have hq :
      causalBehaviorFiniteExperiment π id n q =
        causalFiniteExperiment π Subtype.val n Q := by
    funext w
    change causalBehaviorTraceProb π q (List.ofFn w) =
      causalTraceProb π q.toResponse (List.ofFn w)
    rw [causalTraceProb_eq_behaviorTraceProb
        π q.toResponse q.toResponse_valid,
      CausalBehavior.ofResponse_toResponse]
  rw [hp, hq]
  refine hraw.trans_eq ?_
  rw [causalBehaviorDepthDist_eq_nativeWorldDepthDist]
  rfl

/-! ## Direct finite-horizon universality -/

/-- Deficiency values to every literal observation-only native intervention
of every depth at most `n`. -/
def causalBehaviorNativeDeficiencyValuesUpTo
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) : Set ℝ :=
  {d | ∃ m, m ≤ n ∧ ∃ σ : CausalObservationPlan A O m,
    d = finiteDeficiency E
      (CausalObservationPlan.behaviorPlanExperiment σ ps)}

noncomputable def causalBehaviorNativeDeficiencyUpTo
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) : ℝ :=
  sSup (causalBehaviorNativeDeficiencyValuesUpTo E ps n)

/-- Deficiency values to direct behavior-indexed experiments generated by
all valid randomized policies through horizon `n`. -/
def causalBehaviorPolicyDeficiencyValuesUpTo
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) : Set ℝ :=
  {d | ∃ t, t ≤ n ∧ ∃ π : CausalPolicy A O,
    IsCausalPolicy π ∧
      d = finiteDeficiency E (causalBehaviorFiniteExperiment π ps t)}

noncomputable def causalBehaviorPolicyDeficiencyUpTo
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) : ℝ :=
  sSup (causalBehaviorPolicyDeficiencyValuesUpTo E ps n)

theorem causalBehaviorNativeDeficiencyValuesUpTo_eq_raw
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorNativeDeficiencyValuesUpTo E ps n =
      causalNativeDeficiencyValuesUpTo E
        (causalBehaviorResponsePresentation ps) n := by
  ext d
  constructor
  · rintro ⟨m, hmn, σ, rfl⟩
    refine ⟨m, hmn, σ.toCausalPlan, ?_⟩
    rw [causalBehaviorObservationPlanExperiment_eq_toResponse]
  · rintro ⟨m, hmn, τ, rfl⟩
    refine ⟨m, hmn, CausalObservationPlan.ofCausalPlan τ, ?_⟩
    rw [causalBehaviorObservationPlanExperiment_ofCausalPlan_eq_toResponse]

theorem causalBehaviorPolicyDeficiencyValuesUpTo_eq_raw
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorPolicyDeficiencyValuesUpTo E ps n =
      causalPolicyDeficiencyValuesUpTo E
        (causalBehaviorResponsePresentation ps) n := by
  ext d
  constructor
  · rintro ⟨t, htn, π, hπ, rfl⟩
    refine ⟨t, htn, π, hπ, ?_⟩
    rw [causalBehaviorFiniteExperiment_eq_toResponse]
  · rintro ⟨t, htn, π, hπ, rfl⟩
    refine ⟨t, htn, π, hπ, ?_⟩
    rw [causalBehaviorFiniteExperiment_eq_toResponse]

theorem causalBehaviorNativeDeficiencyUpTo_eq_raw
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorNativeDeficiencyUpTo E ps n =
      causalNativeDeficiencyUpTo E
        (causalBehaviorResponsePresentation ps) n := by
  rw [causalBehaviorNativeDeficiencyUpTo,
    causalNativeDeficiencyUpTo,
    causalBehaviorNativeDeficiencyValuesUpTo_eq_raw]

theorem causalBehaviorPolicyDeficiencyUpTo_eq_raw
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorPolicyDeficiencyUpTo E ps n =
      causalPolicyDeficiencyUpTo E
        (causalBehaviorResponsePresentation ps) n := by
  rw [causalBehaviorPolicyDeficiencyUpTo,
    causalPolicyDeficiencyUpTo,
    causalBehaviorPolicyDeficiencyValuesUpTo_eq_raw]

/-- Finite-horizon universality on the canonical behavior carrier, with the
paper's observation-only native interventions on the left and all randomized
policy experiments on the right. -/
theorem causalBehavior_finiteHorizonUniversality
    [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorNativeDeficiencyUpTo E ps n =
      causalBehaviorPolicyDeficiencyUpTo E ps n := by
  rw [causalBehaviorNativeDeficiencyUpTo_eq_raw,
    causalBehaviorPolicyDeficiencyUpTo_eq_raw]
  exact causal_finiteHorizonUniversality E hE
    (causalBehaviorResponsePresentation ps)
    (causalBehaviorResponsePresentation_valid ps) n

/-! ## Direct process order and greatestness -/

/-- Finitary dominance between direct behavior-indexed acquired processes. -/
def CausalBehaviorFinitaryDominates
    (ps : Θ → CausalBehavior A O)
    (π ρ : ValidCausalPolicy A O) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
    finiteDeficiency
      (causalBehaviorFiniteExperiment π.1 ps t)
      (causalBehaviorFiniteExperiment ρ.1 ps n) < ε

def CausalBehaviorFinitarilyGreatest
    (ps : Θ → CausalBehavior A O)
    (π : ValidCausalPolicy A O) : Prop :=
  ∀ ρ, CausalBehaviorFinitaryDominates ps π ρ

/-- Native sufficiency stated literally with observation-only native plans and
direct behavior-indexed experiments. -/
def CausalBehaviorNativelySufficient
    (ps : Θ → CausalBehavior A O)
    (π : ValidCausalPolicy A O) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
    ∀ σ : CausalObservationPlan A O n,
      finiteDeficiency
        (causalBehaviorFiniteExperiment π.1 ps t)
        (CausalObservationPlan.behaviorPlanExperiment σ ps) < ε

theorem causalBehaviorFinitaryDominates_iff_raw [Nonempty Θ]
    (ps : Θ → CausalBehavior A O) (π ρ : ValidCausalPolicy A O) :
    CausalBehaviorFinitaryDominates ps π ρ ↔
      CausalFinitaryDominates (causalBehaviorResponsePresentation ps) π ρ := by
  unfold CausalBehaviorFinitaryDominates CausalFinitaryDominates
  simp only [causalBehaviorFiniteExperiment_eq_toResponse]

theorem causalBehaviorFinitarilyGreatest_iff_raw [Nonempty Θ]
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) :
    CausalBehaviorFinitarilyGreatest ps π ↔
      CausalFinitarilyGreatest (causalBehaviorResponsePresentation ps) π := by
  unfold CausalBehaviorFinitarilyGreatest CausalFinitarilyGreatest
  exact forall_congr' fun ρ => causalBehaviorFinitaryDominates_iff_raw ps π ρ

theorem causalBehaviorNativelySufficient_iff_raw [Nonempty Θ]
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) :
    CausalBehaviorNativelySufficient ps π ↔
      CausalNativelySufficient (causalBehaviorResponsePresentation ps) π := by
  constructor
  · intro h n ε hε
    obtain ⟨T, hT⟩ := h n ε hε
    refine ⟨T, ?_⟩
    intro t ht τ
    have hs := hT t ht (CausalObservationPlan.ofCausalPlan τ)
    rw [causalBehaviorFiniteExperiment_eq_toResponse,
      causalBehaviorObservationPlanExperiment_ofCausalPlan_eq_toResponse] at hs
    exact hs
  · intro h n ε hε
    obtain ⟨T, hT⟩ := h n ε hε
    refine ⟨T, ?_⟩
    intro t ht σ
    have hs := hT t ht σ.toCausalPlan
    rw [← causalBehaviorFiniteExperiment_eq_toResponse,
      ← causalBehaviorObservationPlanExperiment_eq_toResponse] at hs
    exact hs

theorem causalBehaviorFinitaryDominates_isPreorder [Nonempty Θ]
    (ps : Θ → CausalBehavior A O) :
    (∀ π, CausalBehaviorFinitaryDominates ps π π) ∧
      (∀ π ρ σ,
        CausalBehaviorFinitaryDominates ps π ρ →
        CausalBehaviorFinitaryDominates ps ρ σ →
        CausalBehaviorFinitaryDominates ps π σ) := by
  have hraw := causalFinitaryDominates_isPreorder
    (causalBehaviorResponsePresentation ps)
    (causalBehaviorResponsePresentation_valid ps)
  constructor
  · intro π
    exact (causalBehaviorFinitaryDominates_iff_raw ps π π).2 (hraw.1 π)
  · intro π ρ σ hπρ hρσ
    apply (causalBehaviorFinitaryDominates_iff_raw ps π σ).2
    exact hraw.2 π ρ σ
      ((causalBehaviorFinitaryDominates_iff_raw ps π ρ).1 hπρ)
      ((causalBehaviorFinitaryDominates_iff_raw ps ρ σ).1 hρσ)

theorem causalBehaviorFinitarilyGreatest_equivalent [Nonempty Θ]
    (ps : Θ → CausalBehavior A O)
    {π ρ : ValidCausalPolicy A O}
    (hπ : CausalBehaviorFinitarilyGreatest ps π)
    (hρ : CausalBehaviorFinitarilyGreatest ps ρ) :
    CausalBehaviorFinitaryDominates ps π ρ ∧
      CausalBehaviorFinitaryDominates ps ρ π :=
  ⟨hπ ρ, hρ π⟩

/-- Greatest-process characterization on the canonical behavior carrier. -/
theorem causalBehaviorNativelySufficient_iff_finitarilyGreatest [Nonempty Θ]
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) :
    CausalBehaviorNativelySufficient ps π ↔
      CausalBehaviorFinitarilyGreatest ps π := by
  rw [causalBehaviorNativelySufficient_iff_raw,
    causalBehaviorFinitarilyGreatest_iff_raw]
  exact causalNativelySufficient_iff_finitarilyGreatest
    (causalBehaviorResponsePresentation ps)
    (causalBehaviorResponsePresentation_valid ps) π

/-- With a subsingleton action alphabet there is no acquisition choice: every
valid policy is natively sufficient for every nonempty class of direct
controlled-prefix behaviors. -/
theorem causalBehaviorNativelySufficient_of_subsingleton_action
    [Nonempty Θ] [Subsingleton A]
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) :
    CausalBehaviorNativelySufficient ps π := by
  apply (causalBehaviorNativelySufficient_iff_raw ps π).2
  exact causalNativelySufficient_of_subsingleton_action
    (causalBehaviorResponsePresentation ps)
    (causalBehaviorResponsePresentation_valid ps) π

end IdExp
