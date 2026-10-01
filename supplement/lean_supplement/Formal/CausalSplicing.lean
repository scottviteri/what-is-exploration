import Formal.CausalUniversality

/-!
# The causal per-episode splicing identity

For a fixed native plan, consistency and an observation word determine one
full trace.  Its behavior probability is the product of the behavior action
propensities times the native observation law.  In particular, uniform
behavior makes the weight constant, so conditioning on a match does not tilt
the target law.  This is `lem:splice` of the causal-first paper.
-/

open MeasureTheory ProbabilityTheory Finset Set

set_option linter.unusedSectionVars false

namespace IdExp

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A]

/-- The behavior propensity along the unique plan-compatible trace. -/
noncomputable def causalSpliceWeight (π : CausalPolicy A O) {n : ℕ}
    (τ : CausalPlan A O n) (o : CausalObservationTrace O n) : ℝ :=
  causalPolicyProb π (List.ofFn (causalTraceOfObservations τ o))

theorem causalSpliceWeight_eq_prod (π : CausalPolicy A O) {n : ℕ}
    (τ : CausalPlan A O n) (o : CausalObservationTrace O n) :
    causalSpliceWeight π τ o =
      ∏ k : Fin n, π (causalTracePrefix (causalTraceOfObservations τ o) k)
        (τ (causalTraceDecisionPoint (causalTraceOfObservations τ o) k)) := by
  rw [causalSpliceWeight, causalPolicyProb_ofFn]
  apply Finset.prod_congr rfl
  intro k _
  rw [causalPlanAgreesTrace_traceOfObservations τ o k]

/-- Native observation likelihood contains exactly the controlled response
factors, since all prescribed action factors are one. -/
theorem causalPlanObservationExperiment_eq_responseProb
    {n : ℕ} (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O)
    (θ : Θ) (o : CausalObservationTrace O n) :
    causalPlanObservationExperiment n τ Qs θ o =
      causalResponseProb (Qs θ) (List.ofFn (causalTraceOfObservations τ o)) := by
  rw [causalPlanObservationExperiment_eq_reconstruction,
    causalFiniteExperiment, causalTraceProb_factor, causalPolicyProb_plan_eq_indicator]
  simp [causalPlanTraceIndicator, causalPlanAgreesTrace_traceOfObservations]

/-- The mass of matching transcripts with the specified observation word. -/
noncomputable def causalSpliceMass (π : CausalPolicy A O)
    (Qs : Θ → CausalResponse A O) {n : ℕ} (τ : CausalPlan A O n)
    (θ : Θ) (o : CausalObservationTrace O n) : ℝ := by
  classical
  exact ∑ w : CausalFiniteTrace A O n,
    if CausalPlanAgreesTrace τ w ∧ causalTraceObservations w = o then
      causalFiniteExperiment π Qs n θ w else 0

theorem causalSpliceMass_eq_reconstruction (π : CausalPolicy A O)
    (Qs : Θ → CausalResponse A O) {n : ℕ} (τ : CausalPlan A O n)
    (θ : Θ) (o : CausalObservationTrace O n) :
    causalSpliceMass π Qs τ θ o =
      causalFiniteExperiment π Qs n θ (causalTraceOfObservations τ o) := by
  classical
  unfold causalSpliceMass
  simp_rw [← eq_causalTraceOfObservations_iff]
  simp

/-- The displayed causal splicing identity, for arbitrary history-dependent
behavior and response kernels and any (possibly infinite) world class. -/
theorem causalSpliceMass_eq_weight_mul_target (π : CausalPolicy A O)
    (Qs : Θ → CausalResponse A O) {n : ℕ} (τ : CausalPlan A O n)
    (θ : Θ) (o : CausalObservationTrace O n) :
    causalSpliceMass π Qs τ θ o =
      causalSpliceWeight π τ o * causalPlanObservationExperiment n τ Qs θ o := by
  rw [causalSpliceMass_eq_reconstruction, causalPlanObservationExperiment_eq_responseProb]
  exact causalTraceProb_factor π (Qs θ) _

/-- The path event used in the paper, before discarding the unused suffix. -/
def causalSpliceEvent {n : ℕ} (τ : CausalPlan A O n)
    (o : CausalObservationTrace O n) : Set (CausalTraj A O) :=
  {ω | CausalPlanAgreesTrace τ (fun k : Fin n => ω k.val) ∧
    causalTraceObservations (fun k : Fin n => ω k.val) = o}

theorem causalSpliceEvent_eq_cyl
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    {n : ℕ} (τ : CausalPlan A O n)
    (o : CausalObservationTrace O n) :
    causalSpliceEvent τ o = causalCyl (List.ofFn (causalTraceOfObservations τ o)) := by
  ext ω
  rw [mem_causalCyl_ofFn]
  change (CausalPlanAgreesTrace τ (fun k : Fin n => ω k.val) ∧
    causalTraceObservations (fun k : Fin n => ω k.val) = o) ↔ _
  rw [← eq_causalTraceOfObservations_iff, funext_iff]

/-- The full path-law event has the same mass as the finite transcript
calculation; observations after the requested depth introduce no factors. -/
theorem causalSpliceEvent_measure
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (μ : Θ → Measure (CausalTraj A O))
    (hμ : ∀ θ, IsCausalPathLaw π (Qs θ) (μ θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) (o : CausalObservationTrace O n) :
    μ θ (causalSpliceEvent τ o) = ENNReal.ofReal
      (causalSpliceWeight π τ o * causalPlanObservationExperiment n τ Qs θ o) := by
  rw [causalSpliceEvent_eq_cyl, (hμ θ).cylinder,
    causalTraceProb_factor, causalPlanObservationExperiment_eq_responseProb]
  rfl

/-- Uniform behavior over the primitive action alphabet. -/
noncomputable def causalUniformPolicy (A O : Type*) [Fintype A] : CausalPolicy A O :=
  fun _ _ => (Fintype.card A : ℝ)⁻¹

theorem isCausalPolicy_uniform :
    IsCausalPolicy (causalUniformPolicy A O) := by
  intro h
  constructor
  · intro a
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · simp [causalUniformPolicy, Fintype.card_ne_zero]

theorem causalSpliceWeight_uniform {n : ℕ} (τ : CausalPlan A O n)
    (o : CausalObservationTrace O n) :
    causalSpliceWeight (causalUniformPolicy A O) τ o = (Fintype.card A : ℝ)⁻¹ ^ n := by
  rw [causalSpliceWeight_eq_prod]
  simp [causalUniformPolicy]

/-- A constant match propensity has the same total probability in every
world.  This also applies to any nonuniform policy with a constant propensity
for the particular target, not just to uniform behavior. -/
theorem sum_causalSpliceMass_eq_of_constant
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (p : ℝ)
    (hp : ∀ o, causalSpliceWeight π τ o = p) (θ : Θ) :
    ∑ o, causalSpliceMass π Qs τ θ o = p := by
  simp_rw [causalSpliceMass_eq_weight_mul_target, hp]
  rw [← Finset.mul_sum, (causalPlanObservationExperiment_valid n τ Qs hQ θ).2, mul_one]

/-- The conditional observation row is exactly the native law whenever the
constant propensity is positive.  The denominator is the actual total match
mass, so no conditional-law assumption is hidden in this statement. -/
theorem causalSplice_conditional_eq_of_constant
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (p : ℝ) (hp0 : 0 < p)
    (hp : ∀ o, causalSpliceWeight π τ o = p)
    (θ : Θ) (o : CausalObservationTrace O n) :
    causalSpliceMass π Qs τ θ o / (∑ y, causalSpliceMass π Qs τ θ y) =
      causalPlanObservationExperiment n τ Qs θ o := by
  rw [sum_causalSpliceMass_eq_of_constant π Qs hQ τ p hp θ,
    causalSpliceMass_eq_weight_mul_target, hp]
  exact mul_div_cancel_left₀ _ (ne_of_gt hp0)

/-- Uniform behavior has exact match probability `|A|^{-n}`. -/
theorem sum_causalSpliceMass_uniform
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) :
    ∑ o, causalSpliceMass (causalUniformPolicy A O) Qs τ θ o =
      (Fintype.card A : ℝ)⁻¹ ^ n :=
  sum_causalSpliceMass_eq_of_constant _ Qs hQ τ _ (causalSpliceWeight_uniform τ) θ

theorem causalSplice_conditional_uniform
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) (o : CausalObservationTrace O n) :
    causalSpliceMass (causalUniformPolicy A O) Qs τ θ o /
        (∑ y, causalSpliceMass (causalUniformPolicy A O) Qs τ θ y) =
      causalPlanObservationExperiment n τ Qs θ o := by
  apply causalSplice_conditional_eq_of_constant _ Qs hQ τ
    ((Fintype.card A : ℝ)⁻¹ ^ n) _ (causalSpliceWeight_uniform τ) θ o
  exact pow_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) n

end IdExp
