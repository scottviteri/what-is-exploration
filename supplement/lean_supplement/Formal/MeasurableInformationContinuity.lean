import Formal.FiniteFanoBound
import Formal.MeasurableReversePinsker

/-!
# Sharp finite-output information continuity for measurable world classes

A measurable maximal coupling and the finite Fano bound give the paper's
h(r) + r log k modulus, with one entropy term rather than two. Information
is the existing posterior-density functional; no world topology or support
condition is needed here.
-/
namespace IdExp
open MeasureTheory Finset Set
noncomputable section

variable {Θ X Y : Type*} [MeasurableSpace Θ] [Fintype X] [Fintype Y]

def fanoModulus (k : ℕ) (r : ℝ) : ℝ := Real.binEntropy r + r * Real.log k

@[simp] theorem fanoModulus_zero (k : ℕ) : fanoModulus k 0 = 0 := by simp [fanoModulus]

theorem continuous_fanoModulus (k : ℕ) : Continuous (fanoModulus k) :=
  Real.binEntropy_continuous.add (continuous_id.mul continuous_const)

theorem infinitePriorInformation_mono_garbling [Nonempty X]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hm : ∀ x, Measurable (fun θ => E θ x))
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    infinitePriorInformation μ (finiteDecisionLaw E G) ≤ infinitePriorInformation μ E := by
  have h := integral_reverse_sq_le_information_gap μ E hE hm G hG
  have hn : 0 ≤ ∫ θ, (decodeErr (finiteDecisionLaw E G) E (measurableBayesReverse μ E G) θ)^2 ∂μ :=
    integral_nonneg fun θ => sq_nonneg _
  linarith

variable [DecidableEq X]

def finiteFstRule : X × Y → X → ℝ := fun z x => if z.1 = x then 1 else 0

omit [Fintype Y] in
theorem finiteFstRule_stochastic : (finiteFstRule : X × Y → X → ℝ) ∈ stochasticRules _ _ := by
  intro z _
  constructor
  · intro x; unfold finiteFstRule; split_ifs <;> norm_num
  · simp [finiteFstRule]

omit [MeasurableSpace Θ] in
theorem finiteDecisionLaw_fst (J : FiniteExperiment Θ (X × Y)) (θ : Θ) (x : X) :
    finiteDecisionLaw J finiteFstRule θ x = ∑ y, J θ (x,y) := by
  unfold finiteDecisionLaw finiteFstRule
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_ite]

def finiteSndRule : Y × X → X → ℝ := fun z x => if z.2 = x then 1 else 0

omit [Fintype Y] in
theorem finiteSndRule_stochastic : (finiteSndRule : Y × X → X → ℝ) ∈ stochasticRules _ _ := by
  intro z _
  constructor
  · intro x; unfold finiteSndRule; split_ifs <;> norm_num
  · simp [finiteSndRule]

omit [MeasurableSpace Θ] in
theorem finiteDecisionLaw_snd (J : FiniteExperiment Θ (Y × X)) (θ : Θ) (x : X) :
    finiteDecisionLaw J finiteSndRule θ x = ∑ y, J θ (y,x) := by
  unfold finiteDecisionLaw finiteSndRule
  rw [Fintype.sum_prod_type]
  simp [mul_ite]

theorem integral_finiteMismatch (μ : Measure Θ) [IsFiniteMeasure μ]
    (J : FiniteExperiment Θ (X × X)) (hJ : IsFiniteExperiment J)
    (hm : ∀ z, Measurable (fun θ => J θ z)) :
    (∫ θ, finiteMismatch (J θ) ∂μ) = finiteMismatch (priorSignalMass μ J) := by
  have hi (x y : X) : Integrable (fun θ => if x=y then (0 : ℝ) else J θ (x,y)) μ := by
    by_cases h : x=y
    · simpa only [if_pos h] using (integrable_const (0 : ℝ) : Integrable (fun _ : Θ => (0 : ℝ)) μ)
    · simpa only [if_neg h] using integrable_measurableFiniteExperiment_coordinate μ J hJ hm (x,y)
  unfold finiteMismatch
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  apply sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => hi x y)]
  apply sum_congr rfl
  intro y _
  by_cases h : x=y <;> simp [h, priorSignalMass]

/-- One-sided sharp continuity, obtained from one actual coupled experiment. -/
theorem infinitePriorInformation_sub_le_fano_pos [Nonempty X]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (E F : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ x, Measurable (fun θ => E θ x)) (hmF : ∀ x, Measurable (fun θ => F θ x))
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (hTV : ∀ θ, finiteTV (E θ) (F θ) ≤ r) :
    infinitePriorInformation μ E - infinitePriorInformation μ F ≤ fanoModulus (Fintype.card X) r := by
  let J : FiniteExperiment Θ (X × X) := fun θ => finiteMaximalCoupling (E θ) (F θ)
  have hJ : IsFiniteExperiment J := fun θ => finiteMaximalCoupling_isDist _ _ (hE θ) (hF θ)
  have hmJ : ∀ z, Measurable (fun θ => J θ z) := measurable_finiteMaximalCoupling E F hmE hmF
  have he : finiteDecisionLaw J finiteFstRule = E := by
    funext θ x
    rw [finiteDecisionLaw_fst]
    exact finiteMaximalCoupling_fst _ _ (hE θ) (hF θ) x
  have hf : ∀ θ, finiteMarginalSnd (J θ) = F θ := fun θ =>
    funext fun x => finiteMaximalCoupling_snd _ _ (hE θ) (hF θ) x
  have hmono := infinitePriorInformation_mono_garbling μ J hJ hmJ finiteFstRule finiteFstRule_stochastic
  rw [he] at hmono
  have hmass : finiteMarginalSnd (priorSignalMass μ J) = priorSignalMass μ F := by
    funext x
    unfold finiteMarginalSnd priorSignalMass
    rw [← integral_finsetSum _ (fun y _ => integrable_measurableFiniteExperiment_coordinate μ J hJ hmJ (y,x))]
    apply integral_congr_ae
    filter_upwards [] with θ
    exact congrFun (hf θ) x
  have hmis : finiteMismatch (priorSignalMass μ J) ≤ r := by
    rw [← integral_finiteMismatch μ J hJ hmJ]
    have ht : (fun θ => finiteMismatch (J θ)) = (fun θ => finiteTV (E θ) (F θ)) :=
      funext fun θ => finiteMaximalCoupling_mismatch _ _ (hE θ) (hF θ)
    rw [ht]
    have hi : Integrable (fun θ => finiteTV (E θ) (F θ)) μ := by
      apply Integrable.of_bound (measurable_finiteTV_rows E F hmE hmF).aestronglyMeasurable r
      filter_upwards [] with θ
      simpa only [Real.norm_eq_abs, abs_of_nonneg (finiteTV_nonneg _ _)] using hTV θ
    simpa using integral_mono hi (integrable_const r) hTV
  have hbound := ent_sub_marginal_le_fano_pos (priorSignalMass μ J)
    (priorSignalMass_isDist μ J hJ (integrable_measurableFiniteExperiment_coordinate μ J hJ hmJ)) r hr hrhalf hmis
  rw [hmass] at hbound
  have hrow : ∀ θ, ent (F θ) ≤ ent (J θ) := fun θ => by
    rw [← hf θ]
    exact ent_marginal_snd_le _ (hJ θ).1
  have hi := integral_mono (integrable_finiteExperiment_ent μ F hF hmF)
    (integrable_finiteExperiment_ent μ J hJ hmJ) hrow
  rw [infinitePriorInformation_eq_ent_mass_sub μ J hJ hmJ] at hmono
  rw [infinitePriorInformation_eq_ent_mass_sub μ F hF hmF]
  unfold fanoModulus
  linarith

/-- The paper's finite-output continuity modulus, for arbitrary measurable worlds. -/
theorem abs_infinitePriorInformation_sub_le_fano [Nonempty X]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (E F : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ x, Measurable (fun θ => E θ x)) (hmF : ∀ x, Measurable (fun θ => F θ x))
    (r : ℝ) (hr0 : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hTV : ∀ θ, finiteTV (E θ) (F θ) ≤ r) :
    |infinitePriorInformation μ E - infinitePriorInformation μ F| ≤ fanoModulus (Fintype.card X) r := by
  rcases eq_or_lt_of_le hr0 with hr | hr
  · have he : E = F := funext fun θ =>
      (finiteTV_eq_zero_iff _ _).mp (le_antisymm (hr ▸ hTV θ) (finiteTV_nonneg _ _))
    simp [← hr, he]
  · rw [abs_le]
    constructor
    · have h := infinitePriorInformation_sub_le_fano_pos μ F E hF hE hmF hmE r hr hrhalf
        (fun θ => by rw [finiteTV_symm]; exact hTV θ)
      linarith
    · exact infinitePriorInformation_sub_le_fano_pos μ E F hE hF hmE hmF r hr hrhalf hTV

end
end IdExp
