import Formal.FiniteProbability
import Mathlib.Probability.Martingale.Convergence

/-!
# Bayesian posteriors of finite observations

This foundation uses arbitrary measurable sample spaces, not POMDPs. The
posterior is the literal finite Bayes ratio, with zero on null observations.
Its conditional-expectation identity is proved from the observation masses.
-/

namespace IdExp

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {Θ S Ω : Type*} [Fintype Θ]

/-- Finite Bayes rule, including the null-observation convention `0 / 0 = 0`. -/
noncomputable def finiteBayesPosterior (α : Θ → ℝ) (E : Θ → S → ℝ)
    (s : S) (θ : Θ) : ℝ :=
  α θ * E θ s / ∑ c, α c * E c s

theorem finiteBayesPosterior_nonneg (α : Θ → ℝ) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s) (s : S) (θ : Θ) :
    0 ≤ finiteBayesPosterior α E s θ :=
  div_nonneg (mul_nonneg (hα θ) (hE θ s))
    (Finset.sum_nonneg fun c _ => mul_nonneg (hα c) (hE c s))

theorem finiteBayesPosterior_le_one (α : Θ → ℝ) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s) (s : S) (θ : Θ) :
    finiteBayesPosterior α E s θ ≤ 1 := by
  unfold finiteBayesPosterior
  by_cases hD : (∑ c, α c * E c s) = 0
  · simp [hD]
  · apply (div_le_one (lt_of_le_of_ne
      (Finset.sum_nonneg fun c _ => mul_nonneg (hα c) (hE c s)) (Ne.symm hD))).2
    exact Finset.single_le_sum (fun c _ => mul_nonneg (hα c) (hE c s))
      (Finset.mem_univ θ)

theorem finiteBayesPosterior_pair_le_one (α : Θ → ℝ) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s) (s : S)
    {θ η : Θ} (hne : θ ≠ η) :
    finiteBayesPosterior α E s θ + finiteBayesPosterior α E s η ≤ 1 := by
  classical
  unfold finiteBayesPosterior
  by_cases hD : (∑ c, α c * E c s) = 0
  · simp [hD]
  · rw [← add_div, div_le_one (lt_of_le_of_ne
      (Finset.sum_nonneg fun c _ => mul_nonneg (hα c) (hE c s)) (Ne.symm hD))]
    calc α θ * E θ s + α η * E η s =
        ∑ c ∈ ({θ, η} : Finset Θ), α c * E c s :=
          (Finset.sum_pair (f := fun c => α c * E c s) hne).symm
      _ ≤ ∑ c, α c * E c s := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) fun c _ _ => mul_nonneg (hα c) (hE c s)

theorem finiteBayesPosterior_mul_mass (α : Θ → ℝ) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s) (s : S) (θ : Θ) :
    finiteBayesPosterior α E s θ * (∑ c, α c * E c s) = α θ * E θ s := by
  unfold finiteBayesPosterior
  by_cases hD : (∑ c, α c * E c s) = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg fun c _ =>
      mul_nonneg (hα c) (hE c s)).1 hD θ (Finset.mem_univ θ)
    simp [hD, hz]
  · exact div_mul_cancel₀ _ hD

/-- Prior mixture mass of a finite signal. -/
def finiteBayesMass (α : Θ → ℝ) (E : Θ → S → ℝ) (s : S) : ℝ :=
  ∑ θ, α θ * E θ s

theorem finiteBayesMass_nonneg (α : Θ → ℝ) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s) (s : S) :
    0 ≤ finiteBayesMass α E s :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (hα θ) (hE θ s)

/-- A nonnull finite observation has a probability-vector posterior. -/
theorem finiteBayesPosterior_mem_simplex (α : Θ → ℝ) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s) (s : S)
    (hs : finiteBayesMass α E s ≠ 0) :
    finiteBayesPosterior α E s ∈ stdSimplex ℝ Θ := by
  refine ⟨finiteBayesPosterior_nonneg α E hα hE s, ?_⟩
  simp only [finiteBayesPosterior, ← Finset.sum_div]
  exact div_self hs

variable [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ω]

/-- Joint class/sample law for a finite prior and arbitrary sample laws. -/
noncomputable def finiteBayesJoint (α : Θ → ℝ) (μ : Θ → Measure Ω) : Measure (Θ × Ω) :=
  Measure.sum fun θ => ENNReal.ofReal (α θ) • (μ θ).map (Prod.mk θ)

theorem finiteBayesJoint_apply (α : Θ → ℝ) (μ : Θ → Measure Ω)
    {s : Set (Θ × Ω)} (hs : MeasurableSet s) :
    finiteBayesJoint α μ s = ∑ θ, ENNReal.ofReal (α θ) * μ θ (Prod.mk θ ⁻¹' s) := by
  rw [finiteBayesJoint, Measure.sum_apply _ hs, tsum_fintype]
  apply Finset.sum_congr rfl
  intro θ _
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_prodMk_left hs]

theorem isProbabilityMeasure_finiteBayesJoint {α : Θ → ℝ} (hα : IsDist α)
    (μ : Θ → Measure Ω) (hμ : ∀ θ, IsProbabilityMeasure (μ θ)) :
    IsProbabilityMeasure (finiteBayesJoint α μ) := by
  have : ∀ θ, IsProbabilityMeasure (μ θ) := hμ
  constructor
  rw [finiteBayesJoint_apply α μ MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun θ _ => hα.1 θ), hα.2, ENNReal.ofReal_one]

/-- An a.e. joint assertion is equivalent to its classwise assertions when
every prior weight is positive. This is also the bridge between the two
standard formulations of posterior concentration. -/
theorem ae_finiteBayesJoint_iff (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (hα : ∀ θ, 0 < α θ) (P : Θ × Ω → Prop) :
    (∀ᵐ x ∂finiteBayesJoint α μ, P x) ↔ ∀ θ, ∀ᵐ ω ∂μ θ, P (θ, ω) := by
  simp only [finiteBayesJoint, Measure.ae_sum_iff]
  apply forall_congr'
  intro θ
  rw [Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 (hα θ)).ne']
  exact (measurableEmbedding_prodMk_left θ).ae_map_iff

/-- Indicator of the hidden class on the joint space. -/
noncomputable def finiteBayesClassInd (θ : Θ) : Θ × Ω → ℝ :=
  (Prod.fst ⁻¹' ({θ} : Set Θ)).indicator fun _ => 1

theorem measurableSet_finiteBayesClass (θ : Θ) :
    MeasurableSet (Prod.fst ⁻¹' ({θ} : Set Θ) : Set (Θ × Ω)) :=
  measurable_fst (measurableSet_singleton θ)

theorem integrable_finiteBayesClassInd (μ : Measure (Θ × Ω)) [IsFiniteMeasure μ]
    (θ : Θ) : Integrable (finiteBayesClassInd θ) μ :=
  (integrable_const 1).indicator (measurableSet_finiteBayesClass θ)

section FiniteObservation

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

set_option warn.classDefReducibility false in
/-- Information supplied by one finite observation, on the joint space. -/
def finiteBayesObservationSigma (p : Ω → S) : MeasurableSpace (Θ × Ω) :=
  MeasurableSpace.comap (fun x => p x.2) inferInstance

theorem finiteBayesObservationSigma_le (p : Ω → S) (hp : Measurable p) :
    finiteBayesObservationSigma (Θ := Θ) p ≤
      (inferInstance : MeasurableSpace (Θ × Ω)) :=
  measurable_iff_comap_le.1 (hp.comp measurable_snd)

theorem measurable_finiteBayesObservation_comp {Y : Type*} [MeasurableSpace Y]
    (p : Ω → S) (g : S → Y) :
    Measurable[finiteBayesObservationSigma (Θ := Θ) p]
      (fun x : Θ × Ω => g (p x.2)) :=
  (measurable_of_finite g).comp (Measurable.of_comap_le le_rfl)

theorem finiteBayesJoint_atom (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (p : Ω → S) (hp : Measurable p) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s)
    (hmass : ∀ θ s, μ θ (p ⁻¹' {s}) = ENNReal.ofReal (E θ s)) (s : S) :
    finiteBayesJoint α μ ((fun x : Θ × Ω => p x.2) ⁻¹' {s}) =
      ENNReal.ofReal (∑ θ, α θ * E θ s) := by
  have hmeas : Measurable (fun x : Θ × Ω => p x.2) := hp.comp measurable_snd
  rw [finiteBayesJoint_apply α μ (hmeas (measurableSet_singleton s)),
    ENNReal.ofReal_sum_of_nonneg fun θ _ => mul_nonneg (hα θ) (hE θ s)]
  refine Finset.sum_congr rfl fun θ _ => ?_
  change ENNReal.ofReal (α θ) * μ θ (p ⁻¹' {s}) = _
  rw [hmass, ENNReal.ofReal_mul (hα θ)]

theorem finiteBayesJoint_atom_inter_class (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (p : Ω → S) (hp : Measurable p) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ)
    (hmass : ∀ θ s, μ θ (p ⁻¹' {s}) = ENNReal.ofReal (E θ s)) (s : S) (θ : Θ) :
    finiteBayesJoint α μ
      (((fun x : Θ × Ω => p x.2) ⁻¹' {s}) ∩ Prod.fst ⁻¹' {θ}) =
        ENNReal.ofReal (α θ * E θ s) := by
  classical
  have hmeas : Measurable (fun x : Θ × Ω => p x.2) := hp.comp measurable_snd
  rw [finiteBayesJoint_apply α μ
    ((hmeas (measurableSet_singleton s)).inter
      (measurableSet_finiteBayesClass θ))]
  rw [Finset.sum_eq_single θ]
  · have heq : Prod.mk θ ⁻¹'
        (((fun x : Θ × Ω => p x.2) ⁻¹' {s}) ∩ Prod.fst ⁻¹' {θ}) =
          p ⁻¹' {s} := by ext ω; simp
    rw [heq, hmass, ENNReal.ofReal_mul (hα θ)]
  · intro c _ hc
    have heq : Prod.mk c ⁻¹'
        (((fun x : Θ × Ω => p x.2) ⁻¹' {s}) ∩ Prod.fst ⁻¹' {θ}) = ∅ := by
      ext ω
      simp [hc]
    simp [heq]
  · simp

/-- Literal finite Bayes rule is a version of the conditional expectation
of the class indicator. No likelihood or posterior identity is assumed. -/
theorem finiteBayesPosterior_ae_eq_condExp (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (hα : IsDist α) (hμ : ∀ θ, IsProbabilityMeasure (μ θ))
    (p : Ω → S) (hp : Measurable p) (E : Θ → S → ℝ)
    (hE : ∀ θ s, 0 ≤ E θ s)
    (hmass : ∀ θ s, μ θ (p ⁻¹' {s}) = ENNReal.ofReal (E θ s)) (θ : Θ) :
    (fun x : Θ × Ω => finiteBayesPosterior α E (p x.2) θ)
      =ᵐ[finiteBayesJoint α μ]
      (finiteBayesJoint α μ)[finiteBayesClassInd θ | finiteBayesObservationSigma p] := by
  classical
  have := isProbabilityMeasure_finiteBayesJoint hα μ hμ
  have hind := integrable_finiteBayesClassInd (finiteBayesJoint α μ) θ
  have hmeas := measurable_finiteBayesObservation_comp (Θ := Θ) p
    (fun s => finiteBayesPosterior α E s θ)
  have hpost : Integrable (fun x : Θ × Ω => finiteBayesPosterior α E (p x.2) θ)
      (finiteBayesJoint α μ) := by
    refine Integrable.of_bound
      (hmeas.mono (finiteBayesObservationSigma_le p hp) le_rfl).aestronglyMeasurable
      1 (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (finiteBayesPosterior_nonneg α E hα.1 hE _ θ)]
    exact finiteBayesPosterior_le_one α E hα.1 hE _ θ
  refine ae_eq_condExp_of_forall_setIntegral_eq (finiteBayesObservationSigma_le p hp)
    hind (fun _ _ _ => hpost.integrableOn) (fun s hs _ => ?_)
    hmeas.stronglyMeasurable.aestronglyMeasurable
  obtain ⟨U, -, rfl⟩ := hs
  let F := U.toFinite.toFinset
  have hunion : (fun x : Θ × Ω => p x.2) ⁻¹' U =
      ⋃ s ∈ F, (fun x : Θ × Ω => p x.2) ⁻¹' {s} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff,
      F, Set.Finite.mem_toFinset]
    exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨s, hs, heq⟩ => heq ▸ hs⟩
  have hatom : ∀ s : S, MeasurableSet ((fun x : Θ × Ω => p x.2) ⁻¹' {s}) :=
    fun s => (hp.comp measurable_snd) (measurableSet_singleton s)
  rw [hunion,
    integral_biUnion_finset _ (fun s _ => hatom s)
      (fun s _ t _ hst => (Set.disjoint_singleton.mpr hst).preimage _)
      (fun s _ => hpost.integrableOn),
    integral_biUnion_finset _ (fun s _ => hatom s)
      (fun s _ t _ hst => (Set.disjoint_singleton.mpr hst).preimage _)
      (fun s _ => hind.integrableOn)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [setIntegral_congr_fun (hatom s)
    (fun x (hx : p x.2 = s) => by rw [hx]), setIntegral_const]
  rw [finiteBayesClassInd, setIntegral_indicator (measurableSet_finiteBayesClass θ),
    setIntegral_const, Measure.real, Measure.real,
    finiteBayesJoint_atom α μ p hp E hα.1 hE hmass s,
    finiteBayesJoint_atom_inter_class α μ p hp E hα.1 hmass s θ,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun c _ => mul_nonneg (hα.1 c) (hE c s)),
    ENNReal.toReal_ofReal (mul_nonneg (hα.1 θ) (hE θ s)),
    smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  exact finiteBayesPosterior_mul_mass α E hα.1 hE s θ

end FiniteObservation

end IdExp
