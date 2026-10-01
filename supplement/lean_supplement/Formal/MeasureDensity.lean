import Formal.MeasureTotalVariation

/-!
# Real densities and total variation

Finite density measures and the L¹ formula for TV. These facts are shared by
finite row experiments and compact-dominated prefix continuity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace IdExp

theorem withDensity_ofReal_real_apply
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : StronglyMeasurable f)
    (hfnonneg : 0 ≤ᵐ[μ] f)
    {s : Set Ω} (hs : @MeasurableSet Ω mΩ s) :
    (μ.withDensity fun x => ENNReal.ofReal (f x)).real s =
      ∫ x in s, f x ∂μ := by
  calc
    _ = ∫ _ in s, (1 : ℝ) ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) :=
      setIntegral_one_eq_measureReal.symm
    _ = ∫ x in s, (ENNReal.ofReal (f x)).toReal • (1 : ℝ) ∂μ := by
      exact @setIntegral_withDensity_eq_setIntegral_toReal_smul
        Ω ℝ mΩ μ _ _ (fun x => ENNReal.ofReal (f x)) s (by fun_prop)
        (by filter_upwards with x; simp) (fun _ => (1 : ℝ)) hs
    _ = ∫ x in s, f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hfnonneg] with x hx
      have hx' : 0 ≤ f x := by simpa using hx
      simp [hx']

theorem toSignedMeasure_withDensity_ofReal_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : StronglyMeasurable f)
    (hfint : Integrable f μ) (hfnonneg : 0 ≤ᵐ[μ] f) :
    @Measure.toSignedMeasure Ω mΩ
      (μ.withDensity fun x => ENNReal.ofReal (f x))
      (isFiniteMeasure_withDensity_ofReal hfint.2) = μ.withDensityᵥ f := by
  let _ : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hfint.2
  ext s hs
  rw [Measure.toSignedMeasure_apply_measurable hs,
    withDensityᵥ_apply hfint hs,
    withDensity_ofReal_real_apply (mΩ := mΩ) μ f hf hfnonneg hs]

theorem finiteMeasureTV_withDensity_ofReal
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfint : Integrable f μ) (hgint : Integrable g μ)
    (hfnonneg : 0 ≤ᵐ[μ] f) (hgnonneg : 0 ≤ᵐ[μ] g) :
    @finiteMeasureTV Ω mΩ
      (μ.withDensity fun x => ENNReal.ofReal (f x))
      (μ.withDensity fun x => ENNReal.ofReal (g x))
      (isFiniteMeasure_withDensity_ofReal hfint.2)
      (isFiniteMeasure_withDensity_ofReal hgint.2) =
      (1 / 2) * ∫ x, |f x - g x| ∂μ := by
  have hsigned :
      (@Measure.toSignedMeasure Ω mΩ
        (μ.withDensity fun x => ENNReal.ofReal (f x))
        (isFiniteMeasure_withDensity_ofReal hfint.2) -
       @Measure.toSignedMeasure Ω mΩ
        (μ.withDensity fun x => ENNReal.ofReal (g x))
        (isFiniteMeasure_withDensity_ofReal hgint.2)) =
        μ.withDensityᵥ (fun x => f x - g x) := by
    rw [toSignedMeasure_withDensity_ofReal_eq μ f hf hfint hfnonneg,
      toSignedMeasure_withDensity_ofReal_eq μ g hg hgint hgnonneg]
    exact (withDensityᵥ_sub' hfint hgint).symm
  have hdiff : Integrable (fun x => f x - g x) μ := by
    exact (hfint.sub hgint).congr (Filter.Eventually.of_forall fun _ => rfl)
  unfold finiteMeasureTV
  rw [hsigned, SignedMeasure.totalVariation_eq_variation,
    Measure.variation_withDensityᵥ hdiff]
  congr 1
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hnorm_nonneg : 0 ≤ ∫ x, ‖f x - g x‖ ∂μ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [← ofReal_integral_norm_eq_lintegral_enorm hdiff,
    ENNReal.toReal_ofReal hnorm_nonneg]
  apply integral_congr_ae
  filter_upwards with x
  exact Real.norm_eq_abs (f x - g x)

/-- The finite measure having density `f` with respect to `μ`. -/
noncomputable def withDensityOfRealFinite
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hfint : Integrable f μ) : FiniteMeasure Ω :=
  ⟨μ.withDensity fun x => ENNReal.ofReal (f x),
    isFiniteMeasure_withDensity_ofReal hfint.2⟩

end IdExp
