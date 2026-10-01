import Formal.UniformPrefix
import Formal.MeasureDeficiencyCore
import Formal.MeasureDensity

/-!
# Uniform prefix continuity under compact domination

This module completes the dominated-`L¹` instantiation behind Proposition
`prop:l1-prefix` in `Paper/draft/main.tex`.  It proves all three layers of the
argument:

* conditional expectation on `L¹` is nonexpansive and converges uniformly on
  compact density families along a filtration generating the full sigma-algebra;
* a regular conditional continuation kernel maps a law of density `f` to the
  law of density `E[f | m]`;
* the resulting total-variation error is exactly
  `1/2 * ∫ |E[f | m] - f|`, giving the displayed directed-deficiency bound and
  convergence to zero.

The decoder is bundled as one Markov kernel shared by every world.  Thus the
formal statement controls experiment deficiency, not a collection of
world-dependent reconstructions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace IdExp

open Filter Metric Topology

theorem condExpL1CLM_lipschitz_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] :
    LipschitzWith 1 (condExpL1CLM ℝ hm μ) := by
  simpa [condExpL1CLM] using
    (L1.setToL1_lipschitz (dominatedFinMeasAdditive_condExpInd ℝ hm μ))

theorem tendsto_condExpL1CLM_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ mΩ)
    (hgenerate : (⨆ n, ℱ n) = mΩ) (f : Ω →₁[μ] ℝ) :
    Tendsto (fun n => condExpL1CLM ℝ (ℱ.le n) μ f) atTop (𝓝 f) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hmeas : StronglyMeasurable[⨆ n, ℱ n] (f : Ω → ℝ) := by
    rw [hgenerate]
    exact Lp.stronglyMeasurable f
  have hlevy := (L1.integrable_coeFn f).tendsto_eLpNorm_condExp hmeas
  convert hlevy using 1
  funext n
  apply eLpNorm_congr_ae
  have hcond := condExp_ae_eq_condExpL1CLM (ℱ.le n) (L1.integrable_coeFn f)
  rw [Integrable.toL1_coeFn] at hcond
  exact hcond.symm.sub EventuallyEq.rfl

theorem tendstoUniformlyOn_condExpL1CLM
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ mΩ)
    (hgenerate : (⨆ n, ℱ n) = mΩ)
    {K : Set (Ω →₁[μ] ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n f => condExpL1CLM ℝ (ℱ.le n) μ f) id atTop K := by
  exact tendstoUniformlyOn_id_of_nonexpansive
    (fun n f => condExpL1CLM ℝ (ℱ.le n) μ f)
    (fun n => condExpL1CLM_lipschitz_one μ (ℱ.le n))
    (tendsto_condExpL1CLM_filtration μ ℱ hgenerate) hK

theorem eventually_condExpL1CLM_uniform_on_compact
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ mΩ)
    (hgenerate : (⨆ n, ℱ n) = mΩ)
    (density : Θ → Ω →₁[μ] ℝ)
    (hcompact : IsCompact (closure (Set.range density)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ θ,
      dist (condExpL1CLM ℝ (ℱ.le n) μ (density θ)) (density θ) < ε := by
  have hunif := tendstoUniformlyOn_condExpL1CLM μ ℱ hgenerate hcompact
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  filter_upwards [hunif ε hε] with n hn θ
  simpa [dist_comm] using
    (hn (density θ) (subset_closure (Set.mem_range_self θ)))

/-- Continue a prefix law by the regular conditional law of the dominating
full-path measure. -/
noncomputable def conditionalResample
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ ν : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) : @Measure Ω mΩ :=
  (@condExpKernel Ω mΩ _ μ _ m) ∘ₘ ν.trim hm

theorem conditionalResample_self
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    conditionalResample (mΩ := mΩ) μ μ m hm = μ := by
  simpa [conditionalResample] using
    (@condExpKernel_comp_trim Ω m mΩ _ μ _ hm)

theorem conditionalResample_real_apply
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {s : Set Ω} (hs : @MeasurableSet Ω mΩ s) :
    (conditionalResample (mΩ := mΩ) μ ν m hm).real s =
      ∫ x, ((@condExpKernel Ω mΩ _ μ _ m) x).real s ∂(ν.trim hm) := by
  change ((Measure.bind (ν.trim hm)
    (fun x => (@condExpKernel Ω mΩ _ μ _ m) x) s).toReal) = _
  rw [Measure.bind_apply
    (f := fun x => (@condExpKernel Ω mΩ _ μ _ m) x) hs
    (Kernel.measurable (@condExpKernel Ω mΩ _ μ _ m)).aemeasurable]
  have hfinite : ∀ᵐ x ∂(ν.trim hm),
      (@condExpKernel Ω mΩ _ μ _ m x) s < ∞ := by
    filter_upwards with x
    exact measure_lt_top _ _
  simpa [measureReal_def] using
    (integral_toReal
      (@measurable_condExpKernel Ω m mΩ _ μ _ s hs).aemeasurable
      hfinite).symm

theorem conditionalResample_withDensity_real_apply
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (hfint : Integrable f μ)
    (hfnonneg : ∀ x, 0 ≤ f x)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {s : Set Ω} (hs : @MeasurableSet Ω mΩ s) :
    (conditionalResample (mΩ := mΩ) μ
      (μ.withDensity fun x => ENNReal.ofReal (f x)) m hm).real s =
      ∫ x, f x * ((@condExpKernel Ω mΩ _ μ _ m) x).real s ∂μ := by
  let _ : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hfint.2
  let k : Ω → ℝ := fun x => ((@condExpKernel Ω mΩ _ μ _ m) x).real s
  have hk : StronglyMeasurable[m] k :=
    (@measurable_condExpKernel Ω m mΩ _ μ _ s hs).ennreal_toReal.stronglyMeasurable
  calc
    _ = ∫ x, k x ∂((μ.withDensity fun x => ENNReal.ofReal (f x)).trim hm) := by
      simpa [k] using conditionalResample_real_apply (mΩ := mΩ) μ
        (μ.withDensity fun x => ENNReal.ofReal (f x)) m hm hs
    _ = ∫ x, k x ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) := by
      exact (integral_trim hm hk).symm
    _ = ∫ x, (ENNReal.ofReal (f x)).toReal • k x ∂μ := by
      exact @integral_withDensity_eq_integral_toReal_smul
        Ω ℝ mΩ μ _ _ (fun x => ENNReal.ofReal (f x)) (by fun_prop)
        (by filter_upwards with x; simp) k
    _ = ∫ x, f x * k x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [hfnonneg x, smul_eq_mul]
    _ = _ := rfl

theorem integral_mul_condExpKernel_eq_setIntegral_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hfint : Integrable f μ)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {s : Set Ω} (hs : @MeasurableSet Ω mΩ s) :
    ∫ x, f x * ((@condExpKernel Ω mΩ _ μ _ m) x).real s ∂μ =
      ∫ x in s, μ[f | m] x ∂μ := by
  let k : Ω → ℝ := fun x => ((@condExpKernel Ω mΩ _ μ _ m) x).real s
  let ind : Ω → ℝ := s.indicator fun _ => 1
  have hk : StronglyMeasurable[m] k :=
    (@measurable_condExpKernel Ω m mΩ _ μ _ s hs).ennreal_toReal.stronglyMeasurable
  have hkbound : ∀ x, ‖k x‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hfk : Integrable (fun x => f x * k x) μ :=
    hfint.mul_bdd (hk.mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall hkbound)
  have hgint : Integrable (μ[f | m]) μ := integrable_condExp
  have hgmeas : StronglyMeasurable[m] (μ[f | m]) := stronglyMeasurable_condExp
  have hindmeas : @StronglyMeasurable Ω ℝ _ mΩ ind := by
    exact (@Measurable.indicator Ω ℝ s (fun _ => 1) mΩ _ _
      measurable_const hs).stronglyMeasurable
  have hindbound : ∀ x, ‖ind x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [ind, hx]
  have hindint : Integrable ind μ :=
    Integrable.of_bound hindmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hindbound)
  have hgind : Integrable (fun x => μ[f | m] x * ind x) μ :=
    hgint.mul_bdd hindmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hindbound)
  have hkind : k =ᵐ[μ] μ[ind | m] := by
    simpa [k, ind] using
      (@condExpKernel_ae_eq_condExp Ω m mΩ _ μ _ hm s hs)
  calc
    _ = ∫ x, μ[fun y => f y * k y | m] x ∂μ := by
      rw [integral_condExp hm]
    _ = ∫ x, μ[f | m] x * k x ∂μ := by
      apply integral_congr_ae
      exact condExp_mul_of_stronglyMeasurable_right hk hfk hfint
    _ = ∫ x, μ[f | m] x * μ[ind | m] x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hkind] with x hx
      rw [hx]
    _ = ∫ x, μ[fun y => μ[f | m] y * ind y | m] x ∂μ := by
      apply integral_congr_ae
      exact (condExp_mul_of_stronglyMeasurable_left hgmeas hgind
        hindint).symm
    _ = ∫ x, μ[f | m] x * ind x ∂μ := by
      rw [integral_condExp hm]
    _ = ∫ x in s, μ[f | m] x ∂μ := by
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ s <;> simp [ind, hx]

theorem conditionalResample_withDensity_eq_condExpDensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (hfint : Integrable f μ)
    (hfnonneg : ∀ x, 0 ≤ f x)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    conditionalResample (mΩ := mΩ) μ
      (μ.withDensity fun x => ENNReal.ofReal (f x)) m hm =
      μ.withDensity fun x => ENNReal.ofReal (μ[f | m] x) := by
  let _ : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hfint.2
  have hgint : Integrable (μ[f | m]) μ := integrable_condExp
  let _ : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (μ[f | m] x)) :=
    isFiniteMeasure_withDensity_ofReal hgint.2
  let _ : IsFiniteMeasure (conditionalResample (mΩ := mΩ) μ
      (μ.withDensity fun x => ENNReal.ofReal (f x)) m hm) := by
    unfold conditionalResample
    infer_instance
  apply @Measure.ext Ω mΩ _ _
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (conditionalResample (mΩ := mΩ) μ
      (μ.withDensity fun x => ENNReal.ofReal (f x)) m hm).real s =
    (μ.withDensity fun x => ENNReal.ofReal (μ[f | m] x)).real s
  calc
    _ = ∫ x, f x * ((@condExpKernel Ω mΩ _ μ _ m) x).real s ∂μ :=
      conditionalResample_withDensity_real_apply (mΩ := mΩ)
        μ f hf hfint hfnonneg m hm hs
    _ = ∫ x in s, μ[f | m] x ∂μ :=
      integral_mul_condExpKernel_eq_setIntegral_condExp (mΩ := mΩ)
        μ f hfint m hm hs
    _ = _ := by
      exact (withDensity_ofReal_real_apply (mΩ := mΩ) μ (μ[f | m])
        (stronglyMeasurable_condExp.mono hm)
        (condExp_nonneg (Filter.Eventually.of_forall hfnonneg)) hs).symm

theorem condExpL1CLM_dist_eq_integral_abs
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hfint : Integrable f μ)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] :
    dist (condExpL1CLM ℝ hm μ (hfint.toL1 f)) (hfint.toL1 f) =
      ∫ x, |μ[f | m] x - f x| ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  have hcond := condExp_ae_eq_condExpL1CLM hm hfint
  filter_upwards [hcond, hfint.coeFn_toL1] with x hxcond hxf
  rw [← hxcond, hxf]
  exact Real.dist_eq (μ[f | m] x) (f x)

/-- Regular-conditional continuation, bundled as a finite measure. -/
noncomputable def conditionalResampleFinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (ν : @FiniteMeasure Ω mΩ)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) : @FiniteMeasure Ω mΩ := by
  let _ : IsFiniteMeasure ν.1 := ν.prop
  exact ⟨conditionalResample (mΩ := mΩ) μ ν.1 m hm, by
    unfold conditionalResample
    infer_instance⟩

theorem conditionalResampleFinite_withDensity_eq_condExpDensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (hfint : Integrable f μ)
    (hfnonneg : ∀ x, 0 ≤ f x)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    ((@conditionalResampleFinite Ω mΩ inferInstance μ inferInstance
      (@withDensityOfRealFinite Ω mΩ μ f hfint) m hm : @FiniteMeasure Ω mΩ) :
        @Measure Ω mΩ) =
      ((@withDensityOfRealFinite Ω mΩ μ (μ[f | m]) integrable_condExp :
        @FiniteMeasure Ω mΩ) : @Measure Ω mΩ) := by
  exact @conditionalResample_withDensity_eq_condExpDensity
    Ω mΩ inferInstance μ inferInstance f hf hfint hfnonneg m hm

theorem conditionalResampleFinite_TV_eq_half_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (hfint : Integrable f μ)
    (hfnonneg : ∀ x, 0 ≤ f x)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    @finiteMeasureTV Ω mΩ
      ((@conditionalResampleFinite Ω mΩ inferInstance μ inferInstance
        (@withDensityOfRealFinite Ω mΩ μ f hfint) m hm : @FiniteMeasure Ω mΩ) :
          @Measure Ω mΩ)
      ((@withDensityOfRealFinite Ω mΩ μ f hfint : @FiniteMeasure Ω mΩ) :
        @Measure Ω mΩ)
      inferInstance inferInstance =
      (1 / 2) * ∫ x, |μ[f | m] x - f x| ∂μ := by
  have hmeasure := @conditionalResampleFinite_withDensity_eq_condExpDensity
    Ω mΩ inferInstance μ inferInstance f hf hfint hfnonneg m hm
  calc
    _ = @finiteMeasureTV Ω mΩ
        (μ.withDensity fun x => ENNReal.ofReal (μ[f | m] x))
        (μ.withDensity fun x => ENNReal.ofReal (f x))
        (isFiniteMeasure_withDensity_ofReal integrable_condExp.2)
        (isFiniteMeasure_withDensity_ofReal hfint.2) :=
      @finiteMeasureTV_congr_left Ω mΩ
        ((@conditionalResampleFinite Ω mΩ inferInstance μ inferInstance
          (@withDensityOfRealFinite Ω mΩ μ f hfint) m hm : @FiniteMeasure Ω mΩ) :
            @Measure Ω mΩ)
        (μ.withDensity fun x => ENNReal.ofReal (μ[f | m] x))
        (μ.withDensity fun x => ENNReal.ofReal (f x))
        inferInstance (isFiniteMeasure_withDensity_ofReal integrable_condExp.2)
        (isFiniteMeasure_withDensity_ofReal hfint.2) hmeasure
    _ = _ := @finiteMeasureTV_withDensity_ofReal Ω mΩ μ
      (μ[f | m]) f (stronglyMeasurable_condExp.mono hm) hf
      integrable_condExp hfint
      (condExp_nonneg (Filter.Eventually.of_forall hfnonneg))
      (Filter.Eventually.of_forall hfnonneg)

/-- Restrict a finite measure to a smaller sigma-algebra. -/
noncomputable def trimFinite
    {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (ν : @FiniteMeasure Ω mΩ) (hm : m ≤ mΩ) : @FiniteMeasure Ω m := by
  let _ : IsFiniteMeasure ν.1 := ν.prop
  exact ⟨(ν.1).trim hm, by infer_instance⟩

/-- The regular conditional law of the full path given the prefix is one
world-independent Markov decoder from the prefix sigma-algebra to the full
one. -/
noncomputable def conditionalResampleMarkov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [hSB : StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) :
    @FiniteMarkovKernel Ω Ω m mΩ :=
  @FiniteMarkovKernel.mk Ω Ω m mΩ
    (@condExpKernel Ω mΩ hSB μ inferInstance m) (by infer_instance)

/-- The paper's displayed dominated-prefix deficiency bound. The same
regular-conditional decoder works for every world `θ`. -/
theorem dominatedPrefixDeficiency_le
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [Nonempty Θ] (μ : Measure Ω) [IsFiniteMeasure μ]
    (density : Θ → Ω → ℝ)
    (hstrong : ∀ θ, StronglyMeasurable (density θ))
    (hint : ∀ θ, Integrable (density θ) μ)
    (hnonneg : ∀ θ x, 0 ≤ density θ x)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (c : ℝ)
    (hc : ∀ θ, (1 / 2) * ∫ x,
      |μ[density θ | m] x - density θ x| ∂μ ≤ c) :
    @finiteMeasureDeficiency Θ Ω Ω m mΩ
      (fun θ => @trimFinite Ω m mΩ
        (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) hm)
      (fun θ => @withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) ≤ c := by
  apply @finiteMeasureDeficiency_le_of_decoder Θ Ω Ω m mΩ inferInstance
    (fun θ => @trimFinite Ω m mΩ
      (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) hm)
    (fun θ => @withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ))
    (@conditionalResampleMarkov Ω mΩ inferInstance μ inferInstance m) c
  intro θ
  have hdecode :
      ((@finiteMarkovDecode Ω Ω m mΩ
        (@conditionalResampleMarkov Ω mΩ inferInstance μ inferInstance m)
        (@trimFinite Ω m mΩ
          (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) hm) :
            @FiniteMeasure Ω mΩ) : @Measure Ω mΩ) =
      ((@conditionalResampleFinite Ω mΩ inferInstance μ inferInstance
        (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) m hm :
          @FiniteMeasure Ω mΩ) : @Measure Ω mΩ) := by
    rfl
  calc
    _ = @finiteMeasureTV Ω mΩ
        ((@conditionalResampleFinite Ω mΩ inferInstance μ inferInstance
          (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) m hm :
            @FiniteMeasure Ω mΩ) : @Measure Ω mΩ)
        ((@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ) :
          @FiniteMeasure Ω mΩ) : @Measure Ω mΩ)
        inferInstance inferInstance := by
      exact @finiteMeasureTV_congr_left Ω mΩ _ _ _
        inferInstance inferInstance inferInstance hdecode
    _ = (1 / 2) * ∫ x,
        |μ[density θ | m] x - density θ x| ∂μ :=
      @conditionalResampleFinite_TV_eq_half_L1 Ω mΩ inferInstance
        μ inferInstance (density θ) (hstrong θ) (hint θ) (hnonneg θ) m hm
    _ ≤ c := hc θ

/-- Literal `sup_θ` form of `dominatedPrefixDeficiency_le`. -/
theorem dominatedPrefixDeficiency_le_sSup
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [Nonempty Θ] (μ : Measure Ω) [IsFiniteMeasure μ]
    (density : Θ → Ω → ℝ)
    (hstrong : ∀ θ, StronglyMeasurable (density θ))
    (hint : ∀ θ, Integrable (density θ) μ)
    (hnonneg : ∀ θ x, 0 ≤ density θ x)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hbounded : BddAbove (Set.range fun θ =>
      (1 / 2) * ∫ x, |μ[density θ | m] x - density θ x| ∂μ)) :
    @finiteMeasureDeficiency Θ Ω Ω m mΩ
      (fun θ => @trimFinite Ω m mΩ
        (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) hm)
      (fun θ => @withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) ≤
      sSup (Set.range fun θ =>
        (1 / 2) * ∫ x, |μ[density θ | m] x - density θ x| ∂μ) := by
  refine @dominatedPrefixDeficiency_le Ω Θ mΩ inferInstance inferInstance
    μ inferInstance density hstrong hint hnonneg m hm
    (sSup (Set.range fun θ =>
      (1 / 2) * ∫ x, |μ[density θ | m] x - density θ x| ∂μ)) ?_
  intro θ
  exact le_csSup hbounded ⟨θ, rfl⟩

/-- Compactness of the `L¹` density closure supplies the boundedness premise
of `dominatedPrefixDeficiency_le_sSup`, so this is exactly the displayed
inequality under the paper's hypotheses. -/
theorem dominatedPrefixDeficiency_le_sSup_of_compact
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [Nonempty Θ] (μ : Measure Ω) [IsFiniteMeasure μ]
    (density : Θ → Ω → ℝ)
    (hstrong : ∀ θ, StronglyMeasurable (density θ))
    (hint : ∀ θ, Integrable (density θ) μ)
    (hnonneg : ∀ θ x, 0 ≤ density θ x)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hcompact : IsCompact (closure (Set.range fun θ =>
      (hint θ).toL1 (density θ)))) :
    @finiteMeasureDeficiency Θ Ω Ω m mΩ
      (fun θ => @trimFinite Ω m mΩ
        (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) hm)
      (fun θ => @withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) ≤
      sSup (Set.range fun θ =>
        (1 / 2) * ∫ x, |μ[density θ | m] x - density θ x| ∂μ) := by
  let densityL1 : Θ → Ω →₁[μ] ℝ := fun θ => (hint θ).toL1 (density θ)
  let err : (Ω →₁[μ] ℝ) → ℝ := fun f =>
    (1 / 2) * dist (condExpL1CLM ℝ hm μ f) f
  have hcont : Continuous err := by
    dsimp [err]
    fun_prop
  have himage : BddAbove (err '' closure (Set.range densityL1)) :=
    hcompact.bddAbove_image hcont.continuousOn
  have hbounded : BddAbove (Set.range fun θ =>
      (1 / 2) * ∫ x, |μ[density θ | m] x - density θ x| ∂μ) := by
    apply himage.mono
    rintro y ⟨θ, rfl⟩
    refine ⟨densityL1 θ, subset_closure (Set.mem_range_self θ), ?_⟩
    dsimp [err, densityL1]
    rw [@condExpL1CLM_dist_eq_integral_abs Ω mΩ μ (density θ)
      (hint θ) m hm inferInstance]
  exact @dominatedPrefixDeficiency_le_sSup Ω Θ mΩ inferInstance inferInstance
    μ inferInstance density hstrong hint hnonneg m hm hbounded

/-- **Uniform prefix continuity under compact domination.** If the full
sigma-algebra is generated by the increasing prefix filtration and the
density family is relatively compact in `L¹(μ)`, then the directed
deficiency from the prefix experiment to the full experiment tends to zero.
The witnessing decoder at every horizon is the same regular conditional
continuation kernel for every world. -/
theorem tendsto_dominatedPrefixDeficiency
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [Nonempty Θ] (μ : Measure Ω) [IsFiniteMeasure μ]
    (density : Θ → Ω → ℝ)
    (hstrong : ∀ θ, StronglyMeasurable (density θ))
    (hint : ∀ θ, Integrable (density θ) μ)
    (hnonneg : ∀ θ x, 0 ≤ density θ x)
    (ℱ : Filtration ℕ mΩ) (hgenerate : (⨆ n, ℱ n) = mΩ)
    (hcompact : IsCompact (closure (Set.range fun θ =>
      (hint θ).toL1 (density θ)))) :
    Tendsto
      (fun n => @finiteMeasureDeficiency Θ Ω Ω (ℱ n) mΩ
        (fun θ => @trimFinite Ω (ℱ n) mΩ
          (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) (ℱ.le n))
        (fun θ => @withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev := eventually_condExpL1CLM_uniform_on_compact
    μ ℱ hgenerate (fun θ => (hint θ).toL1 (density θ)) hcompact hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro n hnN
  have hn := hN n hnN
  let E : Θ → @FiniteMeasure Ω (ℱ n) := fun θ =>
    @trimFinite Ω (ℱ n) mΩ
      (@withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)) (ℱ.le n)
  let F : Θ → @FiniteMeasure Ω mΩ := fun θ =>
    @withDensityOfRealFinite Ω mΩ μ (density θ) (hint θ)
  let G : @FiniteMarkovKernel Ω Ω (ℱ n) mΩ :=
    @conditionalResampleMarkov Ω mΩ inferInstance μ inferInstance (ℱ n)
  have herr : ∀ θ, @finiteMeasureTV Ω mΩ
      ((@finiteMarkovDecode Ω Ω (ℱ n) mΩ G (E θ) :
        @FiniteMeasure Ω mΩ) : @Measure Ω mΩ)
      ((F θ : @FiniteMeasure Ω mΩ) : @Measure Ω mΩ)
      inferInstance inferInstance ≤ ε / 2 := by
    intro θ
    have htv : @finiteMeasureTV Ω mΩ
        ((@finiteMarkovDecode Ω Ω (ℱ n) mΩ G (E θ) :
          @FiniteMeasure Ω mΩ) : @Measure Ω mΩ)
        ((F θ : @FiniteMeasure Ω mΩ) : @Measure Ω mΩ)
        inferInstance inferInstance =
        (1 / 2) * ∫ x,
          |μ[density θ | ℱ n] x - density θ x| ∂μ := by
      exact @conditionalResampleFinite_TV_eq_half_L1 Ω mΩ inferInstance
        μ inferInstance (density θ) (hstrong θ) (hint θ) (hnonneg θ)
        (ℱ n) (ℱ.le n)
    rw [htv, ← condExpL1CLM_dist_eq_integral_abs
      μ (density θ) (hint θ) (ℱ n) (ℱ.le n)]
    exact (mul_le_mul_of_nonneg_left (le_of_lt (hn θ)) (by norm_num)).trans_eq
      (by ring)
  have hlower : 0 ≤ @finiteMeasureDeficiency Θ Ω Ω (ℱ n) mΩ E F :=
    @finiteMeasureDeficiency_nonneg_of_decoder Θ Ω Ω (ℱ n) mΩ inferInstance
      E F G (ε / 2) herr
  have hupper : @finiteMeasureDeficiency Θ Ω Ω (ℱ n) mΩ E F ≤ ε / 2 :=
    @finiteMeasureDeficiency_le_of_decoder Θ Ω Ω (ℱ n) mΩ inferInstance
      E F G (ε / 2) herr
  change dist (@finiteMeasureDeficiency Θ Ω Ω (ℱ n) mΩ E F) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlower]
  exact hupper.trans_lt (by linarith)

end IdExp
