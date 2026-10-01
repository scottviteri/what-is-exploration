/-
Bhattacharyya affinity vanishes exactly at mutual singularity.

This model-independent module defines
`bhatt μ ν = ∫⁻ (dμ/dλ · dν/dλ)^{1/2} dλ` with `λ = μ + ν` and
`hellingerSq = 1 - bhatt`. This supports the worst-pair terminal separation
criterion in the full reader (`thm:finite-objectives`), not the selected
sequential posterior-movement reward in `PosteriorMovement.lean`.
The value-one/singularity characterization is proved as
`bhatt μ ν = 0 ↔ μ ⟂ₘ ν`
(`bhatt_eq_zero_iff`) plus the ENNReal triviality `1 - b = 1 ↔ b = 0`.
No probability-measure hypothesis is needed for either half; finiteness is
used only to get the Lebesgue decomposition instances.
-/
import Formal.FiniteProbability

namespace IdExp

open MeasureTheory Filter
open scoped ENNReal

/-- Bhattacharyya affinity `∫ √(dP dQ)` via Radon–Nikodym derivatives w.r.t.
the dominating measure `P + Q`. -/
noncomputable def bhatt {X : Type*} [MeasurableSpace X] (μ ν : Measure X) :
    ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1/2 : ℝ) ∂(μ + ν)

/-- `1 − ∫ √(dP dQ)`, valued in `ℝ≥0∞` with truncated subtraction.
For probability measures this is normalized squared Hellinger distance,
half the sum/integral of squared square-root differences. The definition on
arbitrary finite measures is not their usual squared Hellinger distance. -/
noncomputable def hellingerSq {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) : ℝ≥0∞ :=
  1 - bhatt μ ν

/-- Worst-pair squared Hellinger separation of any experiment, independent
of a POMDP or trajectory encoding. For a singleton class the empty infimum is
infinite, so the value-one characterization below requires two worlds. -/
noncomputable def worstPairHellinger {Θ X : Type*} [MeasurableSpace X]
    (μfam : Θ → Measure X) : ℝ≥0∞ :=
  ⨅ (θ : Θ) (θ' : Θ) (_ : θ ≠ θ'), hellingerSq (μfam θ) (μfam θ')

theorem one_sub_eq_one_iff {b : ℝ≥0∞} : 1 - b = 1 ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have hlt := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hb
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · rintro rfl
    simp

variable {X : Type*} [MeasurableSpace X]

theorem measurable_bhatt_integrand (μ ν : Measure X) :
    Measurable fun x =>
      (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ) :=
  ((Measure.measurable_rnDeriv _ _).mul (Measure.measurable_rnDeriv _ _)).pow_const _

/-- `bhatt = 0` iff the product of the two densities vanishes a.e. -/
theorem bhatt_eq_zero_iff_ae (μ ν : Measure X) :
    bhatt μ ν = 0 ↔
      ∀ᵐ x ∂(μ + ν), μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x = 0 := by
  unfold bhatt
  rw [lintegral_eq_zero_iff (measurable_bhatt_integrand μ ν)]
  constructor
  · intro h
    filter_upwards [h] with x hx
    have hx' : (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ) = 0 := by
      simpa using hx
    rcases ENNReal.rpow_eq_zero_iff.1 hx' with ⟨h0, _⟩ | ⟨_, hneg⟩
    · exact h0
    · norm_num at hneg
  · intro h
    filter_upwards [h] with x hx
    show (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ) = (0 : X → ℝ≥0∞) x
    rw [hx, Pi.zero_apply]
    exact ENNReal.zero_rpow_of_pos (by norm_num)

/-- The set-integral of a density recovers the measure. -/
theorem measure_eq_setLIntegral_rnDeriv (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {S : Set X} (hS : MeasurableSet S) :
    μ S = ∫⁻ x in S, μ.rnDeriv (μ + ν) x ∂(μ + ν) := by
  have hμ : μ ≪ μ + ν :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ (μ + ν) hμ]
  exact withDensity_apply _ hS

theorem bhatt_eq_zero_iff (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    bhatt μ ν = 0 ↔ μ ⟂ₘ ν := by
  have hf := Measure.measurable_rnDeriv μ (μ + ν)
  have hg := Measure.measurable_rnDeriv ν (μ + ν)
  have hcomm : ν + μ = μ + ν := add_comm _ _
  -- both densities are taken w.r.t. the same `μ + ν`; `ν`'s uses `ν + μ` in the
  -- generic lemma, so rewrite once.
  have hνS : ∀ {S : Set X}, MeasurableSet S →
      ν S = ∫⁻ x in S, ν.rnDeriv (μ + ν) x ∂(μ + ν) := by
    intro S hS
    have := measure_eq_setLIntegral_rnDeriv ν μ hS
    rwa [hcomm] at this
  rw [bhatt_eq_zero_iff_ae]
  constructor
  · intro h
    set S : Set X := {x | μ.rnDeriv (μ + ν) x = 0} with hSdef
    have hS : MeasurableSet S := hf (measurableSet_singleton 0)
    refine ⟨S, hS, ?_, ?_⟩
    · rw [measure_eq_setLIntegral_rnDeriv μ ν hS, lintegral_eq_zero_iff hf,
        Filter.EventuallyEq, ae_restrict_iff' hS]
      exact Eventually.of_forall fun x hx => hx
    · rw [hνS hS.compl, lintegral_eq_zero_iff hg, Filter.EventuallyEq,
        ae_restrict_iff' hS.compl]
      filter_upwards [h] with x hx hxS
      rcases mul_eq_zero.1 hx with h0 | h0
      · exact absurd h0 hxS
      · exact h0
  · rintro ⟨S, hS, hμS, hνSc⟩
    have h1 : ∀ᵐ x ∂(μ + ν), x ∈ S → μ.rnDeriv (μ + ν) x = 0 := by
      rw [measure_eq_setLIntegral_rnDeriv μ ν hS, lintegral_eq_zero_iff hf,
        Filter.EventuallyEq, ae_restrict_iff' hS] at hμS
      exact hμS
    have h2 : ∀ᵐ x ∂(μ + ν), x ∈ Sᶜ → ν.rnDeriv (μ + ν) x = 0 := by
      rw [hνS hS.compl, lintegral_eq_zero_iff hg, Filter.EventuallyEq,
        ae_restrict_iff' hS.compl] at hνSc
      exact hνSc
    filter_upwards [h1, h2] with x hx1 hx2
    by_cases hxS : x ∈ S
    · rw [hx1 hxS, zero_mul]
    · rw [hx2 hxS, mul_zero]

/-- Squared Hellinger distance is one exactly at mutual singularity. -/
theorem hellingerSq_eq_one_iff (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    hellingerSq μ ν = 1 ↔ μ ⟂ₘ ν := by
  unfold hellingerSq
  exact one_sub_eq_one_iff.trans (bhatt_eq_zero_iff μ ν)

theorem worstPairHellinger_le_one {Θ : Type*} [Nontrivial Θ]
    (E : Θ → Measure X) : worstPairHellinger E ≤ 1 := by
  obtain ⟨θ, η, hne⟩ := exists_pair_ne Θ
  exact iInf_le_of_le θ (iInf_le_of_le η
    (iInf_le_of_le hne (show hellingerSq (E θ) (E η) ≤ 1 from tsub_le_self)))

/-- The value-one criterion does not require a finite world class. -/
theorem worstPairHellinger_eq_one_iff_pairwise_mutuallySingular
    {Θ : Type*} [Nontrivial Θ] (E : Θ → Measure X)
    (hE : ∀ θ, IsProbabilityMeasure (E θ)) :
    worstPairHellinger E = 1 ↔ Pairwise fun θ η => E θ ⟂ₘ E η := by
  constructor
  · intro h θ η hne
    have := hE θ
    have := hE η
    apply (hellingerSq_eq_one_iff _ _).1
    apply le_antisymm tsub_le_self
    calc
      1 = worstPairHellinger E := h.symm
      _ ≤ hellingerSq (E θ) (E η) :=
        iInf_le_of_le θ (iInf_le_of_le η (iInf_le _ hne))
  · intro h
    apply le_antisymm (worstPairHellinger_le_one E)
    refine le_iInf fun θ => le_iInf fun η => le_iInf fun hne => ?_
    have := hE θ
    have := hE η
    exact ((hellingerSq_eq_one_iff _ _).2 (h hne)).ge

end IdExp
