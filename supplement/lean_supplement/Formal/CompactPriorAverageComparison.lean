import Formal.FinitaryInformationEquality
import Formal.CompactTerminalReadiness
import Formal.CountableInformationCeiling

/-!
# Positive atoms on a compact class lift average to uniform finitary comparison

A positive prior mass at every world converts mean decoder error convergence
into pointwise convergence. Dominated convergence handles each decision task;
the existing compact decision-uniformity theorem supplies uniform deficiency.
No terminal decoder, identification, or attained greatest policy is assumed.
-/
namespace IdExp
open MeasureTheory Set Finset Filter Topology
noncomputable section
set_option linter.unusedSectionVars false

/-- A world's positive prior atom quantitatively controls its decoder error. -/
theorem atom_mul_decodeErr_le_priorAverageDecodeErr
    {Θ X Y : Type*} [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    [Fintype X] [Fintype Y] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ x, Measurable (fun θ => E θ x))
    (hmF : ∀ y, Measurable (fun θ => F θ y))
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (θ : Θ) :
    μ.real {θ} * decodeErr E F G θ ≤ priorAverageDecodeErr μ E F G := by
  have h := setIntegral_le_integral (integrable_finiteDecodeErr μ E F hE hF hmE hmF G hG)
    (Eventually.of_forall (decodeErr_nonneg E F G)) (s := {θ})
  simpa [integral_singleton, smul_eq_mul, priorAverageDecodeErr, measureReal_def] using h

/-- Compact continuous finite experiments: vanishing prior-average deficiency
implies vanishing uniform deficiency if every world has positive prior mass. -/
theorem compactDeficiency_tendsto_zero_of_priorAverage
    {Θ Y : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [T2Space Θ] [BorelSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [Fintype Y] [Nonempty Y] {Xt : ℕ → Type*} [∀ t, Fintype (Xt t)]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (hp : ∀ θ, 0 < μ.real {θ})
    (E : ∀ t, FiniteExperiment Θ (Xt t)) (F : FiniteExperiment Θ Y)
    (hE : ∀ t, IsFiniteExperiment (E t)) (hF : IsFiniteExperiment F)
    (hcE : ∀ t x, Continuous (fun θ => E t θ x))
    (hcF : ∀ y, Continuous (fun θ => F θ y))
    (hchain : ∀ s t, s ≤ t → FiniteBlackwellLE (E s) (E t))
    (ha : Tendsto (fun t => priorAverageDeficiency μ (E t) F) atTop (𝓝 0)) :
    Tendsto (fun t => finiteDeficiency (E t) F) atTop (𝓝 0) := by
  classical
  have hex (t : ℕ) := exists_decoder_le_priorAverageDeficiency_add μ (E t) F
    (show 0 < 1/((t : ℝ)+1) by positivity)
  choose G hG he using hex
  have hmean : Tendsto (fun t => priorAverageDecodeErr μ (E t) F (G t)) atTop (𝓝 0) := by
    apply squeeze_zero (fun t => priorAverageDecodeErr_nonneg μ _ _ _) he
    simpa only [add_zero] using ha.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpoint (θ : Θ) : Tendsto (fun t => decodeErr (E t) F (G t) θ) atTop (𝓝 0) := by
    apply squeeze_zero (fun t => decodeErr_nonneg _ _ _ _) (fun t => ?_)
      (show Tendsto (fun t => priorAverageDecodeErr μ (E t) F (G t) / μ.real {θ})
        atTop (𝓝 0) by simpa using hmean.div_const (μ.real {θ}))
    apply (le_div_iff₀ (hp θ)).mpr
    simpa only [mul_comm] using atom_mul_decodeErr_le_priorAverageDecodeErr μ (E t) F
      (hE t) hF (fun x => (hcE t x).measurable) (fun y => (hcF y).measurable) (G t) (hG t) θ
  apply compactDeficiency_tendsto_zero_of_pointwise_readiness E F hE hF hcE hcF hchain
  intro ν
  let B := fun t => finiteDecisionLaw (E t) (G t)
  have hcB t : ∀ y, Continuous (fun θ => B t θ y) := by
    intro y
    dsimp [B, finiteDecisionLaw]
    fun_prop
  have hlim : Tendsto (fun t => ∫ z : CompactDecisionParameter Θ Y,
      decodeErr (E t) F (G t) z.1 ∂(ν : Measure _)) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence (μ := (ν : Measure _))
      (F := fun t (z : CompactDecisionParameter Θ Y) => decodeErr (E t) F (G t) z.1)
      (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun t => ((measurable_finiteDecodeErr (E t) F
        (fun x => (hcE t x).measurable) (fun y => (hcF y).measurable) (G t)).comp
        measurable_fst).aestronglyMeasurable)
      (integrable_const 1)
      (fun t => Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (decodeErr_nonneg _ _ _ _)] using
          decodeErr_le_one (E t) F (hE t) hF (G t) (hG t) z.1))
      (Eventually.of_forall (fun z => hpoint z.1))
    simpa using hd
  apply squeeze_zero (fun t => le_max_right _ _) (fun t => ?_)
    (show Tendsto (fun t => 2 * ∫ z : CompactDecisionParameter Θ Y,
      decodeErr (E t) F (G t) z.1 ∂(ν : Measure _)) atTop (𝓝 0) by
        simpa using hlim.const_mul 2)
  have hi y : Integrable (fun z : CompactDecisionParameter Θ Y => |F z.1 y - B t z.1 y|)
      (ν : Measure _) := by
    have hc : Continuous (fun z : CompactDecisionParameter Θ Y => |F z.1 y - B t z.1 y|) := by
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq : (∑ y, ∫ z : CompactDecisionParameter Θ Y, |F z.1 y - B t z.1 y| ∂(ν : Measure _)) =
      2 * ∫ z : CompactDecisionParameter Θ Y, decodeErr (E t) F (G t) z.1 ∂(ν : Measure _) := by
    rw [← integral_finsetSum _ (fun y _ => hi y), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    dsimp [B, decodeErr, finiteDecisionLaw]
    simp_rw [abs_sub_comm]
    ring
  have hdpi := compactDecisionValue_mono_of_finiteBlackwellLE (E t) (B t) (hcE t)
    ⟨G t, hG t, rfl⟩ ν
  have hg := compactDecisionValue_sub_le_integral_l1 F (B t) hcF (hcB t) ν
  rw [heq] at hg
  apply max_le
  · linarith
  · exact mul_nonneg (by norm_num) (integral_nonneg (fun _ => decodeErr_nonneg _ _ _ _))

namespace MeasurableFiniteProcess
variable {Θ P : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
  [T2Space Θ] [BorelSpace Θ] [CompactSpace Θ] [Nonempty Θ]
  {S : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
  (M : MeasurableFiniteProcess Θ P S) (μ : Measure Θ) [IsProbabilityMeasure μ]
  (hp : ∀ θ, 0 < μ.real {θ})
  (hc : ∀ π n x, Continuous (fun θ => M.experiment π n θ x))

include hp hc in
/-- On a compact positive-atom class, the two actual finitary orders coincide. -/
theorem averageDominates_iff_uniform_of_compact_atoms (π ρ : P) :
    M.AverageDominates μ π ρ ↔ M.UniformDominates π ρ := by
  constructor
  · intro ha n ε hε
    have hlim : Tendsto (fun t => priorAverageDeficiency μ (M.experiment π t) (M.experiment ρ n))
        atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.2
      intro η hη
      obtain ⟨T, hT⟩ := ha n η hη
      filter_upwards [eventually_ge_atTop T] with t ht
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (priorAverageDeficiency_nonneg μ _ _)]
      exact hT t ht
    have hu := compactDeficiency_tendsto_zero_of_priorAverage μ hp _ _
      (M.valid π) (M.valid ρ n) (hc π) (hc ρ n) (M.refines π) hlim
    exact eventually_atTop.mp ((tendsto_order.mp hu).2 ε hε)
  · exact M.averageDominates_of_uniform μ

include hp hc in
/-- Finite complete information is strictly monotone for this compact class. -/
theorem completeInformation_strictlyMonotone_of_compact_atoms
    (hb : ∀ π, M.InformationBounded μ π) :
    IsStrictlyFinitaryMonotone M.indexed indexedFiniteDeficiency (M.completeInformation μ) := by
  apply (M.completeInformation_strictlyFinitaryMonotone_iff μ hb).mpr
  intro π ρ _ ha
  exact (M.averageDominates_iff_uniform_of_compact_atoms μ hp hc ρ π).mp ha

include hp in
/-- Finite atomic prior entropy supplies the finite-information premise. -/
theorem informationBounded_of_atomic_entropy
    (hi : Integrable (fun θ => -Real.log (μ.real {θ})) μ) (π : P) :
    M.InformationBounded μ π := by
  refine ⟨∫ θ, -Real.log (μ.real {θ}) ∂μ, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact information_le_atomic_entropy μ hp hi _ (M.valid π n) (M.measurable π n)

end MeasurableFiniteProcess
end
end IdExp
