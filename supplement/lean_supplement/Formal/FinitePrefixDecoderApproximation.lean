import Formal.DominatedPrefix
import Formal.BlackwellConverse
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Finite-prefix approximation of a terminal randomized decoder

For each fixed probability law, conditional expectation approximates every
finite-output terminal decoder in L1 along a generating finite-signal
filtration. The approximants are actual stochastic matrices, including on
null prefix cells. No finite or countable world-class assumption is used.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology Finset Set
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Ω Y : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype Y] [Nonempty Y]

/-- Conditioning a probability vector preserves its simplex constraints a.e. -/
theorem ae_isDist_condExp_decoder (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : Ω → Y → ℝ) (hG : ∀ ω, IsDist (G ω))
    (hGm : ∀ y, Measurable (fun ω => G ω y))
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    ∀ᵐ ω ∂μ, IsDist (fun y => μ[fun z => G z y | m] ω) := by
  let : MeasurableSpace Ω := mΩ
  have hint y : Integrable (fun ω => G ω y) μ := by
    apply Integrable.of_bound (μ := μ) (hGm y).aestronglyMeasurable 1
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((hG ω).1 y)]
    exact ((Finset.single_le_sum (fun z _ => (hG ω).1 z)
      (Finset.mem_univ y)).trans_eq (hG ω).2)
  have hn : ∀ y, 0 ≤ᵐ[μ] μ[fun z => G z y | m] :=
    fun y => condExp_nonneg (Eventually.of_forall fun ω => (hG ω).1 y)
  have hs := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset Y))
    (f := fun y ω => G ω y) (fun y _ => hint y) m
  have heq : (∑ y, fun ω => G ω y) = fun _ => (1 : ℝ) := by
    funext ω
    simpa using (hG ω).2
  rw [heq, condExp_const hm] at hs
  filter_upwards [ae_all_iff.2 hn, hs] with ω hω hsum
  exact ⟨hω, by simpa only [Finset.sum_apply] using hsum.symm⟩

/-- A finite-signal conditional mean is represented by a stochastic matrix.
Null cells use a fixed uniform distribution rather than an invalid zero row. -/
theorem exists_stochasticRule_condExp_decoder
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (q : Ω → X) (hq : Measurable q)
    (G : Ω → Y → ℝ) (hG : ∀ ω, IsDist (G ω))
    (hGm : ∀ y, Measurable (fun ω => G ω y)) :
    ∃ H ∈ stochasticRules X Y,
      ∀ y, (fun ω => H (q ω) y) =ᵐ[μ]
        μ[fun ω => G ω y | MeasurableSpace.comap q inferInstance] := by
  classical
  let m := MeasurableSpace.comap q inferInstance
  let : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := measurable_iff_comap_le.1 hq
  have hf y : ∃ g : X → ℝ, StronglyMeasurable g ∧
      μ[fun ω => G ω y | m] = g ∘ q :=
    (stronglyMeasurable_condExp (μ := μ) (m := m)
      (f := fun ω => G ω y)).exists_eq_measurable_comp
  choose g hgm hfactor using hf
  let r : X → Y → ℝ := fun x y => g y x
  let H : X → Y → ℝ := fun x => if IsDist (r x) then r x else uniformPrior Y
  refine ⟨H, fun x _ => ?_, ?_⟩
  · dsimp only [H]
    split_ifs with h
    · exact h
    · exact isDist_uniformPrior
  · intro y
    filter_upwards [ae_isDist_condExp_decoder μ G hG hGm m hm] with ω hω
    have hrow : r (q ω) = fun y => μ[fun z => G z y | m] ω := by
      funext y
      simpa only [r, Function.comp_apply] using (congrFun (hfactor y) ω).symm
    have hvalid : IsDist (r (q ω)) := hrow.symm ▸ hω
    change H (q ω) y = _
    simp only [H, if_pos hvalid, hrow, m]

/-- Every finite-output terminal decoder admits valid prefix matrices with
vanishing integrated coordinate error under a fixed finite path law. -/
theorem exists_finitePrefix_decoder_L1
    {Xt : ℕ → Type*} [∀ t, Fintype (Xt t)]
    [∀ t, MeasurableSpace (Xt t)] [∀ t, MeasurableSingletonClass (Xt t)]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : ∀ t, Ω → Xt t) (hq : ∀ t, Measurable (q t))
    (ℱ : Filtration ℕ mΩ)
    (hℱ : ∀ t, ℱ t = MeasurableSpace.comap (q t) inferInstance)
    (hgenerate : (⨆ t, ℱ t) = mΩ)
    (G : Ω → Y → ℝ) (hG : ∀ ω, IsDist (G ω))
    (hGm : ∀ y, Measurable (fun ω => G ω y)) :
    ∃ H : ∀ t, Xt t → Y → ℝ,
      (∀ t, H t ∈ stochasticRules (Xt t) Y) ∧
      Tendsto (fun t => ∑ y, ∫ ω, |H t (q t ω) y - G ω y| ∂μ)
        atTop (𝓝 0) := by
  choose H hH heq using fun t =>
    exists_stochasticRule_condExp_decoder μ (q t) (hq t) G hG hGm
  refine ⟨H, hH, ?_⟩
  have hint y : Integrable (fun ω => G ω y) μ := by
    apply Integrable.of_bound (μ := μ) (hGm y).aestronglyMeasurable 1
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((hG ω).1 y)]
    exact ((Finset.single_le_sum (fun z _ => (hG ω).1 z)
      (Finset.mem_univ y)).trans_eq (hG ω).2)
  have ht y : Tendsto (fun t => ∫ ω, |H t (q t ω) y - G ω y| ∂μ)
      atTop (𝓝 0) := by
    have hc := (tendsto_condExpL1CLM_filtration μ ℱ hgenerate
      ((hint y).toL1 (fun ω => G ω y))).dist
        (tendsto_const_nhds (x := (hint y).toL1 (fun ω => G ω y)))
    simp only [dist_self] at hc
    apply hc.congr
    intro t
    rw [condExpL1CLM_dist_eq_integral_abs]
    apply integral_congr_ae
    filter_upwards [heq t y] with ω hω
    rw [hℱ t, hω]
  simpa using tendsto_finsetSum Finset.univ (fun y _ => ht y)

end IdExp
