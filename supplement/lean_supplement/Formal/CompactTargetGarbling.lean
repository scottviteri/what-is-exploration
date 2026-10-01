import Formal.CompactDecoderFamily
import Formal.MeasureTVTopology
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Exact garbling from a finite source into a compact target

With finite source signals and a compact Hausdorff target whose finite Borel
measures have a Hausdorff weak topology, zero deficiency is attained by an
actual Markov kernel. The world class need not be finite. This is not a
general attainment result for arbitrary infinite source signals.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {Θ X Y : Type*} [Fintype X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
  [T2Space Y] [CompactSpace Y] [HasOuterApproxClosed Y] [Nonempty Y]

omit [Nonempty Y] in
/-- The set of experiments obtained by decoding one finite source into a
compact target is weakly closed, simultaneously at every world. -/
theorem isClosed_range_finiteSourceDecodedLaw (E : FiniteExperiment Θ X) :
    IsClosed (range fun D : X → ProbabilityMeasure Y =>
      fun θ => finiteSourceDecodedLaw (E θ) D) := by
  apply IsCompact.isClosed
  exact isCompact_range (continuous_pi fun θ => continuous_finiteSourceDecodedLaw (E θ))

/-- Zero directed deficiency is exact Blackwell dominance for a finite
source and compact target. Compactness is used on decoder rows; the target
experiment may be indexed by an arbitrary world class. -/
theorem blackwellLE_of_finiteSource_deficiency_zero
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : Θ → FiniteMeasure Y) (hF : ∀ θ, IsProbabilityMeasure (F θ : Measure Y))
    (hzero : finiteMeasureDeficiency (rowExperiment E) F = 0) :
    BlackwellLE (fun θ => (F θ : Measure Y))
      (fun θ => (rowExperiment E θ : Measure X)) := by
  have hprobE : ∀ θ, IsProbabilityMeasure (rowExperiment E θ : Measure X) :=
    fun θ => isProbabilityMeasure_finiteMeasureOfRow (E θ) (hE θ)
  have hne := finiteMeasureDeficiencyCandidates_nonempty_of_prob
    (rowExperiment E) F hprobE hF
  have happ (n : ℕ) : ∃ G : FiniteMarkovKernel X Y, ∀ θ,
      finiteMeasureTV (finiteMarkovDecode G (rowExperiment E θ) : Measure Y)
        (F θ : Measure Y) ≤ 1 / ((n : ℝ) + 1) := by
    simpa only [hzero, zero_add] using
      exists_finiteMarkovDecoder_le_add_of_nonempty (rowExperiment E) F hne
        (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose G hG using happ
  let D : ℕ → X → ProbabilityMeasure Y := fun n => (G n).probabilityRows
  have hlim : Tendsto (fun n => fun θ => finiteSourceDecodedLaw (E θ) (D n))
      atTop (𝓝 F) := by
    apply tendsto_pi_nhds.2
    intro θ
    apply tendsto_finiteMeasure_of_tendsto_TV_zero
    apply squeeze_zero (fun n => finiteMeasureTV_nonneg _ _)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [D, finiteSourceDecodedLaw_eq_finiteMarkovDecode, rowExperiment] using hG n θ
  have hmem : F ∈ range (fun D : X → ProbabilityMeasure Y =>
      fun θ => finiteSourceDecodedLaw (E θ) D) :=
    (isClosed_range_finiteSourceDecodedLaw E).mem_of_tendsto hlim
      (Eventually.of_forall fun n => ⟨D n, rfl⟩)
  obtain ⟨D₀, hD₀⟩ := hmem
  let K := finiteSourceDecoderKernel D₀
  refine ⟨K.toKernel, K.isMarkov, fun θ => ?_⟩
  change (finiteMarkovDecode K (rowExperiment E θ) : Measure Y) = (F θ : Measure Y)
  have h := congrFun hD₀ θ
  change finiteSourceDecodedLaw (E θ) D₀ = F θ at h
  change ((finiteMarkovDecode (finiteSourceDecoderKernel D₀)
    (finiteMeasureOfRow (E θ)) : FiniteMeasure Y) : Measure Y) = (F θ : Measure Y)
  exact congrArg Subtype.val
    ((finiteMarkovDecode_finiteSourceDecoderKernel (E θ) D₀).trans h)

end IdExp
