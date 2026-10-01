import Formal.MeasureDeficiency

/-!
# Finite-source decoder families in the weak topology

A Markov decoder from a finite discrete source is a finite tuple of probability
measures. Its output law is the continuous finite mixture of these rows. The
identities below use the existing `finiteMarkovDecode` and `rowExperiment`, so
compactness of the tuple space can be applied to the actual decoder family.
The target need not be finite, and continuity requires neither compactness nor
Hausdorffness; those hypotheses belong to subsequent attainment arguments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace IdExp

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The probability-measure rows of a bundled Markov kernel. -/
def FiniteMarkovKernel.probabilityRows (G : FiniteMarkovKernel X Y) :
    X → ProbabilityMeasure Y := fun x => by
  let _ : IsMarkovKernel G.toKernel := G.isMarkov
  exact ⟨G.toKernel x, inferInstance⟩

@[simp] theorem FiniteMarkovKernel.coe_probabilityRows
    (G : FiniteMarkovKernel X Y) (x : X) :
    (G.probabilityRows x : Measure Y) = G.toKernel x := rfl

variable [Fintype X] [MeasurableSingletonClass X]

/-- The output measure obtained by mixing a finite tuple of probability rows.
As for `finiteMeasureOfRow`, negative input weights are clipped to zero. -/
def finiteSourceDecodedLaw (p : X → ℝ) (D : X → ProbabilityMeasure Y) :
    FiniteMeasure Y := ∑ x, (p x).toNNReal • (D x).toFiniteMeasure

/-- Every tuple of probability measures is a Markov decoder on a finite
discrete source. There is no extra measurable-selection condition. -/
def finiteSourceDecoderKernel (D : X → ProbabilityMeasure Y) :
    FiniteMarkovKernel X Y where
  toKernel := {
    toFun := fun x => (D x : Measure Y)
    measurable' := measurable_of_countable _ }
  isMarkov := ⟨fun x => (D x).property⟩

@[simp] theorem finiteSourceDecoderKernel_probabilityRows
    (D : X → ProbabilityMeasure Y) :
    (finiteSourceDecoderKernel D).probabilityRows = D := rfl

/-- Finite mixing is continuous for the weak topology on finite measures. -/
theorem continuous_finiteSourceDecodedLaw
    [TopologicalSpace Y] [OpensMeasurableSpace Y] (p : X → ℝ) :
    Continuous (finiteSourceDecodedLaw (Y := Y) p) := by
  unfold finiteSourceDecodedLaw
  apply continuous_finsetSum
  intro x _
  exact (show Continuous (fun _ : X → ProbabilityMeasure Y => (p x).toNNReal)
    from continuous_const).smul
      (ProbabilityMeasure.toFiniteMeasure_continuous.comp (continuous_apply x))

/-- The tuple representation computes the output law of the original bundled
Markov kernel, including when the input row is not normalized. -/
theorem finiteSourceDecodedLaw_eq_finiteMarkovDecode (p : X → ℝ)
    (G : FiniteMarkovKernel X Y) :
    finiteSourceDecodedLaw p G.probabilityRows =
      finiteMarkovDecode G (finiteMeasureOfRow p) := by
  let _ : IsMarkovKernel G.toKernel := G.isMarkov
  apply FiniteMeasure.toMeasure_injective
  ext s hs
  change ((∑ x, (p x).toNNReal • (G.probabilityRows x).toFiniteMeasure :
    FiniteMeasure Y) : Measure Y) s =
      (G.toKernel ∘ₘ (Measure.count.withDensity fun x => ENNReal.ofReal (p x))) s
  rw [FiniteMeasure.toMeasure_sum, Measure.finsetSum_apply,
    Measure.bind_apply hs (Kernel.aemeasurable G.toKernel)]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (Kernel.measurable_coe G.toKernel hs), lintegral_count, tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  rfl

/-- Decoding by the kernel built from a tuple is exactly finite mixing. -/
theorem finiteMarkovDecode_finiteSourceDecoderKernel (p : X → ℝ)
    (D : X → ProbabilityMeasure Y) :
    finiteMarkovDecode (finiteSourceDecoderKernel D) (finiteMeasureOfRow p) =
      finiteSourceDecodedLaw p D := by
  simpa using (finiteSourceDecodedLaw_eq_finiteMarkovDecode p
    (finiteSourceDecoderKernel D)).symm

/-- The same identification for the repository's bundled finite-row experiments. -/
theorem finiteSourceDecodedLaw_eq_decode_rowExperiment {Θ : Type*}
    (E : FiniteExperiment Θ X) (G : FiniteMarkovKernel X Y) (θ : Θ) :
    finiteSourceDecodedLaw (E θ) G.probabilityRows =
      finiteMarkovDecode G (rowExperiment E θ) :=
  finiteSourceDecodedLaw_eq_finiteMarkovDecode (E θ) G

end

end IdExp
