import Formal.CausalSharedTail
import Formal.RecoveryBridge
import Formal.BinaryBlackwell

/-!
# Terminal information after a shared causal tail

For a finite world class, a world-independent continuation after horizon k
makes the recorded k-prefix and complete path Le Cam equivalent. Their
pairwise TV distances agree exactly. These results invoke proved prefix
continuity; they do not assume terminal garbling attainment.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- The finite-prefix pair TV is constant once the shared continuation starts. -/
theorem causalTraceMeasure_sharedTail_pairTV
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSharedCausalTail Qs k R) {n : ℕ} (hn : k ≤ n) (θ η : Θ) :
    finiteMeasureTV
      (causalTraceMeasureExperiment Qs hQ π n θ : Measure (CausalFiniteTrace A O n))
      (causalTraceMeasureExperiment Qs hQ π n η : Measure (CausalFiniteTrace A O n)) =
      finiteTV (causalFiniteExperiment π.val Qs k θ) (causalFiniteExperiment π.val Qs k η) := by
  rw [causalTraceMeasureExperiment_eq_rowExperiment]
  simp only [rowExperiment]
  rw [finiteMeasureTV_finiteMeasureOfRow _ _
    (causalFiniteExperiment_valid π.val π.property Qs hQ n θ).1
    (causalFiniteExperiment_valid π.val π.property Qs hQ n η).1]
  exact causalFiniteExperiment_sharedTail_pairTV π.val π.property Qs hQ R hR k htail hn θ η

variable [Fintype Θ] [Nonempty Θ]

/-- A fixed prefix has zero deficiency to the infinite path when all worlds
share the continuation after that prefix. No exact terminal decoder is assumed. -/
theorem causalSharedTail_prefix_path_deficiency_zero
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSharedCausalTail Qs k R) :
    finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π k)
      (causalPathExperiment Qs hQ π) = 0 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨T, hT⟩ := exists_causalPrefixDeficiency_lt Qs hQ π hε
    let n := max T k
    have hn : k ≤ n := le_max_right _ _
    have hzero : finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π k)
        (causalTraceMeasureExperiment Qs hQ π n) = 0 := by
      rw [finiteMeasureDeficiency_trace_trace_eq_finiteDeficiency]
      exact finiteDeficiency_eq_zero_of_finiteBlackwellLE _ _
        (causalFiniteExperiment_of_sharedTail_blackwell π.val π.property Qs R hR k htail hn)
    have htri := finiteMeasureDeficiency_triangle_of_prob
      (causalTraceMeasureExperiment Qs hQ π k)
      (causalTraceMeasureExperiment Qs hQ π n) (causalPathExperiment Qs hQ π)
      (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π k)
      (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π n)
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
    rw [hzero, zero_add] at htri
    exact (htri.trans (hT n (le_max_left _ _)).le).trans_eq (zero_add ε).symm
  · exact finiteMeasureDeficiency_nonneg_of_prob _ _
      (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π k)
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)

/-- Literal pairwise full-path TV equals the finite-prefix TV. -/
theorem causalPath_sharedTail_pairTV
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSharedCausalTail Qs k R) (θ η : Θ) :
    finiteMeasureTV
      (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))
      (causalPathExperiment Qs hQ π η : Measure (CausalTraj A O)) =
      finiteTV (causalFiniteExperiment π.val Qs k θ) (causalFiniteExperiment π.val Qs k η) := by
  apply le_antisymm
  · have h := finiteMeasureDeficiency_pairwise_lower
      (causalTraceMeasureExperiment Qs hQ π k) (causalPathExperiment Qs hQ π)
      (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π k)
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π) θ η
    rw [causalSharedTail_prefix_path_deficiency_zero Qs hQ π R hR k htail,
      causalTraceMeasure_sharedTail_pairTV Qs hQ π R hR k htail le_rfl θ η] at h
    linarith
  · have := (causalPrefixKernel (A := A) (O := O) k).isMarkov
    have h := finiteMeasureTV_comp_le (causalPrefixKernel k).toKernel
      (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))
      (causalPathExperiment Qs hQ π η : Measure (CausalTraj A O))
    change finiteMeasureTV
      (finiteMarkovDecode (causalPrefixKernel k) (causalPathExperiment Qs hQ π θ) :
        Measure (CausalFiniteTrace A O k))
      (finiteMarkovDecode (causalPrefixKernel k) (causalPathExperiment Qs hQ π η) :
        Measure (CausalFiniteTrace A O k)) ≤ _ at h
    simp only [finiteMarkovDecode_causalPrefixKernel] at h
    rw [causalTraceMeasure_sharedTail_pairTV Qs hQ π R hR k htail le_rfl θ η] at h
    exact h

end IdExp
