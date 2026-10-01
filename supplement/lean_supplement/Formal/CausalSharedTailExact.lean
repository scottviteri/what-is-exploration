import Formal.CausalSharedTailTerminal
import Formal.CompactTargetGarbling

/-!
# Exact terminal garbling after a shared continuation

Finite-alphabet trajectories are compact metrizable. Finite-source
zero-deficiency attainment therefore upgrades the shared-tail prefix/path
equivalence to exact Blackwell equivalence. The discrete topologies are
supplied internally, not extra assumptions on the causal interface.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory

variable {A O Θ X : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- Any finite source with zero deficiency to a finite-alphabet causal path
admits one exact world-independent path decoder. No finiteness of the world
class is needed in this attainment step. -/
theorem blackwellLE_causalPath_of_finiteSource_deficiency_zero
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O)
    (hzero : finiteMeasureDeficiency (rowExperiment E)
      (causalPathExperiment Qs hQ π) = 0) :
    BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
      (fun θ => (rowExperiment E θ : Measure X)) := by
  let : TopologicalSpace A := ⊥
  let : TopologicalSpace O := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : DiscreteTopology O := ⟨rfl⟩
  exact blackwellLE_of_finiteSource_deficiency_zero E hE
    (causalPathExperiment Qs hQ π)
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π) hzero

variable [Fintype Θ] [Nonempty Θ]

/-- Exact simulation of the entire path from a fixed recorded prefix when
all worlds share the continuation after that prefix. -/
theorem causalSharedTail_prefix_path_blackwell
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSharedCausalTail Qs k R) :
    BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
      (fun θ => (causalTraceMeasureExperiment Qs hQ π k θ :
        Measure (CausalFiniteTrace A O k))) := by
  rw [causalTraceMeasureExperiment_eq_rowExperiment]
  apply blackwellLE_causalPath_of_finiteSource_deficiency_zero
    (causalFiniteExperiment π.val Qs k)
    (causalFiniteExperiment_valid π.val π.property Qs hQ k) Qs hQ π
  rw [← causalTraceMeasureExperiment_eq_rowExperiment]
  exact causalSharedTail_prefix_path_deficiency_zero Qs hQ π R hR k htail

/-- The prefix projection supplies the reverse exact garbling. -/
theorem causalSharedTail_prefix_path_blackwell_equiv
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSharedCausalTail Qs k R) :
    BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
        (fun θ => (causalTraceMeasureExperiment Qs hQ π k θ :
          Measure (CausalFiniteTrace A O k))) ∧
      BlackwellLE (fun θ => (causalTraceMeasureExperiment Qs hQ π k θ :
          Measure (CausalFiniteTrace A O k)))
        (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))) := by
  refine ⟨causalSharedTail_prefix_path_blackwell Qs hQ π R hR k htail,
    (causalPrefixKernel k).toKernel, (causalPrefixKernel k).isMarkov, fun θ => ?_⟩
  exact congrArg Subtype.val (finiteMarkovDecode_causalPrefixKernel Qs hQ π k θ)

end IdExp
