import Formal.PulseBehavior
import Formal.CausalPrefixContinuity
import Formal.WaitingQueryReadiness
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Infinite-record identification in the pulse example

Both collectors have a measurable exact label decoder of their actual
infinite path law. This does not assert uniform finite-time decoding, and
it does not identify a complete prefix information objective with a terminal
information divergence.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The infinite action-observation record of a deterministic root choice. -/
def pulsePath (b : Bool) (θ : WaitingQueryWorld) : CausalTraj Bool Bool :=
  fun i => (if i = 0 then b else false,
    if i = 0 then b && θ.isSome else waitingQueryBit θ i)

@[simp] theorem pulsePath_prefix (b : Bool) (θ : WaitingQueryWorld) (t : ℕ) :
    causalPrefixMap t (pulsePath b θ) = pulseTrace b t θ := rfl

theorem pulsePath_injective (b : Bool) : Function.Injective (pulsePath b) := by
  intro θ η h
  apply pulseTrace_all_injective b
  funext t
  exact congrArg (causalPrefixMap t) h

theorem pulsePath_measurable (b : Bool) : Measurable (pulsePath b) :=
  measurable_of_countable _

/-- A measurable label decoder exists on the whole path space, with an
arbitrary value on paths impossible in this deterministic experiment. -/
theorem pulsePath_exact_decoder (b : Bool) :
    ∃ D : CausalTraj Bool Bool → WaitingQueryWorld,
      Measurable D ∧ ∀ θ, D (pulsePath b θ) = θ := by
  let e := (pulsePath_measurable b).measurableEmbedding (pulsePath_injective b)
  exact ⟨e.invFun, e.measurable_invFun, e.leftInverse_invFun⟩

theorem pulsePath_mem_cylinder (b : Bool) (θ : WaitingQueryWorld)
    (h : CausalHistory Bool Bool) :
    pulsePath b θ ∈ causalCyl h ↔ h = List.ofFn (pulseTrace b h.length θ) := by
  rw [mem_causalCyl]
  constructor
  · intro he
    have hf : (fun i : Fin h.length => h[i]) = pulseTrace b h.length θ := by
      funext i
      exact (he i).symm
    rw [← hf]
    simp
  · intro he i
    have hf := congrArg (fun l : List (Bool × Bool) => l[i.val]?) he
    simpa [List.getElem?_eq_getElem i.isLt, pulseTrace, pulsePath] using hf.symm

/-- The actual causal path probability measure is concentrated at the
explicit infinite record. -/
theorem pulse_pathMeasure_eq_dirac (b : Bool) (θ : WaitingQueryWorld) :
    causalPathMeasure (pulsePolicy b).1 (pulsePolicy b).2
      (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _) =
      Measure.dirac (pulsePath b θ) := by
  apply causalPathLaw_unique (pulsePolicy b).1 (detResponse (pulseOutput θ))
    (isCausalPathLaw_causalPathMeasure _ _ _ _)
  refine ⟨inferInstance, fun h => ?_⟩
  change Measure.dirac (pulsePath b θ) (causalCyl h) =
    ENNReal.ofReal (causalTraceProb (detPolicy (pulseAction b)) (detResponse (pulseOutput θ)) h)
  rw [causalTraceProb_det, pulse_detTraceList,
    Measure.dirac_apply' _ (measurableSet_causalCyl h)]
  by_cases he : h = List.ofFn (pulseTrace b h.length θ)
  · rw [if_pos he, Set.indicator_of_mem ((pulsePath_mem_cylinder b θ h).2 he)]
    simp
  · rw [if_neg he, Set.indicator_of_notMem (fun hm => he ((pulsePath_mem_cylinder b θ h).1 hm))]
    simp

/-- Exact identification is under every world law, including the no-pulse
world; there is no prior-null exception. -/
theorem pulse_terminal_exact_identification (b : Bool) :
    ∃ D : CausalTraj Bool Bool → WaitingQueryWorld, Measurable D ∧ ∀ θ,
      (causalPathMeasure (pulsePolicy b).1 (pulsePolicy b).2
        (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _))
        {ω | D ω = θ} = 1 := by
  obtain ⟨D, hD, hcorrect⟩ := pulsePath_exact_decoder b
  refine ⟨D, hD, fun θ => ?_⟩
  rw [pulse_pathMeasure_eq_dirac]
  change (Measure.dirac (pulsePath b θ)) (D ⁻¹' {θ}) = 1
  rw [Measure.dirac_apply' _ (hD (measurableSet_singleton θ))]
  simp [hcorrect]

/-- Terminal exact identification and failure of native sufficiency coexist
in this one concrete countable controlled-behavior family. -/
theorem pulse_terminal_identification_without_native_sufficiency :
    (∃ D : CausalTraj Bool Bool → WaitingQueryWorld, Measurable D ∧ ∀ θ,
      (causalPathMeasure (pulsePolicy false).1 (pulsePolicy false).2
        (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _))
        {ω | D ω = θ} = 1) ∧
    ¬ CausalBehaviorNativelySufficient pulseBehavior (pulsePolicy false) :=
  ⟨pulse_terminal_exact_identification false, pulse_wait_not_nativelySufficient⟩

/-- The actual terminal statistical experiment of either deterministic
collector, with its full action-observation path as signal. -/
noncomputable def pulseTerminalExperiment (b : Bool) :
    Experiment WaitingQueryWorld (CausalTraj Bool Bool) := fun θ =>
  causalPathMeasure (pulsePolicy b).1 (pulsePolicy b).2
    (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _)

/-- Every deterministic pulse collector can simulate the other from its
complete infinite record, in the measurable Blackwell sense. -/
theorem pulse_terminal_blackwell (b c : Bool) :
    BlackwellLE (pulseTerminalExperiment b) (pulseTerminalExperiment c) := by
  obtain ⟨D, hD, hcorrect⟩ := pulsePath_exact_decoder c
  let f : CausalTraj Bool Bool → CausalTraj Bool Bool := pulsePath b ∘ D
  have hf : Measurable f := (pulsePath_measurable b).comp hD
  refine ⟨Kernel.deterministic f hf, inferInstance, fun θ => ?_⟩
  simp only [pulseTerminalExperiment, pulse_pathMeasure_eq_dirac]
  rw [Measure.dirac_bind (Kernel.deterministic f hf).measurable]
  simp [Kernel.deterministic_apply, f, hcorrect]

/-- Any score invariant under terminal Blackwell equivalence ties WAIT and
QUERY, although their growing processes are strictly ordered. -/
theorem pulse_terminal_invariant_score_ties
    {R : Type*} (score : Experiment WaitingQueryWorld (CausalTraj Bool Bool) → R)
    (hinvariant : ∀ E F, BlackwellLE E F → BlackwellLE F E → score E = score F) :
    score (pulseTerminalExperiment false) = score (pulseTerminalExperiment true) ∧
    CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy true) (pulsePolicy false) ∧
    ¬ CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy false) (pulsePolicy true) :=
  ⟨hinvariant _ _ (pulse_terminal_blackwell false true) (pulse_terminal_blackwell true false),
    pulse_query_strictly_dominates_wait⟩

end IdExp
