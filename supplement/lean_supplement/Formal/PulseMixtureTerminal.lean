import Formal.PulseMixture
import Formal.PulseTerminal

/-!
# Exact terminal identification for every root-query mixture

All randomized root choices still reveal the world from the entire pulse
stream. The same world-independent measurable decoder works in both branches.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- One measurable decoder works simultaneously for both root choices. -/
theorem pulsePath_common_exact_decoder :
    ∃ D : CausalTraj Bool Bool → WaitingQueryWorld, Measurable D ∧
      ∀ b θ, D (pulsePath b θ) = θ := by
  obtain ⟨D0, h0, hc0⟩ := pulsePath_exact_decoder false
  obtain ⟨D1, h1, hc1⟩ := pulsePath_exact_decoder true
  let D : CausalTraj Bool Bool → WaitingQueryWorld :=
    fun ω => if (ω 0).1 then D1 ω else D0 ω
  have hD : Measurable D := by
    apply Measurable.ite _ h1 h0
    exact measurableSet_eq_fun ((measurable_pi_apply 0).fst) measurable_const
  refine ⟨D, hD, fun b θ => ?_⟩
  cases b <;> simp [D, pulsePath, hc0, hc1]

/-- The actual path law of the randomized collector is a once-at-root
mixture of the two deterministic complete records. -/
theorem pulseMix_pathMeasure_eq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (θ : WaitingQueryWorld) :
    causalPathMeasure (pulseMixPolicy s) (pulseMixPolicy_valid hs)
      (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _) =
      ENNReal.ofReal (1 - s) • Measure.dirac (pulsePath false θ) +
      ENNReal.ofReal s • Measure.dirac (pulsePath true θ) := by
  apply causalPathLaw_unique (pulseMixPolicy s) (detResponse (pulseOutput θ))
    (isCausalPathLaw_causalPathMeasure _ _ _ _)
  constructor
  · constructor
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hs.2) hs.1]
    simp
  · intro h
    have h0 := causalPathMeasure_cyl (pulsePolicy false).1 (pulsePolicy false).2
      (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _) h
    have h1 := causalPathMeasure_cyl (pulsePolicy true).1 (pulsePolicy true).2
      (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _) h
    rw [pulse_pathMeasure_eq_dirac] at h0 h1
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [smul_eq_mul]
    rw [h0, h1, ← ENNReal.ofReal_mul (sub_nonneg.mpr hs.2), ← ENNReal.ofReal_mul hs.1,
      ← ENNReal.ofReal_add
        (mul_nonneg (sub_nonneg.mpr hs.2) (causalTraceProb_nonneg _ (pulsePolicy false).2 _
          (isCausalResponse_detResponse _) h))
        (mul_nonneg hs.1 (causalTraceProb_nonneg _ (pulsePolicy true).2 _
          (isCausalResponse_detResponse _) h)), pulseMix_trace]

/-- Every mixture exactly identifies every world from the terminal record.
The all-zero pulse stream is decoded as the no-pulse world. -/
theorem pulseMix_terminal_exact_identification {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ D : CausalTraj Bool Bool → WaitingQueryWorld, Measurable D ∧ ∀ θ,
      (causalPathMeasure (pulseMixPolicy s) (pulseMixPolicy_valid hs)
        (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _))
        {ω | D ω = θ} = 1 := by
  obtain ⟨D, hD, hc⟩ := pulsePath_common_exact_decoder
  refine ⟨D, hD, fun θ => ?_⟩
  rw [pulseMix_pathMeasure_eq hs]
  change (ENNReal.ofReal (1 - s) • Measure.dirac (pulsePath false θ) +
    ENNReal.ofReal s • Measure.dirac (pulsePath true θ)) (D ⁻¹' {θ}) = 1
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hD (measurableSet_singleton θ))]
  simp [hc]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hs.2) hs.1]
  simp

/-- The terminal identification statement and the exact finite native
profile have different answers on every nontrivial waiting mixture. -/
theorem pulseMix_identifies_but_not_native {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hne : s ≠ 1) :
    (∃ D : CausalTraj Bool Bool → WaitingQueryWorld, Measurable D ∧ ∀ θ,
      (causalPathMeasure (pulseMixPolicy s) (pulseMixPolicy_valid hs)
        (detResponse (pulseOutput θ)) (isCausalResponse_detResponse _))
        {ω | D ω = θ} = 1) ∧
    ¬ CausalBehaviorNativelySufficient pulseBehavior ⟨pulseMixPolicy s, pulseMixPolicy_valid hs⟩ :=
  ⟨pulseMix_terminal_exact_identification hs, fun h => hne ((pulseMix_nativelySufficient_iff hs).1 h)⟩

end IdExp
