import Formal.PairedAlarmEmpowermentChannel

/-!
# Terminal-channel components of the paired alarm's block-capacity return

This supplies terminal-component expectations to the return algebra in
`PairedAlarmBlockComplete`. The paper's literal full-block channel and complete
objective are defined in `PairedAlarmBlockChannel`. Here `multiStepCapacity`
retains only the terminal sensor of a probe; it is one component, not the selected
block capacity. Its expectation at each positive collection time is `1 - s`, where
`s` is the collecting policy's startup inspection probability. The selected
block calculation sums the components for probe lengths `1,...,n`, giving
`n * (1 - s)` per positive collection time.

Only the policy-history expectation and finite component sums are kept here.
`PairedAlarmBlockChannel` supplies the full-block factorization, actual startup
integral, and complete literal objective comparison.
-/

noncomputable section
namespace IdExp.PairedAlarm.Empowerment
open Finset

/-! ## A non-inspecting witness policy -/

/-- Always PLAY₀; it never inspects. -/
def playPolicy : ValidCausalPolicy Action Observation := validDetPolicy fun _ => play0

theorem playPolicy_inspection : inspectionProbability playPolicy.1 = 0 := by
  norm_num [inspectionProbability, playPolicy, validDetPolicy, detPolicy, inspect, play0]

/-! ## Expected empowerment at the actual visited history -/

/-- Expected terminal-observation capacity at the collecting policy's history after
`t` observations, in a fixed world. -/
def multiStepStage (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World)
    (t : ℕ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Observation t,
    experiment π.1 t θ w * multiStepCapacity θ (List.ofFn w) n

theorem multiStepStage_zero (n : ℕ) (π : ValidCausalPolicy Action Observation)
    (θ : World) : multiStepStage n π θ 0 = multiStepCapacity θ [] n := by
  simp [multiStepStage, experiment, causalFiniteExperiment, causalTraceProb,
    causalTraceProbFrom]

theorem inspected_ofFn (t : ℕ) (w : CausalFiniteTrace Action Observation (t + 1)) :
    inspected (List.ofFn w) ↔ (w 0).1 = inspect := by
  rw [List.ofFn_succ]
  exact inspected_cons _ _ _

/-- At every positive time, in every world, the expected terminal capacity is the
play-branch probability `1 - s`, whatever the policy does after startup. -/
theorem multiStepStage_succ (n : ℕ) (π : ValidCausalPolicy Action Observation)
    (θ : World) (t : ℕ) :
    multiStepStage (n + 1) π θ (t + 1) = 1 - inspectionProbability π.1 := by
  have hl (w : CausalFiniteTrace Action Observation (t + 1)) :
      multiStepCapacity θ (List.ofFn w) (n + 1) = if (w 0).1 = inspect then 0 else 1 := by
    rw [multiStepCapacity_tail θ (List.ofFn w) (by simp) n]
    by_cases hi : (w 0).1 = inspect
    · rw [if_pos ((inspected_ofFn t w).2 hi), if_pos hi]
    · rw [if_neg (fun h => hi ((inspected_ofFn t w).1 h)), if_neg hi]
  have hr := causalFiniteExperiment_root_action_mass response response_valid π t θ inspect
  change (∑ w : CausalFiniteTrace Action Observation (t + 1),
    if (w 0).1 = inspect then experiment π.1 (t + 1) θ w else 0) = π.1 [] inspect at hr
  have hn := (experiment_valid π.1 π.2 (t + 1) θ).2
  simp only [multiStepStage, hl]
  calc (∑ w : CausalFiniteTrace Action Observation (t + 1),
        experiment π.1 (t + 1) θ w * (if (w 0).1 = inspect then 0 else 1))
      = (∑ w : CausalFiniteTrace Action Observation (t + 1), experiment π.1 (t + 1) θ w) -
        ∑ w : CausalFiniteTrace Action Observation (t + 1),
          (if (w 0).1 = inspect then experiment π.1 (t + 1) θ w else 0) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro w _
        split_ifs <;> ring
    _ = 1 - inspectionProbability π.1 := by
        rw [hn, hr]
        rfl

/-- Literal finite sum of the expected terminal capacities at times `0, …, N-1`,
in a fixed world. -/
def multiStepFinite (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World)
    (N : ℕ) : ℝ :=
  ∑ t ∈ range N, multiStepStage n π θ t

theorem multiStepFinite_succ (n m : ℕ) (π : ValidCausalPolicy Action Observation)
    (θ : World) :
    multiStepFinite (n + 1) π θ (m + 1) =
      multiStepCapacity θ [] (n + 1) + (1 - inspectionProbability π.1) * m := by
  rw [multiStepFinite, sum_range_succ']
  simp only [multiStepStage_succ, multiStepStage_zero, sum_const, card_range, nsmul_eq_mul]
  ring

end IdExp.PairedAlarm.Empowerment
