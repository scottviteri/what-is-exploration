import Formal.PairedAlarmEmpowerment
import Formal.PairedAlarmNativeScore

/-!
# Return algebra for block empowerment and native loss

This reusable return core takes a finite startup expectation b and checks the
component sum, cumulative return, infinite ties, and exact optimizer/native-loss
sets. `PairedAlarmBlockChannel` proves the literal full observation-block
factorization and its startup prior integrability, then instantiates b with
that integral. Use that module for the end-to-end objective. Units are bits.
-/
namespace IdExp.PairedAlarm.BlockComplete
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Each of the `n` coordinates carries one button bit at every nonempty history. -/
def count (n T : ℕ) : ℕ := n * (T - 1)

theorem component_finite_sum (n m : ℕ) (π : ValidCausalPolicy Action Observation)
    (θ : World) :
    (∑ j ∈ range n, (Empowerment.multiStepFinite (j+1) π θ (m+1) -
      Empowerment.multiStepCapacity θ [] (j+1))) =
      (count n (m+1) : ℝ) * (1-inspectionProbability π.1) := by
  simp_rw [Empowerment.multiStepFinite_succ, add_sub_cancel_left]
  simp [count, Nat.cast_mul, nsmul_eq_mul]
  ring

theorem count_lower (n T : ℕ) (hn : 1 ≤ n) : T / 2 ≤ count n T := by
  have h := Nat.mul_le_mul_right (T-1) hn
  simp only [Nat.one_mul] at h
  have hT : T / 2 ≤ T-1 := by omega
  exact hT.trans h

theorem count_mono (n : ℕ) : Monotone (count n) := by
  intro T V hTV
  exact Nat.mul_le_mul_left n (Nat.sub_le_sub_right hTV 1)

theorem count_closed (n T : ℕ) : count n T = n * (T-1) := rfl

/-- Eventual deficiency to the literal paired startup-inspection experiment. -/
def eventualInspectionDeficiency (π : ValidCausalPolicy Action Observation) : ℝ :=
  eventualLoss response π (experiment inspectPolicy 1)

theorem eventualInspectionDeficiency_eq (π : ValidCausalPolicy Action Observation) :
    eventualInspectionDeficiency π = (1-inspectionProbability π.1)/2 :=
  eventual_inspection_loss π

def finiteReturn (b : ℝ) (n : ℕ) (π : ValidCausalPolicy Action Observation) (T : ℕ) : ℝ :=
  if T = 0 then 0 else b + (count n T : ℝ) * (1-inspectionProbability π.1)

/-- Extended nonnegative total. Real tsum would default to zero on divergence. -/
def completeReturn (b : ℝ) (n : ℕ) (π : ValidCausalPolicy Action Observation) : ENNReal :=
  ⨆ T : ℕ, ENNReal.ofReal (finiteReturn b n π T)

theorem finiteReturn_nonneg (b : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (π : ValidCausalPolicy Action Observation) (T : ℕ) : 0 ≤ finiteReturn b n π T := by
  unfold finiteReturn
  split_ifs
  · exact le_rfl
  · exact add_nonneg hb (mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (inspectionProbability_le_one π.1 π.2)))

theorem finiteReturn_mono (b : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (π : ValidCausalPolicy Action Observation) : Monotone (finiteReturn b n π) := by
  intro T V hTV
  by_cases hT : T = 0
  · simp only [finiteReturn, hT]
    exact finiteReturn_nonneg b hb n π V
  · have hV : V ≠ 0 := by omega
    simp only [finiteReturn, hT, hV, if_false]
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast count_mono n hTV)
      (sub_nonneg.mpr (inspectionProbability_le_one π.1 π.2))

theorem inspect_return (b : ℝ) (n : ℕ) (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 = 1) : completeReturn b n π = ENNReal.ofReal b := by
  apply le_antisymm
  · apply iSup_le; intro T
    by_cases hT : T=0 <;> simp [finiteReturn, hs, hT]
  · simpa [completeReturn, finiteReturn, hs] using
      (le_iSup (fun T : ℕ => ENNReal.ofReal (finiteReturn b n π T)) 1)

theorem play_return (b : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (π : ValidCausalPolicy Action Observation) (hs : inspectionProbability π.1 < 1) :
    completeReturn b n π = ⊤ := by
  have hc : 0 < (1-inspectionProbability π.1) := by linarith
  by_contra hne
  obtain ⟨k, hk⟩ := exists_nat_gt (((completeReturn b n π).toReal-b) /
    ((1-inspectionProbability π.1)))
  have hu := le_iSup (fun T : ℕ => ENNReal.ofReal (finiteReturn b n π T)) (2*k+2)
  have hr := (ENNReal.ofReal_le_iff_le_toReal hne).mp hu
  have hcount : ((k+1 : ℕ) : ℝ) ≤ (count n (2*k+2) : ℝ) := by
    exact_mod_cast (show k+1 ≤ count n (2*k+2) by
      have := count_lower n (2*k+2) hn; omega)
  have hk' := (div_lt_iff₀ hc).mp hk
  simp only [finiteReturn, show 2*k+2 ≠ 0 by omega, if_false] at hr
  have := mul_le_mul_of_nonneg_right hcount hc.le
  push_cast at this
  nlinarith

theorem return_top_iff (b : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (π : ValidCausalPolicy Action Observation) :
    completeReturn b n π = ⊤ ↔ inspectionProbability π.1 < 1 := by
  constructor
  · intro h
    by_contra hs
    have he : inspectionProbability π.1 = 1 :=
      le_antisymm (inspectionProbability_le_one π.1 π.2) (le_of_not_gt hs)
    rw [inspect_return b n π he] at h
    exact ENNReal.ofReal_ne_top h
  · exact play_return b n hn π

theorem maximizer_iff (b : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, completeReturn b n ρ ≤ completeReturn b n π) ↔
      inspectionProbability π.1 < 1 := by
  constructor
  · intro h
    have hp := play_return b n hn Empowerment.playPolicy (by rw [Empowerment.playPolicy_inspection]; norm_num)
    have ht : completeReturn b n π = ⊤ := top_le_iff.mp (hp ▸ h Empowerment.playPolicy)
    exact (return_top_iff b n hn π).mp ht
  · intro hs ρ
    rw [play_return b n hn π hs]
    exact le_top

theorem all_optima_failure (b : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, completeReturn b n ρ ≤ completeReturn b n π) :
    0 < eventualInspectionDeficiency π ∧ eventualInspectionDeficiency π ≤ 1/2 ∧
      CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
      ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  have hs := (maximizer_iff b n hn π).mp hopt
  refine ⟨?_, ?_, inspection_strictly_dominates π.1 π.2 hs⟩
  · rw [eventualInspectionDeficiency_eq]; linarith
  · rw [eventualInspectionDeficiency_eq]
    linarith [inspectionProbability_nonneg π.1 π.2]

/-- Prescribe the initial inspection probability; later actions cannot undo the branch. -/
def mixedPolicy (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ValidCausalPolicy Action Observation :=
  ⟨fun _ => ![s, 1-s, 0], by
    intro h
    constructor
    · intro a; fin_cases a <;> simp <;> linarith
    · simp [Fin.sum_univ_three]⟩

theorem mixed_inspection (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    inspectionProbability (mixedPolicy s hs hs1).1 = s := by
  rfl

/-- Every positive loss up to one half occurs at a complete-return optimum. -/
theorem optimizer_loss_realized (b : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1/2) :
    ∃ π : ValidCausalPolicy Action Observation,
      (∀ ρ, completeReturn b n ρ ≤ completeReturn b n π) ∧
      eventualInspectionDeficiency π = d := by
  let π := mixedPolicy (1-2*d) (by linarith : 0 ≤ 1-2*d) (by linarith : 1-2*d ≤ 1)
  have hs : inspectionProbability π.1 = 1-2*d := rfl
  refine ⟨π, (maximizer_iff b n hn π).mpr (by rw [hs]; linarith), ?_⟩
  rw [eventualInspectionDeficiency_eq, hs]
  ring

end
end IdExp.PairedAlarm.BlockComplete
