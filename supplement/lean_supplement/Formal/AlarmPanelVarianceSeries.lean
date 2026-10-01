import Formal.AlarmPanelPrior
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The finite-valued monitor variance series and its strict comparison. The
causal posterior bridge is separate; these are the exact series estimates. -/
namespace IdExp.AlarmPanelVariance
open Filter Topology
noncomputable section

def alarmMass (k : ℕ) : ℝ := (1/2 : ℝ)^(k+2)
def silentMass (k : ℕ) : ℝ := 1/2 + (1/2 : ℝ)^(k+1)
def playTerm (k : ℕ) : ℝ := 2 * alarmMass k * (1 - alarmMass k / silentMass k)

theorem alarmMass_pos (k : ℕ) : 0 < alarmMass k := by unfold alarmMass; positivity

theorem alarmMass_summable : Summable alarmMass := by
  have he : alarmMass = fun k => (1/2 : ℝ)^k * (1/4) := by
    funext k
    simp [alarmMass, pow_add]
    ring
  rw [he]
  exact (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_right _

theorem alarmMass_sum : (∑' k, alarmMass k) = 1/2 := by
  have he : alarmMass = fun k => (1/2 : ℝ)^k * (1/4) := by
    funext k
    simp [alarmMass, pow_add]
    ring
  rw [he, tsum_mul_right, tsum_geometric_of_lt_one
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)]
  norm_num

theorem silentMass_eq (k : ℕ) : silentMass k = 1/2 + 2 * alarmMass k := by
  unfold silentMass alarmMass
  rw [show k+2=(k+1)+1 by omega, pow_succ]
  ring

theorem alarmMass_le_quarter (k : ℕ) : alarmMass k ≤ 1/4 := by
  have h : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold alarmMass
  rw [pow_add]
  norm_num
  linarith

theorem silentMass_pos (k : ℕ) : 0 < silentMass k := by
  rw [silentMass_eq]
  have h := alarmMass_pos k
  linarith

theorem hazard_bounds (k : ℕ) :
    0 ≤ alarmMass k / silentMass k ∧ alarmMass k / silentMass k ≤ 1/4 := by
  constructor
  · exact div_nonneg (alarmMass_pos k).le (silentMass_pos k).le
  · apply (div_le_iff₀ (silentMass_pos k)).2
    rw [silentMass_eq]
    have h := alarmMass_le_quarter k
    linarith

theorem playTerm_bounds (k : ℕ) :
    (3/2 : ℝ) * alarmMass k ≤ playTerm k ∧ playTerm k ≤ 2 * alarmMass k := by
  have ha := alarmMass_pos k
  have hh := hazard_bounds k
  unfold playTerm
  constructor <;> nlinarith

theorem playTerm_nonneg (k : ℕ) : 0 ≤ playTerm k :=
  (mul_nonneg (by norm_num : (0:ℝ) ≤ 3/2) (alarmMass_pos k).le).trans (playTerm_bounds k).1

theorem playTerm_summable : Summable playTerm :=
  Summable.of_nonneg_of_le playTerm_nonneg (fun k => (playTerm_bounds k).2)
    (alarmMass_summable.mul_left 2)

def playTotal : ℝ := ∑' k, playTerm k
def inspectTotal : ℝ := 1/4 + ∑' k, alarmMass k

@[simp] theorem inspectTotal_eq : inspectTotal = 3/4 := by
  rw [inspectTotal, alarmMass_sum]
  norm_num

theorem playTotal_gt : (3/4 : ℝ) < playTotal := by
  have h := Summable.tsum_lt_tsum (fun k => (playTerm_bounds k).1)
    (show (3/2 : ℝ) * alarmMass 1 < playTerm 1 by
      norm_num [alarmMass, playTerm, silentMass])
    (alarmMass_summable.mul_left (3/2)) playTerm_summable
  norm_num [tsum_mul_left, alarmMass_sum, playTotal] at h ⊢
  exact h

theorem playTotal_le_one : playTotal ≤ 1 := by
  have h := Summable.tsum_le_tsum (fun k => (playTerm_bounds k).2)
    playTerm_summable (alarmMass_summable.mul_left 2)
  simpa [tsum_mul_left, alarmMass_sum, playTotal] using h

/-- The root-mixture formula, once identified with the actual causal score,
is maximized exactly when inspection probability is zero. -/
def mixture (s : ℝ) : ℝ := s * inspectTotal + (1-s) * playTotal

theorem mixture_le (s : ℝ) (hs : 0 ≤ s) : mixture s ≤ playTotal := by
  have h := playTotal_gt
  rw [mixture, inspectTotal_eq]
  nlinarith

theorem mixture_eq_iff (s : ℝ) (hs : 0 ≤ s) : mixture s = playTotal ↔ s = 0 := by
  rw [mixture, inspectTotal_eq]
  have h := playTotal_gt
  constructor
  · intro he; nlinarith
  · intro he; simp [he]

end
end IdExp.AlarmPanelVariance
