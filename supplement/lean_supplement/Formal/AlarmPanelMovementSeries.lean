import Formal.AlarmPanelPosteriorMovement

/-! Summable reward series and a uniform strict inspection advantage for every
proper geometric discount and for the complete undiscounted return. -/
noncomputable section
namespace IdExp.AlarmPanelMovement
open AlarmPanel AlarmPanelVariance PosteriorMovement Finset

 theorem fair_bounds (kind : Kind) : 0 < fairReward kind ∧ fairReward kind ≤ 1 := by
  cases kind
  · have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2:ℝ)
    simp only [fairReward]; constructor <;> nlinarith
  · norm_num [fairReward]

theorem binary_bounds (kind : Kind) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryReward kind p ∧ binaryReward kind p ≤ 4*p := by
  cases kind
  · have hq : 0 ≤ 1-p := by linarith
    have hs := Real.sq_sqrt hq
    have hn := Real.sqrt_nonneg (1-p)
    have hnp := Real.sqrt_nonneg p
    have hsp := Real.sq_sqrt hp
    have hle : Real.sqrt p ≤ 1 := by nlinarith
    have hleq : Real.sqrt (1-p) ≤ 1 := by nlinarith
    have hpoly : 0 ≤ (1-Real.sqrt (1-p))^2 * (2*Real.sqrt (1-p)+1) := by positivity
    simp only [binaryReward]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hle hp,
        mul_le_mul_of_nonneg_left hleq hq]
    · nlinarith [mul_nonneg hp hnp]
  · simp only [binaryReward]
    constructor <;> nlinarith

theorem hellinger_upper (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryReward .hellinger p ≤ 3*p - 2*p*Real.sqrt p := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-p by linarith)
  have hn := Real.sqrt_nonneg (1-p)
  have hpoly : 0 ≤ (1-Real.sqrt (1-p))^2 * (2*Real.sqrt (1-p)+1) := by positivity
  simp only [binaryReward]
  nlinarith

theorem play_bounds (kind : Kind) (k : ℕ) :
    0 ≤ playTerm kind k ∧ playTerm kind k ≤ 4*alarmMass k := by
  have hb := binary_bounds kind _ (hazard_bounds k).1 (le_trans (hazard_bounds k).2 (by norm_num))
  have hs := silentMass_pos k
  constructor
  · exact mul_nonneg hs.le hb.1
  · unfold playTerm
    calc silentMass k * binaryReward kind (alarmMass k / silentMass k) ≤
        silentMass k * (4*(alarmMass k / silentMass k)) := mul_le_mul_of_nonneg_left hb.2 hs.le
      _ = 4*alarmMass k := by field_simp

theorem play_summable (kind : Kind) : Summable (playTerm kind) :=
  Summable.of_nonneg_of_le (fun k => (play_bounds kind k).1)
    (fun k => (play_bounds kind k).2) (alarmMass_summable.mul_left 4)

theorem inspect_summable (kind : Kind) : Summable (inspectTerm kind) := by
  exact (alarmMass_summable.mul_left 2).mul_right _

theorem inspect_nonneg (kind : Kind) (k : ℕ) : 0 ≤ inspectTerm kind k := by
  unfold inspectTerm
  exact mul_nonneg (mul_nonneg (by norm_num) (alarmMass_pos k).le) (fair_bounds kind).1.le

/-- A summable upper envelope for PLAY's extra monitor reward. Keeping the first
two exact corrections suffices; no numerical approximation enters this bound. -/
def penalty (kind : Kind) (k : ℕ) : ℝ :=
  match kind with
  | .hellinger => (3-2*fairReward .hellinger)*alarmMass k -
      (if k=0 then 1/4 else 0) - (if k=1 then Real.sqrt 2 / 16 else 0)
  | .absolute => 2*alarmMass k - (if k=0 then 1/4 else 0)

theorem penalty_nonneg (kind : Kind) (k : ℕ) : 0 ≤ penalty kind k := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have ha := alarmMass_pos k
  cases kind
  · by_cases h0 : k=0
    · subst k; norm_num [penalty, fairReward, alarmMass]; nlinarith
    · by_cases h1 : k=1
      · subst k; norm_num [penalty, fairReward, alarmMass]; nlinarith
      · simp only [penalty, fairReward, if_neg h0, if_neg h1, sub_zero]
        apply mul_nonneg _ ha.le; nlinarith
  · by_cases h0 : k=0
    · subst k; norm_num [penalty, alarmMass]
    · simp only [penalty, if_neg h0, sub_zero]; positivity

theorem play_extra_le_penalty (kind : Kind) (k : ℕ) :
    playTerm kind k - inspectTerm kind k ≤ penalty kind k := by
  have ha := alarmMass_pos k
  have hs := silentMass_pos k
  have hh := hazard_bounds k
  cases kind
  · have hu := mul_le_mul_of_nonneg_left
      (hellinger_upper _ hh.1 (hh.2.trans (by norm_num))) hs.le
    have hm : silentMass k * (3*(alarmMass k / silentMass k) -
        2*(alarmMass k / silentMass k)*Real.sqrt (alarmMass k / silentMass k)) =
        3*alarmMass k - 2*alarmMass k*Real.sqrt (alarmMass k / silentMass k) := by field_simp
    rw [hm] at hu
    have hmass : silentMass k ≤ 1 := by rw [silentMass_eq]; linarith [alarmMass_le_quarter k]
    have hdiv : alarmMass k ≤ alarmMass k / silentMass k :=
      (le_div_iff₀ hs).2 (mul_le_of_le_one_right ha.le hmass)
    have hroot := Real.sqrt_le_sqrt hdiv
    have hcor : (if k=0 then (1/4:ℝ) else 0) +
        (if k=1 then Real.sqrt 2 / 16 else 0) ≤ 2*alarmMass k*Real.sqrt (alarmMass k) := by
      by_cases h0 : k=0
      · subst k; norm_num [alarmMass, Real.sqrt_div]
      · by_cases h1 : k=1
        · subst k
          have he : Real.sqrt (1/8:ℝ) = Real.sqrt 2 / 4 := by
            have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 1/8 by norm_num)
            have hsq2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
            nlinarith [Real.sqrt_nonneg (1/8:ℝ), Real.sqrt_nonneg (2:ℝ)]
          rw [show alarmMass 1 = (1/8:ℝ) by norm_num [alarmMass]]
          simp only [show ¬ (1:ℕ)=0 by decide, if_false, if_true, zero_add]
          rw [he]; ring_nf; exact le_rfl
        · simp only [if_neg h0, if_neg h1, zero_add]; positivity
    simp only [playTerm, inspectTerm, penalty]
    nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*alarmMass k by positivity)]
  · have he : playTerm .absolute k - inspectTerm .absolute k = alarmMass k / silentMass k := by
      unfold playTerm inspectTerm binaryReward fairReward
      rw [silentMass_eq]
      field_simp
      ring
    rw [he]
    by_cases h0 : k=0
    · subst k; norm_num [penalty, alarmMass, silentMass]
    · simp only [penalty, if_neg h0, sub_zero]
      apply (div_le_iff₀ hs).2
      rw [silentMass_eq]
      nlinarith [sq_nonneg (alarmMass k)]

theorem penalty_summable (kind : Kind) : Summable (penalty kind) := by
  cases kind
  · exact ((alarmMass_summable.mul_left _).sub ((hasSum_ite_eq 0 _).summable)).sub ((hasSum_ite_eq 1 _).summable)
  · exact (alarmMass_summable.mul_left _).sub ((hasSum_ite_eq 0 _).summable)

theorem penalty_sum_lt (kind : Kind) : (∑' k, penalty kind k) < fairReward kind := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  cases kind
  · simp only [penalty]
    rw [Summable.tsum_sub ((alarmMass_summable.mul_left _).sub ((hasSum_ite_eq 0 _).summable))
        ((hasSum_ite_eq 1 _).summable),
      Summable.tsum_sub (alarmMass_summable.mul_left _) ((hasSum_ite_eq 0 _).summable),
      tsum_mul_left, alarmMass_sum, tsum_ite_eq, tsum_ite_eq]
    simp only [fairReward]
    nlinarith
  · simp only [penalty]
    rw [Summable.tsum_sub (alarmMass_summable.mul_left _) ((hasSum_ite_eq 0 _).summable),
      tsum_mul_left, alarmMass_sum, tsum_ite_eq]
    norm_num [fairReward]

end IdExp.AlarmPanelMovement
