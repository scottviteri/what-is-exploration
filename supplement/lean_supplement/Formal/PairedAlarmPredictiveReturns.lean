import Formal.PairedAlarmPredictiveStages
import Formal.KnownNoisePredictionError

/-!
# Finite and complete predictive rewards on the coinless alarm

The returns below sum the literal Bayesian next-observation Shannon and Square
stage rewards, including their different deterministic-startup predictions.
PLAY maximizes Shannon from horizon two and Square from horizon three. Complete
Shannon is two bits under certain inspection and infinite with positive PLAY
probability. Every complete Square return diverges to negative infinity.
-/

noncomputable section
namespace IdExp.PairedAlarm.Predictive
open Finset
open AlarmPanelVariance (alarmMass silentMass)

/-- Inspect at every history (only the startup choice matters). -/
def alwaysInspect : ValidCausalPolicy Action Observation := validDetPolicy (fun _ => inspect)

/-- Play `PLAY₀` at every history. -/
def alwaysPlay : ValidCausalPolicy Action Observation := validDetPolicy (fun _ => play0)

theorem alwaysInspect_inspectionProbability : inspectionProbability alwaysInspect.1 = 1 := by
  simp [alwaysInspect, validDetPolicy, detPolicy, inspectionProbability]

theorem alwaysPlay_inspectionProbability : inspectionProbability alwaysPlay.1 = 0 := by
  simp [alwaysPlay, validDetPolicy, detPolicy, inspectionProbability, inspect, play0]

theorem shannonStage_alwaysInspect (t : ℕ) :
    shannonStage alwaysInspect t = shannonInspectValue t := by
  rw [shannonStage_mixture, alwaysInspect_inspectionProbability]; ring

theorem shannonStage_alwaysPlay (t : ℕ) : shannonStage alwaysPlay t = shannonPlayValue t := by
  rw [shannonStage_mixture, alwaysPlay_inspectionProbability]; ring

theorem squareStage_alwaysInspect (t : ℕ) :
    squareStage alwaysInspect t = squareInspectValue t := by
  rw [squareStage_mixture, alwaysInspect_inspectionProbability]; ring

theorem squareStage_alwaysPlay (t : ℕ) : squareStage alwaysPlay t = squarePlayValue t := by
  rw [squareStage_mixture, alwaysPlay_inspectionProbability]; ring

/-- Finite sums include startup as stage zero. -/
def shannonFinite (π : ValidCausalPolicy Action Observation) (H : ℕ) : ℝ :=
  ∑ t ∈ range H, shannonStage π t

def squareFinite (π : ValidCausalPolicy Action Observation) (H : ℕ) : ℝ :=
  ∑ t ∈ range H, squareStage π t

theorem shannonFinite_mixture (π : ValidCausalPolicy Action Observation) (H : ℕ) :
    shannonFinite π H = inspectionProbability π.1 * shannonFinite alwaysInspect H +
      (1-inspectionProbability π.1) * shannonFinite alwaysPlay H := by
  simp only [shannonFinite, shannonStage_mixture, alwaysInspect_inspectionProbability,
    alwaysPlay_inspectionProbability]
  simp only [one_mul, sub_self, zero_mul, add_zero, sub_zero, zero_add]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]

theorem squareFinite_mixture (π : ValidCausalPolicy Action Observation) (H : ℕ) :
    squareFinite π H = inspectionProbability π.1 * squareFinite alwaysInspect H +
      (1-inspectionProbability π.1) * squareFinite alwaysPlay H := by
  simp only [squareFinite, squareStage_mixture, alwaysInspect_inspectionProbability,
    alwaysPlay_inspectionProbability]
  simp only [one_mul, sub_self, zero_mul, add_zero, sub_zero, zero_add]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]

/-- Strict concavity makes the first alarm tick repay the startup information bit. -/
theorem shannon_first_tick_gap :
    1 < shannonPlayValue 1 - shannonInspectValue 1 := by
  have hc := Real.strictConcave_binEntropy.2
    (show (0:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1/2:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (by norm_num : (0:ℝ) ≠ 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  have hh : Real.binEntropy (1/2:ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  norm_num [smul_eq_mul, hh] at hc
  have hdiv := (lt_div_iff₀ log_two_pos).2 hc
  norm_num [shannonPlayValue, shannonInspectValue, alarmMass,
    AlarmPanelVariance.silentMass_eq, binEntropyBits]
  linarith

theorem shannonFinite_inspect_lt_play (H : ℕ) (hH : 2 ≤ H) :
    shannonFinite alwaysInspect H < shannonFinite alwaysPlay H := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hH
  clear hH
  induction n with
  | zero =>
    have hh := shannon_first_tick_gap
    simp [shannonFinite, sum_range_succ, shannonStage_alwaysInspect,
      shannonStage_alwaysPlay, shannonInspectValue, shannonPlayValue] at *
    linarith
  | succ n ih =>
    simp only [Nat.add_succ, shannonFinite, sum_range_succ] at *
    have hp := shannonInspectValue_le_play (n+1)
    rw [← shannonStage_alwaysInspect, ← shannonStage_alwaysPlay] at hp
    convert add_lt_add_of_lt_of_le ih hp using 1 <;> congr 2 <;> omega

theorem squareFinite_inspect_lt_play (H : ℕ) (hH : 3 ≤ H) :
    squareFinite alwaysInspect H < squareFinite alwaysPlay H := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hH
  clear hH
  induction n with
  | zero =>
    norm_num [squareFinite, sum_range_succ, squareStage_alwaysInspect,
      squareStage_alwaysPlay, squareInspectValue, squarePlayValue, alarmMass,
      AlarmPanelVariance.silentMass_eq]
  | succ n ih =>
    simp only [Nat.add_succ, squareFinite, sum_range_succ] at *
    have hp := squareInspectValue_le_play (n+2)
    rw [← squareStage_alwaysInspect, ← squareStage_alwaysPlay] at hp
    convert add_lt_add_of_lt_of_le ih hp using 1 <;> congr 2 <;> omega

/-- An affine root mixture with a strictly larger PLAY column has exactly the
policies that never inspect as its maximizers. -/
theorem mixture_maximizer_iff (f : ValidCausalPolicy Action Observation → ℝ)
    (hmix : ∀ π, f π = inspectionProbability π.1 * f alwaysInspect +
      (1-inspectionProbability π.1) * f alwaysPlay)
    (hlt : f alwaysInspect < f alwaysPlay) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, f ρ ≤ f π) ↔ inspectionProbability π.1 = 0 := by
  constructor
  · intro h
    have hp := h alwaysPlay
    rw [hmix π] at hp
    have hs := inspectionProbability_nonneg π.1 π.2
    nlinarith
  · intro hs ρ
    rw [hmix ρ, hmix π, hs]
    have hr := inspectionProbability_nonneg ρ.1 ρ.2
    nlinarith

theorem shannonFinite_maximizer_iff (H : ℕ) (hH : 2 ≤ H)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, shannonFinite ρ H ≤ shannonFinite π H) ↔ inspectionProbability π.1 = 0 :=
  mixture_maximizer_iff (fun π => shannonFinite π H) (fun π => shannonFinite_mixture π H)
    (shannonFinite_inspect_lt_play H hH) π

theorem squareFinite_maximizer_iff (H : ℕ) (hH : 3 ≤ H)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, squareFinite ρ H ≤ squareFinite π H) ↔ inspectionProbability π.1 = 0 :=
  mixture_maximizer_iff (fun π => squareFinite π H) (fun π => squareFinite_mixture π H)
    (squareFinite_inspect_lt_play H hH) π

/-- The startup advantage of inspection governs the short horizons. -/
theorem mixture_inspect_maximizer_iff (f : ValidCausalPolicy Action Observation → ℝ)
    (hmix : ∀ π, f π = inspectionProbability π.1 * f alwaysInspect +
      (1-inspectionProbability π.1) * f alwaysPlay)
    (hlt : f alwaysPlay < f alwaysInspect) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, f ρ ≤ f π) ↔ inspectionProbability π.1 = 1 := by
  constructor
  · intro h
    have hp := h alwaysInspect
    rw [hmix π] at hp
    have hs := inspectionProbability_le_one π.1 π.2
    nlinarith
  · intro hs ρ
    rw [hmix ρ, hmix π, hs]
    have hr := inspectionProbability_le_one ρ.1 ρ.2
    nlinarith

theorem shannonFinite_one_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, shannonFinite ρ 1 ≤ shannonFinite π 1) ↔ inspectionProbability π.1 = 1 := by
  apply mixture_inspect_maximizer_iff _ (fun π => shannonFinite_mixture π 1)
  norm_num [shannonFinite, shannonStage_alwaysInspect, shannonStage_alwaysPlay,
    shannonInspectValue, shannonPlayValue]

theorem squareFinite_one_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, squareFinite ρ 1 ≤ squareFinite π 1) ↔ inspectionProbability π.1 = 1 := by
  apply mixture_inspect_maximizer_iff _ (fun π => squareFinite_mixture π 1)
  norm_num [squareFinite, squareStage_alwaysInspect, squareStage_alwaysPlay,
    squareInspectValue, squarePlayValue]

theorem squareFinite_two_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, squareFinite ρ 2 ≤ squareFinite π 2) ↔ inspectionProbability π.1 = 1 := by
  apply mixture_inspect_maximizer_iff _ (fun π => squareFinite_mixture π 2)
  norm_num [squareFinite, sum_range_succ, squareStage_alwaysInspect, squareStage_alwaysPlay,
    squareInspectValue, squarePlayValue, alarmMass, AlarmPanelVariance.silentMass_eq]

/-- Closed finite Shannon return under certain inspection. -/
theorem shannonFinite_inspect_closed (n : ℕ) :
    shannonFinite alwaysInspect (n+1) = 2 - (1/2:ℝ)^n := by
  induction n with
  | zero => norm_num [shannonFinite, shannonStage_alwaysInspect, shannonInspectValue]
  | succ n ih =>
    unfold shannonFinite at *
    rw [sum_range_succ, ih, shannonStage_alwaysInspect]
    simp only [shannonInspectValue, alarmMass, pow_add, pow_one, pow_two]
    ring

/-- Closed finite Square return under certain inspection. -/
theorem squareFinite_inspect_closed (n : ℕ) :
    squareFinite alwaysInspect (n+1) = -(n:ℝ) - (1/2:ℝ)^(n+1) := by
  induction n with
  | zero => norm_num [squareFinite, squareStage_alwaysInspect, squareInspectValue]
  | succ n ih =>
    unfold squareFinite at *
    rw [sum_range_succ, ih, squareStage_alwaysInspect]
    simp only [squareInspectValue, alarmMass, pow_add, pow_one, pow_two, Nat.cast_add,
      Nat.cast_one]
    ring

/-- Nonnegative extended total, which records divergence as positive infinity. -/
def shannonComplete (π : ValidCausalPolicy Action Observation) : ENNReal :=
  ∑' t, ENNReal.ofReal (shannonStage π t)

theorem shannonInspect_summable : Summable shannonInspectValue := by
  apply (summable_nat_add_iff 1).mp
  simpa only [shannonInspectValue] using AlarmPanelVariance.alarmMass_summable.mul_left 2

theorem shannonInspect_sum : (∑' t, shannonInspectValue t) = 2 := by
  rw [shannonInspect_summable.tsum_eq_zero_add]
  simp only [shannonInspectValue, tsum_mul_left, AlarmPanelVariance.alarmMass_sum]
  norm_num

theorem shannonComplete_inspect (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 = 1) : shannonComplete π = 2 := by
  have he (t : ℕ) : shannonStage π t = shannonInspectValue t := by
    rw [shannonStage_mixture, hs]; ring
  have hn (t : ℕ) : 0 ≤ shannonInspectValue t := by
    rw [← shannonStage_alwaysInspect]; exact shannonStage_nonneg _ _
  unfold shannonComplete
  simp only [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn shannonInspect_summable, shannonInspect_sum]
  norm_num

/-- Positive PLAY probability supplies a linear lower bound on total surprise. -/
theorem shannonFinite_lower (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    (n:ℝ) * (1-inspectionProbability π.1) ≤ shannonFinite π (n+1) := by
  induction n with
  | zero => simpa [shannonFinite] using shannonStage_nonneg π 0
  | succ n ih =>
    have hstage : 1-inspectionProbability π.1 ≤ shannonStage π (n+1) := by
      have hi : 0 ≤ shannonInspectValue (n+1) := by
        rw [← shannonStage_alwaysInspect]; exact shannonStage_nonneg _ _
      have hp := shannon_play_sub_inspect_tick n
      have hs := inspectionProbability_nonneg π.1 π.2
      have hsp := inspectionProbability_le_one π.1 π.2
      rw [shannonStage_mixture]
      nlinarith [mul_nonneg hs hi,
        mul_nonneg (sub_nonneg.mpr hsp) (show 0 ≤ shannonPlayValue (n+1)-1 by linarith)]
    unfold shannonFinite at *
    rw [sum_range_succ]
    push_cast
    nlinarith

theorem shannonFinite_le_complete (π : ValidCausalPolicy Action Observation) (H : ℕ) :
    ENNReal.ofReal (shannonFinite π H) ≤ shannonComplete π := by
  rw [shannonFinite, ENNReal.ofReal_sum_of_nonneg (fun t _ => shannonStage_nonneg π t)]
  exact ENNReal.sum_le_tsum _

theorem shannonComplete_play (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 < 1) : shannonComplete π = ⊤ := by
  have hc : 0 < 1-inspectionProbability π.1 := by linarith
  by_contra hne
  obtain ⟨n, hn⟩ := exists_nat_gt ((shannonComplete π).toReal / (1-inspectionProbability π.1))
  have hu := (ENNReal.ofReal_le_iff_le_toReal hne).mp (shannonFinite_le_complete π (n+1))
  have hl := shannonFinite_lower π n
  have hn' := (div_lt_iff₀ hc).mp hn
  linarith

theorem shannonComplete_top_iff (π : ValidCausalPolicy Action Observation) :
    shannonComplete π = ⊤ ↔ inspectionProbability π.1 < 1 := by
  constructor
  · intro ht
    by_contra hs
    have hs' := le_antisymm (inspectionProbability_le_one π.1 π.2) (le_of_not_gt hs)
    rw [shannonComplete_inspect π hs'] at ht
    norm_num at ht
  · exact shannonComplete_play π

theorem shannonComplete_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, shannonComplete ρ ≤ shannonComplete π) ↔ inspectionProbability π.1 < 1 := by
  constructor
  · intro h
    have hp := shannonComplete_play alwaysPlay (by rw [alwaysPlay_inspectionProbability]; norm_num)
    have ht : shannonComplete π = ⊤ := top_le_iff.mp (hp ▸ h alwaysPlay)
    exact (shannonComplete_top_iff π).mp ht
  · intro hs ρ
    rw [shannonComplete_play π hs]
    exact le_top

/-- A uniform negative bound suffices to establish every complete Square return. -/
theorem squareStage_le_neg_quarter (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    squareStage π t ≤ -1/4 := by
  have hs := inspectionProbability_nonneg π.1 π.2
  have hs1 := inspectionProbability_le_one π.1 π.2
  have hi : squareInspectValue t ≤ -1/4 := by
    cases t with
    | zero => norm_num [squareInspectValue]
    | succ k => simp only [squareInspectValue]; linarith [AlarmPanelVariance.alarmMass_le_quarter k]
  have hp : squarePlayValue t ≤ -1/4 := by
    cases t with
    | zero => norm_num [squarePlayValue]
    | succ k =>
      simp only [squarePlayValue]
      have ha := AlarmPanelVariance.alarmMass_le_quarter k
      have hn := (AlarmPanelVariance.alarmMass_pos k).le
      have hh := hazard_nonneg k
      nlinarith [mul_nonneg hn hh]
  rw [squareStage_mixture]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hi),
    mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hp)]

theorem squareFinite_upper (π : ValidCausalPolicy Action Observation) (H : ℕ) :
    squareFinite π H ≤ -(H:ℝ)/4 := by
  calc
    squareFinite π H ≤ ∑ _t ∈ range H, (-1/4:ℝ) :=
      Finset.sum_le_sum (fun t _ => squareStage_le_neg_quarter π t)
    _ = -(H:ℝ)/4 := by simp; ring

theorem squareFinite_antitone (π : ValidCausalPolicy Action Observation) :
    Antitone (squareFinite π) := by
  apply antitone_nat_of_succ_le
  intro H
  unfold squareFinite
  rw [sum_range_succ]
  linarith [squareStage_nonpos π H]

theorem squareFinite_tendsto_atBot (π : ValidCausalPolicy Action Observation) :
    Filter.Tendsto (squareFinite π) Filter.atTop Filter.atBot := by
  apply Filter.tendsto_atBot.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (-4*b)
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun H hH => ?_⟩
  have hNH : (N:ℝ) ≤ H := by exact_mod_cast hH
  linarith [squareFinite_upper π H]

/-- Square partial returns decrease, so their extended total is their infimum. -/
def squareComplete (π : ValidCausalPolicy Action Observation) : EReal :=
  ⨅ H : ℕ, (squareFinite π H : EReal)

theorem squareComplete_eq_bot (π : ValidCausalPolicy Action Observation) :
    squareComplete π = ⊥ := by
  by_contra hne
  obtain ⟨H, hH⟩ := exists_nat_gt (-4*(squareComplete π).toReal)
  have he : (squareComplete π).toReal ≤ squareFinite π H := by
    apply EReal.coe_le_coe_iff.mp
    exact (EReal.coe_toReal_le hne).trans (iInf_le (fun H : ℕ => (squareFinite π H : EReal)) H)
  have hu := squareFinite_upper π H
  linarith

/-- Complete Square ties every policy at negative infinity. -/
theorem squareComplete_all_maximize (π ρ : ValidCausalPolicy Action Observation) :
    squareComplete ρ ≤ squareComplete π := by
  rw [squareComplete_eq_bot ρ, squareComplete_eq_bot π]

/-- Expected one-hot squared error `‖e_O - q‖²` of the newest raw observation. -/
def squaredErrorStage (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  stage oneHotSquaredError π t

/-- In expectation, Square is one-hot squared prediction error minus one. -/
theorem squareStage_eq_squaredErrorStage (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    squareStage π t = squaredErrorStage π t - 1 := by
  rw [squareStage_eq, squaredErrorStage, stage_eq]
  have he (u : Trace t) (a : Action) :
      ∑ o, predictive π t u a o * oneHotSquaredError (predictive π t u a) o =
        (-∑ o, predictive π t u a o ^ 2) + 1 := by
    have hx := expectedOneHotSquaredError_self _ (predictive_valid π t u a)
    unfold expectedOneHotSquaredError at hx
    rw [hx]; ring
  have hrow (u : Trace t) :
      ∑ a, π.1 (List.ofFn u) a * ((-∑ o, predictive π t u a o ^ 2) + 1) =
        (∑ a, π.1 (List.ofFn u) a * (-∑ o, predictive π t u a o ^ 2)) + 1 := by
    simp only [mul_add, mul_one, sum_add_distrib, (π.2 _).2]
  simp only [he]
  simp only [hrow]
  simp only [mul_add, mul_one, sum_add_distrib, (mass_valid π t).2]
  ring


def squaredErrorFinite (π : ValidCausalPolicy Action Observation) (H : ℕ) : ℝ :=
  ∑ t ∈ range H, squaredErrorStage π t

theorem squareFinite_eq_squaredErrorFinite (π : ValidCausalPolicy Action Observation)
    (H : ℕ) : squareFinite π H = squaredErrorFinite π H - H := by
  simp [squareFinite, squaredErrorFinite, squareStage_eq_squaredErrorStage,
    Finset.sum_sub_distrib]

end IdExp.PairedAlarm.Predictive
