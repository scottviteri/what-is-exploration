import Formal.AlarmPanelVariantFinite

/-!
# Three-observation objectives on the intervention variants

The third observation is the first monitor tick. Under the prior, its
predictive law depends only on the startup record: after inspection the
revealed bit decides it (never: label 0 surely; finite: pulse now with
conditional probability 1/2), and without inspection the pulse-now
probability is the prior mass 1/4. Exact conditional surprisal and ideal
one-hot prediction error over three observations are affine in the startup
inspection probability `s` with strictly negative slope in every valid
variant, because the inspection bit makes the first monitor reading more
predictable. In particular, with the panel retained the two-step objectives
tie while the three-step objectives still have every maximizer at `s = 0`.
-/

namespace IdExp.AlarmPanelPrior
open MeasureTheory Set

/-- Integrands constant on alarm times at least one reduce to three atoms. -/
theorem integral_none_zero_tail (f : World → ℝ)
    (hf : ∀ k : ℕ, f (some (k+1)) = f (some 1)) :
    (∫ θ, f θ ∂prior) =
      (1/2 : ℝ) * f none + (1/4 : ℝ) * f (some 0) + (1/4 : ℝ) * f (some 1) := by
  have he : f = fun θ => f (some 1) +
      ({none} : Set World).indicator (fun _ => f none - f (some 1)) θ +
      ({some 0} : Set World).indicator (fun _ => f (some 0) - f (some 1)) θ := by
    funext θ
    cases θ with
    | none => simp
    | some k =>
      cases k with
      | zero => simp
      | succ k => simp [hf k]
  conv_lhs => rw [he]
  rw [integral_add ((integrable_const _).add
      ((integrable_const _).indicator (measurableSet_singleton _)))
      ((integrable_const _).indicator (measurableSet_singleton _)),
    integral_add (integrable_const _)
      ((integrable_const _).indicator (measurableSet_singleton _)),
    integral_indicator_const _ (measurableSet_singleton _),
    integral_indicator_const _ (measurableSet_singleton _)]
  simp only [integral_const, smul_eq_mul]
  have hu : prior.real Set.univ = 1 := by simp [prior]
  rw [hu, waitingQueryGeometricPrior_none, waitingQueryGeometricPrior_some]
  norm_num
  ring

end IdExp.AlarmPanelPrior

namespace IdExp.AlarmPanel
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

variable (v : Variant)

/-- Pulse-now law of a monitor tick: label 1 with probability `q`, else label 0. -/
def pulseLaw (q : ℝ) (o : Observation) : ℝ := q * pointDist 1 o + (1 - q) * pointDist 0 o

theorem pulseLaw_sum (q : ℝ) : ∑ o, pulseLaw q o = 1 := by
  unfold pulseLaw
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, (pointDist_valid 1).2, (pointDist_valid 0).2]
  ring

/-- Conditional pulse-now probability at the first monitor tick, given the
startup record: revealed bit after inspection, prior mass otherwise. -/
def thirdQ (x : Action × Observation) : ℝ :=
  if x.1 = inspect then (if 2 ≤ x.2.val then 2⁻¹ else 0) else 4⁻¹

theorem monitorLabel_none (k : ℕ) : monitorLabel none k = 0 := by simp [monitorLabel]
theorem monitorLabel_some_self (k : ℕ) : monitorLabel (some k) k = 1 := by simp [monitorLabel]
theorem monitorLabel_some_ne {j k : ℕ} (h : j ≠ k) : monitorLabel (some j) k = 0 := by
  simp [monitorLabel, h]

theorem responseV_first_monitor (θ : World) (x y : Action × Observation) (c : Action)
    (o : Observation) : responseV v θ [x,y] c o = pointDist (monitorLabel θ 0) o := by
  rw [responseV_monitor v θ [x,y] c o (by simp) (by simp)]
  simp

/-- Law of the three retained action/observation pairs under the prior. -/
def threeStepMassV (π : ValidCausalPolicy Action Observation)
    (x y z : Action × Observation) : ℝ :=
  twoStepMassV v π x y * π.1 [x,y] z.1 * pulseLaw (thirdQ x) z.2

/-- The proposed three-step law is the actual countable-prior predictive record law. -/
theorem threeStepMassV_eq (π : ValidCausalPolicy Action Observation)
    (x y z : Action × Observation) :
    (∫ θ, causalTraceProb π.1 (responseV v θ) [x,y,z] ∂AlarmPanelPrior.prior) =
      threeStepMassV v π x y z := by
  rw [AlarmPanelPrior.integral_none_zero_tail _ (by
    intro k
    simp [causalTraceProb, causalTraceProbFrom, secondLawV_response, responseV_root,
      responseV_first_monitor, monitorLabel_none, monitorLabel_some_ne (Nat.succ_ne_zero k),
      monitorLabel_some_ne (Nat.succ_ne_zero 0)])]
  simp only [causalTraceProb, causalTraceProbFrom, List.nil_append, secondLawV_response,
    mul_one, responseV_root, responseV_first_monitor]
  rcases x with ⟨a,o⟩
  fin_cases a <;> fin_cases o <;>
    norm_num [threeStepMassV, twoStepMassV, thirdQ, pulseLaw, inspect, pairDistP, startupDistP,
      colorMass, responseV_first_monitor, monitorLabel_none, monitorLabel_some_self,
      monitorLabel_some_ne (Nat.succ_ne_zero 0), Fin.ext_iff] <;> ring

/-- Expected conditional score of three observations, conditioned on actions. -/
def threeStepScoreV (π : ValidCausalPolicy Action Observation)
    (g : (Observation → ℝ) → ℝ) : ℝ :=
  conditionalScoreV v π g +
    ∑ x, ∑ y, twoStepMassV v π x y * ∑ c, π.1 [x,y] c * g (pulseLaw (thirdQ x))

theorem third_inspect_sum (p : ℝ) (g : (Observation → ℝ) → ℝ) :
    (∑ o : Observation, startupDistP p o * g (pulseLaw (thirdQ ((0 : Action), o)))) =
      (g (pulseLaw 0) + g (pulseLaw 2⁻¹)) / 2 := by
  norm_num [thirdQ, startupDistP, colorMass, Fin.sum_univ_succ, inspect] <;> ring

theorem third_play_sum (p : ℝ) (g : (Observation → ℝ) → ℝ) (a : Action) (ha : a ≠ 0) :
    (∑ o : Observation, startupDistP p o * g (pulseLaw (thirdQ (a, o)))) =
      g (pulseLaw 4⁻¹) := by
  simp only [thirdQ, inspect, ha, if_false]
  rw [← sum_mul, startupDistP_sum, one_mul]

theorem threeStepScoreV_eq (π : ValidCausalPolicy Action Observation)
    (g : (Observation → ℝ) → ℝ) :
    threeStepScoreV v π g = conditionalScoreV v π g +
      π.1 [] 0 * ((g (pulseLaw 0) + g (pulseLaw 2⁻¹)) / 2) +
      (1 - π.1 [] 0) * g (pulseLaw 4⁻¹) := by
  have hb : ∀ (x y : Action × Observation),
      (∑ c, π.1 [x,y] c * g (pulseLaw (thirdQ x))) = g (pulseLaw (thirdQ x)) := by
    intro x y; rw [← sum_mul, (π.2 _).2, one_mul]
  simp only [threeStepScoreV, hb, ← sum_mul, twoStepMassV_fst]
  rw [Fintype.sum_prod_type]
  have hx : ∀ a : Action, (∑ o : Observation,
      π.1 [] a * startupDistP v.p o * g (pulseLaw (thirdQ (a, o)))) =
      π.1 [] a * ∑ o : Observation, startupDistP v.p o * g (pulseLaw (thirdQ (a, o))) := by
    intro a; rw [mul_sum]; apply sum_congr rfl; intro o _; ring
  simp_rw [hx]
  rw [Fin.sum_univ_three, third_inspect_sum, third_play_sum _ _ 1 (by decide),
    third_play_sum _ _ 2 (by decide)]
  have hroot := (π.2 []).2
  rw [Fin.sum_univ_three] at hroot
  linear_combination (g (pulseLaw 4⁻¹)) * hroot

/-! ## Scores of the pulse law -/

theorem pulseLaw_entropy (q : ℝ) : ent (pulseLaw q) = Real.binEntropy q := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [ent, pulseLaw, pointDist, Fin.sum_univ_succ] <;>
    (try norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]) <;>
    (try norm_num) <;> ring

theorem pulseLaw_oneHotRisk (q : ℝ) : oneHotRisk (pulseLaw q) = 2 * q * (1 - q) := by
  rw [oneHotRisk_eq_one_sub_sum_sq _ (pulseLaw_sum q)]
  norm_num [pulseLaw, pointDist, Fin.sum_univ_succ] <;>
    (try norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]) <;>
    (try norm_num) <;> ring

theorem binEntropy_quarter :
    Real.binEntropy 4⁻¹ = Real.log 2 / 2 + 3/4 * Real.log (4/3) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  unfold Real.binEntropy
  rw [inv_inv]
  have h34 : (1 - (4:ℝ)⁻¹)⁻¹ = 4/3 := by norm_num
  have h34' : (1 - (4:ℝ)⁻¹) = 3/4 := by norm_num
  rw [h34, h34', h4]
  ring

theorem half_log_two_lt_binEntropy_quarter : Real.log 2 / 2 < Real.binEntropy 4⁻¹ := by
  have := Real.log_pos (show (1:ℝ) < 4/3 by norm_num)
  rw [binEntropy_quarter]
  linarith

/-! ## Three-step surprisal -/

/-- Expected exact conditional predictive surprisal of the first three
observations, in nats. -/
def surprisalThreeV (π : ValidCausalPolicy Action Observation) : ℝ :=
  threeStepScoreV v π ent

theorem surprisalThreeV_eq (π : ValidCausalPolicy Action Observation) :
    surprisalThreeV v π = surprisalObjectiveV v π +
      π.1 [] 0 * (Real.log 2 / 2) + (1 - π.1 [] 0) * Real.binEntropy 4⁻¹ := by
  rw [surprisalThreeV, threeStepScoreV_eq, pulseLaw_entropy, pulseLaw_entropy, pulseLaw_entropy,
    Real.binEntropy_two_inv, (Real.binEntropy_eq_zero).2 (Or.inl rfl)]
  unfold surprisalObjectiveV
  ring

/-- In every valid variant, every three-step surprisal maximizer skips inspection. -/
theorem surprisalThreeV_maximizer_iff (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, surprisalThreeV v ρ ≤ surprisalThreeV v π) ↔ π.1 [] 0 = 0 := by
  have hgap := half_log_two_lt_binEntropy_quarter
  have hi : (if v.retain = false then 0 else Real.binEntropy v.p) ≤ Real.binEntropy v.p := by
    split_ifs
    · exact Real.binEntropy_nonneg hv.1 hv.2
    · exact le_rfl
  have he : ∀ σ : ValidCausalPolicy Action Observation, surprisalThreeV v σ =
      Real.log 2 + Real.binEntropy v.p +
      σ.1 [] 0 * (if v.retain = false then 0 else Real.binEntropy v.p) +
      (1 - σ.1 [] 0) * Real.binEntropy v.p +
      σ.1 [] 0 * (Real.log 2 / 2) + (1 - σ.1 [] 0) * Real.binEntropy 4⁻¹ := by
    intro σ; rw [surprisalThreeV_eq, surprisalObjectiveV_eq]
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [he, he, noveltyPolicy_root] at hh
    have hs := (π.2 []).1 0
    nlinarith [mul_nonneg hs (sub_nonneg.2 hi), mul_nonneg hs (sub_nonneg.2 hgap.le)]
  · intro h ρ
    rw [he, he, h]
    have hs := (ρ.2 []).1 0
    nlinarith [mul_nonneg hs (sub_nonneg.2 hi), mul_nonneg hs (sub_nonneg.2 hgap.le)]

/-- Panel retained: two-step surprisal ties, three-step surprisal still
strictly prefers skipping inspection, with regret `s` times the gap
between the pulse entropy and half a bit. -/
theorem retained_surprisalThree_regret (π : ValidCausalPolicy Action Observation) :
    surprisalThreeV Variant.retained noveltyPolicy - surprisalThreeV Variant.retained π =
      π.1 [] 0 * (Real.binEntropy 4⁻¹ - Real.log 2 / 2) := by
  rw [surprisalThreeV_eq, surprisalThreeV_eq, retained_surprisal_constant,
    retained_surprisal_constant, noveltyPolicy_root]
  ring

theorem retained_surprisalThree_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, surprisalThreeV Variant.retained ρ ≤ surprisalThreeV Variant.retained π) ↔
      π.1 [] 0 = 0 :=
  surprisalThreeV_maximizer_iff Variant.retained Variant.retained_valid π

/-! ## Three-step prediction error -/

def predictionErrorThreeV (π : ValidCausalPolicy Action Observation) : ℝ :=
  threeStepScoreV v π oneHotRisk

theorem predictionErrorThreeV_eq (π : ValidCausalPolicy Action Observation) :
    predictionErrorThreeV v π = predictionErrorObjectiveV v π +
      π.1 [] 0 * (1/4) + (1 - π.1 [] 0) * (3/8) := by
  rw [predictionErrorThreeV, threeStepScoreV_eq, pulseLaw_oneHotRisk, pulseLaw_oneHotRisk,
    pulseLaw_oneHotRisk]
  unfold predictionErrorObjectiveV
  ring

theorem predictionErrorThreeV_maximizer_iff (hv : v.Valid)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, predictionErrorThreeV v ρ ≤ predictionErrorThreeV v π) ↔ π.1 [] 0 = 0 := by
  have hi : (if v.retain = false then 0 else 2 * v.p * (1 - v.p)) ≤ 2 * v.p * (1 - v.p) := by
    split_ifs
    · have := hv.1; have := hv.2; nlinarith
    · exact le_rfl
  have he : ∀ σ : ValidCausalPolicy Action Observation, predictionErrorThreeV v σ =
      1 - (v.p^2 + (1-v.p)^2)/2 +
      σ.1 [] 0 * (if v.retain = false then 0 else 2 * v.p * (1 - v.p)) +
      (1 - σ.1 [] 0) * (2 * v.p * (1 - v.p)) +
      σ.1 [] 0 * (1/4) + (1 - σ.1 [] 0) * (3/8) := by
    intro σ; rw [predictionErrorThreeV_eq, predictionErrorObjectiveV_eq]
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [he, he, noveltyPolicy_root] at hh
    have hs := (π.2 []).1 0
    nlinarith [mul_nonneg hs (sub_nonneg.2 hi)]
  · intro h ρ
    rw [he, he, h]
    have hs := (ρ.2 []).1 0
    nlinarith [mul_nonneg hs (sub_nonneg.2 hi)]

theorem retained_predictionErrorThree_regret (π : ValidCausalPolicy Action Observation) :
    predictionErrorThreeV Variant.retained noveltyPolicy -
      predictionErrorThreeV Variant.retained π = π.1 [] 0 * (1/8) := by
  rw [predictionErrorThreeV_eq, predictionErrorThreeV_eq, retained_predictionError_constant,
    retained_predictionError_constant, noveltyPolicy_root]
  ring

theorem retained_predictionErrorThree_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, predictionErrorThreeV Variant.retained ρ ≤ predictionErrorThreeV Variant.retained π) ↔
      π.1 [] 0 = 0 :=
  predictionErrorThreeV_maximizer_iff Variant.retained Variant.retained_valid π

end
end IdExp.AlarmPanel
