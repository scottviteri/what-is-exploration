import Formal.AlarmPanelVariant
import Formal.AlarmPanelFinite

/-!
# Literal two-observation objectives on the intervention variants

The same finite prior-predictive construction as `AlarmPanelFinite`, for a
variant `v`: the startup label has law `startupDistP v.p` under the prior for
either root action, and the second (panel) label has the world-independent law
`secondLawV v`. Exact conditional predictive surprisal and ideal one-hot
prediction error are affine in the startup inspection probability `s`.

Consequences recorded for the paper's intervention row:

* panel retained, fair colors: both two-step objectives are constant over all
  policies (the strict preference for skipping inspection becomes a tie);
* original panel rule, any color probability strictly between 0 and 1: every
  maximizer of either objective has `s = 0`, with regret exactly `s` times
  the color entropy or `s` times the color variance term.
-/

namespace IdExp.AlarmPanel
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

variable (v : Variant)

/-- The second observation law of a variant, after a given startup action. -/
def secondLawV (a b : Action) : Observation → ℝ :=
  if a = 0 ∧ v.retain = false then pointDist 0 else pairDistP v.p (b == 2)

theorem secondLawV_valid (hv : v.Valid) (a b : Action) : IsDist (secondLawV v a b) := by
  by_cases h : a = 0 ∧ v.retain = false
  · simpa [secondLawV, h] using pointDist_valid (0 : Observation)
  · simpa [secondLawV, h] using pairDistP_valid hv.1 hv.2 (b == 2)

theorem secondLawV_sum (a b : Action) : ∑ o, secondLawV v a b o = 1 := by
  unfold secondLawV
  split_ifs
  · exact (pointDist_valid 0).2
  · exact pairDistP_sum v.p (b == 2)

theorem secondLawV_response (θ : World) (x : Action × Observation) (a : Action) :
    responseV v θ [x] a = secondLawV v x.1 a := by
  funext o
  by_cases h : x.1 = 0 <;> simp [responseV, secondLawV, inspected, inspect, play1, h] <;>
    split_ifs <;> rfl

/-- Full law of both retained action/observation pairs under the prior. -/
def twoStepMassV (π : ValidCausalPolicy Action Observation)
    (x y : Action × Observation) : ℝ :=
  π.1 [] x.1 * startupDistP v.p x.2 * π.1 [x] y.1 * secondLawV v x.1 y.1 y.2

def twoExpectationV (π : ValidCausalPolicy Action Observation)
    (f : (Action × Observation) → (Action × Observation) → ℝ) : ℝ :=
  ∑ x, ∑ y, twoStepMassV v π x y * f x y

/-- The proposed finite law is the actual countable-prior predictive record law. -/
theorem twoStepMassV_eq (π : ValidCausalPolicy Action Observation)
    (x y : Action × Observation) :
    (∫ θ, causalTraceProb π.1 (responseV v θ) [x,y] ∂AlarmPanelPrior.prior) =
      twoStepMassV v π x y := by
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    simp [causalTraceProb, causalTraceProbFrom, secondLawV_response, responseV_root])]
  simp only [causalTraceProb, causalTraceProbFrom, List.nil_append,
    secondLawV_response, mul_one, responseV_root]
  rcases x with ⟨a,o⟩
  fin_cases a <;> fin_cases o <;>
    norm_num [twoStepMassV, inspect, pairDistP, startupDistP, colorMass, Fin.ext_iff] <;> ring

theorem twoExpectationV_causal (π : ValidCausalPolicy Action Observation)
    (f : (Action × Observation) → (Action × Observation) → ℝ) :
    (∫ θ, (∑ x, ∑ y, causalTraceProb π.1 (responseV v θ) [x,y] * f x y)
      ∂AlarmPanelPrior.prior) = twoExpectationV v π f := by
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    simp [causalTraceProb, causalTraceProbFrom, secondLawV_response, responseV_root])]
  simp only [twoExpectationV, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  have he := twoStepMassV_eq v π x y
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    simp [causalTraceProb, causalTraceProbFrom, secondLawV_response, responseV_root])] at he
  rw [← he]
  ring

theorem twoStepMassV_nonneg (hv : v.Valid) (π : ValidCausalPolicy Action Observation)
    (x y : Action × Observation) : 0 ≤ twoStepMassV v π x y :=
  mul_nonneg (mul_nonneg (mul_nonneg ((π.2 []).1 x.1)
    ((startupDistP_valid hv.1 hv.2).1 x.2)) ((π.2 [x]).1 y.1))
    ((secondLawV_valid v hv x.1 y.1).1 y.2)

theorem twoStepMassV_fst (π : ValidCausalPolicy Action Observation) (x : Action × Observation) :
    (∑ y, twoStepMassV v π x y) = π.1 [] x.1 * startupDistP v.p x.2 := by
  simp only [twoStepMassV, Fintype.sum_prod_type]
  simp_rw [← mul_sum, secondLawV_sum, mul_one]
  rw [← mul_sum, (π.2 [x]).2]
  ring

theorem twoStepMassV_valid (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    IsDist (fun p : (Action × Observation) × (Action × Observation) =>
      twoStepMassV v π p.1 p.2) := by
  refine ⟨fun p => twoStepMassV_nonneg v hv π p.1 p.2, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [twoStepMassV_fst]
  rw [Fintype.sum_prod_type]
  simp_rw [← mul_sum, startupDistP_sum, mul_one]
  exact (π.2 []).2

theorem twoExpectationV_const (hv : v.Valid) (π : ValidCausalPolicy Action Observation)
    (c : ℝ) : twoExpectationV v π (fun _ _ => c) = c := by
  simp only [twoExpectationV, ← sum_mul]
  have hv2 := (twoStepMassV_valid v hv π).2
  rw [Fintype.sum_prod_type] at hv2
  rw [hv2, one_mul]

/-- Expected conditional score of both observations, conditioned on the
chosen action, under the variant's prior-predictive laws. -/
def conditionalScoreV (π : ValidCausalPolicy Action Observation)
    (g : (Observation → ℝ) → ℝ) : ℝ :=
  g (startupDistP v.p) + ∑ a, ∑ o : Observation, π.1 [] a * startupDistP v.p o *
    ∑ b, π.1 [(a,o)] b * g (secondLawV v a b)

theorem conditionalScoreV_eq (π : ValidCausalPolicy Action Observation)
    (g : (Observation → ℝ) → ℝ) (r i q : ℝ)
    (hr : g (startupDistP v.p) = r)
    (hs : ∀ a b, g (secondLawV v a b) = if a = 0 then i else q) :
    conditionalScoreV v π g = r + π.1 [] 0 * i + (1-π.1 [] 0) * q := by
  simp only [conditionalScoreV, hr, hs]
  have hb : ∀ (a : Action) (o : Observation),
      (∑ b, π.1 [(a,o)] b * (if a = 0 then i else q)) = if a = 0 then i else q := by
    intro a o
    rw [← sum_mul, (π.2 _).2, one_mul]
  simp_rw [hb]
  have hsum : ∀ a : Action, (∑ o : Observation,
      π.1 [] a * startupDistP v.p o * (if a = 0 then i else q)) =
      π.1 [] a * (if a = 0 then i else q) := by
    intro a
    rw [← sum_mul, ← mul_sum, startupDistP_sum, mul_one]
  simp_rw [hsum]
  have hroot := (π.2 []).2
  simp only [Fin.sum_univ_three] at hroot ⊢
  norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]
  norm_num
  nlinarith [congrArg (fun x : ℝ => x * q) hroot]

/-! ## Entropies of the color laws -/

theorem negMulLog_half_mul (x : ℝ) :
    Real.negMulLog (x / 2) = x / 2 * Real.log 2 + Real.negMulLog x / 2 := by
  rw [show x / 2 = x * (1/2) by ring, Real.negMulLog_mul]
  have h : Real.negMulLog (1/2 : ℝ) = (1/2) * Real.log 2 := by
    simp only [Real.negMulLog, one_div, Real.log_inv]; ring
  rw [h]; ring

theorem pairDistP_entropy (p : ℝ) (b : Bool) : ent (pairDistP p b) = Real.binEntropy p := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  cases b <;> norm_num [ent, pairDistP, colorMass, Fin.sum_univ_succ] <;> ring

theorem startupDistP_entropy (p : ℝ) :
    ent (startupDistP p) = Real.log 2 + Real.binEntropy p := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [ent, startupDistP, colorMass, Fin.sum_univ_succ, negMulLog_half_mul] <;> ring

theorem secondLawV_entropy (a b : Action) :
    ent (secondLawV v a b) = if a = 0 ∧ v.retain = false then 0 else Real.binEntropy v.p := by
  unfold secondLawV
  split_ifs
  · norm_num [ent, pointDist, Fin.sum_univ_succ] <;>
      (try norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]) <;>
      norm_num
  · exact pairDistP_entropy v.p _

/-! ## Surprisal -/

/-- Expected exact conditional predictive surprisal of the first two
observations, in nats. -/
def surprisalObjectiveV (π : ValidCausalPolicy Action Observation) : ℝ :=
  conditionalScoreV v π ent

theorem surprisalObjectiveV_eq (π : ValidCausalPolicy Action Observation) :
    surprisalObjectiveV v π = Real.log 2 + Real.binEntropy v.p +
      π.1 [] 0 * (if v.retain = false then 0 else Real.binEntropy v.p) +
      (1 - π.1 [] 0) * Real.binEntropy v.p := by
  have hs : ∀ a b, ent (secondLawV v a b) =
      if a = 0 then (if v.retain = false then 0 else Real.binEntropy v.p)
      else Real.binEntropy v.p := by
    intro a b
    rw [secondLawV_entropy]
    by_cases ha : a = 0 <;> by_cases hr : v.retain = false <;> simp [ha, hr]
  rw [surprisalObjectiveV, conditionalScoreV_eq v π ent _ _ _ (startupDistP_entropy v.p) hs]

/-- The original variant recovers the original two-step surprisal. -/
theorem surprisalObjectiveV_original (π : ValidCausalPolicy Action Observation) :
    surprisalObjectiveV Variant.original π = surprisalObjective π := by
  rw [surprisalObjectiveV_eq, surprisalObjective_eq, Variant.original_retain, Variant.original_p,
    if_pos rfl, one_div, Real.binEntropy_two_inv]
  ring

/-- Panel retained, fair colors: every policy has the same two-step surprisal. -/
theorem retained_surprisal_constant (π : ValidCausalPolicy Action Observation) :
    surprisalObjectiveV Variant.retained π = 3 * Real.log 2 := by
  rw [surprisalObjectiveV_eq, Variant.retained_retain, Variant.retained_p,
    if_neg (by decide : ¬ (true = false)), one_div, Real.binEntropy_two_inv]
  ring

theorem retained_surprisal_tie (π ρ : ValidCausalPolicy Action Observation) :
    surprisalObjectiveV Variant.retained π = surprisalObjectiveV Variant.retained ρ := by
  rw [retained_surprisal_constant, retained_surprisal_constant]

theorem colored_surprisal_eq (p : ℝ) (π : ValidCausalPolicy Action Observation) :
    surprisalObjectiveV (Variant.colored p) π =
      Real.log 2 + Real.binEntropy p + (1 - π.1 [] 0) * Real.binEntropy p := by
  rw [surprisalObjectiveV_eq, Variant.colored_retain, Variant.colored_p, if_pos rfl]
  ring

/-- Original panel rule, any nondegenerate color: every surprisal maximizer
skips inspection. -/
theorem colored_surprisal_maximizer_iff (p : ℝ) (h0 : 0 < p) (h1 : p < 1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, surprisalObjectiveV (Variant.colored p) ρ ≤ surprisalObjectiveV (Variant.colored p) π)
      ↔ π.1 [] 0 = 0 := by
  have hp : 0 < Real.binEntropy p := Real.binEntropy_pos h0 h1
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [colored_surprisal_eq, colored_surprisal_eq, noveltyPolicy_root] at hh
    nlinarith [(π.2 []).1 0]
  · intro h ρ
    rw [colored_surprisal_eq, colored_surprisal_eq, h]
    nlinarith [(ρ.2 []).1 0]

/-- Surprisal regret is exactly the inspection probability times the color entropy. -/
theorem colored_surprisal_regret (p : ℝ) (π : ValidCausalPolicy Action Observation) :
    surprisalObjectiveV (Variant.colored p) noveltyPolicy -
      surprisalObjectiveV (Variant.colored p) π = π.1 [] 0 * Real.binEntropy p := by
  rw [colored_surprisal_eq, colored_surprisal_eq, noveltyPolicy_root]
  ring

/-! ## Ideal one-hot prediction error -/

/-- For any probability vector, the ideal one-hot risk is one minus the sum of
squared masses. Only the total mass is used. -/
theorem oneHotRisk_eq_one_sub_sum_sq (q : Observation → ℝ) (hq : ∑ j, q j = 1) :
    oneHotRisk q = 1 - ∑ j, q j ^ 2 := by
  have h : ∀ o : Observation, (∑ j : Observation, ((if j = o then 1 else 0) - q j)^2) =
      1 - 2 * q o + ∑ j, q j ^ 2 := by
    intro o
    have e : ∀ j : Observation, ((if j = o then 1 else 0) - q j)^2 =
        (if j = o then 1 - 2 * q j else 0) + q j ^ 2 := by
      intro j; split_ifs <;> ring
    simp only [e, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  unfold oneHotRisk
  simp_rw [h]
  have e2 : ∀ o : Observation, q o * (1 - 2 * q o + ∑ j, q j ^ 2) =
      q o - 2 * q o ^ 2 + q o * ∑ j, q j ^ 2 := by intro o; ring
  simp_rw [e2]
  rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, hq, one_mul, ← mul_sum]
  ring

theorem startupDistP_oneHotRisk (p : ℝ) :
    oneHotRisk (startupDistP p) = 1 - (p^2 + (1-p)^2)/2 := by
  rw [oneHotRisk_eq_one_sub_sum_sq _ (startupDistP_sum p)]
  norm_num [startupDistP, colorMass, Fin.sum_univ_succ] <;> ring

theorem pairDistP_oneHotRisk (p : ℝ) (b : Bool) :
    oneHotRisk (pairDistP p b) = 2 * p * (1 - p) := by
  rw [oneHotRisk_eq_one_sub_sum_sq _ (pairDistP_sum p b)]
  cases b <;> norm_num [pairDistP, colorMass, Fin.sum_univ_succ] <;> ring

theorem secondLawV_oneHotRisk (a b : Action) :
    oneHotRisk (secondLawV v a b) =
      if a = 0 ∧ v.retain = false then 0 else 2 * v.p * (1 - v.p) := by
  unfold secondLawV
  split_ifs
  · norm_num [oneHotRisk, pointDist, Fin.sum_univ_succ] <;>
      (try norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]) <;>
      norm_num
  · exact pairDistP_oneHotRisk v.p _

def predictionErrorObjectiveV (π : ValidCausalPolicy Action Observation) : ℝ :=
  conditionalScoreV v π oneHotRisk

theorem predictionErrorObjectiveV_eq (π : ValidCausalPolicy Action Observation) :
    predictionErrorObjectiveV v π = 1 - (v.p^2 + (1-v.p)^2)/2 +
      π.1 [] 0 * (if v.retain = false then 0 else 2 * v.p * (1 - v.p)) +
      (1 - π.1 [] 0) * (2 * v.p * (1 - v.p)) := by
  have hs : ∀ a b, oneHotRisk (secondLawV v a b) =
      if a = 0 then (if v.retain = false then 0 else 2 * v.p * (1 - v.p))
      else 2 * v.p * (1 - v.p) := by
    intro a b
    rw [secondLawV_oneHotRisk]
    by_cases ha : a = 0 <;> by_cases hr : v.retain = false <;> simp [ha, hr]
  rw [predictionErrorObjectiveV,
    conditionalScoreV_eq v π oneHotRisk _ _ _ (startupDistP_oneHotRisk v.p) hs]

theorem predictionErrorObjectiveV_original (π : ValidCausalPolicy Action Observation) :
    predictionErrorObjectiveV Variant.original π = predictionErrorObjective π := by
  rw [predictionErrorObjectiveV_eq, predictionErrorObjective_eq, Variant.original_retain,
    Variant.original_p, if_pos rfl]
  ring

/-- Panel retained, fair colors: every policy has the same two-step prediction error. -/
theorem retained_predictionError_constant (π : ValidCausalPolicy Action Observation) :
    predictionErrorObjectiveV Variant.retained π = 5/4 := by
  rw [predictionErrorObjectiveV_eq, Variant.retained_retain, Variant.retained_p,
    if_neg (by decide : ¬ (true = false))]
  ring

theorem retained_predictionError_tie (π ρ : ValidCausalPolicy Action Observation) :
    predictionErrorObjectiveV Variant.retained π = predictionErrorObjectiveV Variant.retained ρ := by
  rw [retained_predictionError_constant, retained_predictionError_constant]

theorem colored_predictionError_eq (p : ℝ) (π : ValidCausalPolicy Action Observation) :
    predictionErrorObjectiveV (Variant.colored p) π =
      1 - (p^2 + (1-p)^2)/2 + (1 - π.1 [] 0) * (2 * p * (1 - p)) := by
  rw [predictionErrorObjectiveV_eq, Variant.colored_retain, Variant.colored_p, if_pos rfl]
  ring

theorem colored_predictionError_maximizer_iff (p : ℝ) (h0 : 0 < p) (h1 : p < 1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, predictionErrorObjectiveV (Variant.colored p) ρ ≤
      predictionErrorObjectiveV (Variant.colored p) π) ↔ π.1 [] 0 = 0 := by
  have hp : 0 < 2 * p * (1 - p) := by nlinarith
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [colored_predictionError_eq, colored_predictionError_eq, noveltyPolicy_root] at hh
    nlinarith [(π.2 []).1 0]
  · intro h ρ
    rw [colored_predictionError_eq, colored_predictionError_eq, h]
    nlinarith [(ρ.2 []).1 0]

theorem colored_predictionError_regret (p : ℝ) (π : ValidCausalPolicy Action Observation) :
    predictionErrorObjectiveV (Variant.colored p) noveltyPolicy -
      predictionErrorObjectiveV (Variant.colored p) π = π.1 [] 0 * (2 * p * (1 - p)) := by
  rw [colored_predictionError_eq, colored_predictionError_eq, noveltyPolicy_root]
  ring

end
end IdExp.AlarmPanel

/-! ## Two-step label novelty rows on the variants -/

namespace IdExp.AlarmPanel
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

variable (v : Variant)

/-- Probability that the two observed labels coincide. -/
def repetitionV (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectationV v π (fun x y => if x.2 = y.2 then 1 else 0)

theorem repetitionV_eq (π : ValidCausalPolicy Action Observation) :
    repetitionV v π = ∑ a, ∑ o, π.1 [] a * startupDistP v.p o *
      ∑ b, π.1 [(a,o)] b * secondLawV v a b o := by
  simp only [repetitionV, twoExpectationV, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
  simp only [twoStepMassV, sum_ite_eq, mem_univ, if_true]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro o _
  rw [mul_sum]
  apply sum_congr rfl; intro b _
  ring

theorem repetitionV_nonneg (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    0 ≤ repetitionV v π := by
  unfold repetitionV twoExpectationV
  apply sum_nonneg; intro x _
  apply sum_nonneg; intro y _
  apply mul_nonneg (twoStepMassV_nonneg v hv π x y)
  dsimp
  split_ifs <;> norm_num

/-- Actual first-visit label reward at two observations. -/
def countObjectiveV (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectationV v π (fun x y => if x.2 = y.2 then 1 else 2)

theorem countObjectiveV_eq (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    countObjectiveV v π = 2 - repetitionV v π := by
  rw [← twoExpectationV_const v hv π 2]
  simp only [countObjectiveV, repetitionV, twoExpectationV, ← sum_sub_distrib]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  split_ifs <;> ring

/-- The empirical raw-label entropy of two observations. -/
def entropyObjectiveV (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectationV v π (fun x y => ent (empiricalLaw x y))

theorem entropyObjectiveV_eq (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    entropyObjectiveV v π = (1 - repetitionV v π) * Real.log 2 := by
  rw [← twoExpectationV_const v hv π 1]
  simp only [entropyObjectiveV, twoExpectationV, empiricalLaw_entropy, repetitionV,
    ← sum_sub_distrib, sum_mul]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  split_ifs <;> ring

/-- The categorical count-one pseudo-count bonus at two observations. -/
def pseudoCountObjectiveV (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectationV v π (fun x y => if x.2 = y.2 then 1 + 1 / Real.sqrt 2 else 2)

theorem pseudoCountObjectiveV_eq (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    pseudoCountObjectiveV v π = 2 - (1 - 1 / Real.sqrt 2) * repetitionV v π := by
  calc
    _ = twoExpectationV v π (fun _ _ => 2) - (1 - 1 / Real.sqrt 2) * repetitionV v π := by
      simp only [pseudoCountObjectiveV, repetitionV, twoExpectationV, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      split_ifs <;> ring
    _ = _ := by rw [twoExpectationV_const v hv]

/-- The inspection branch repeats exactly when the panel is disabled and the
startup label is 0; with the panel retained, the opposite pair never repeats. -/
theorem repetitionV_inspect_contribution (π : ValidCausalPolicy Action Observation) :
    (∑ o, π.1 [] 0 * startupDistP v.p o * ∑ b, π.1 [(0,o)] b * secondLawV v 0 b o) =
      if v.retain = false then π.1 [] 0 * ((1 - v.p) / 2)
      else π.1 [] 0 * ∑ o, startupDistP v.p o * ∑ b, π.1 [(0,o)] b * pairDistP v.p (b == 2) o := by
  by_cases hr : v.retain = false
  · simp only [secondLawV, hr, and_true, eq_self_iff_true, if_true, pointDist, mul_ite, mul_one,
      mul_zero]
    simp only [sum_ite_irrel, (π.2 _).2, mul_ite, mul_one, sum_ite_eq, mem_univ, if_true]
    simp [startupDistP, colorMass, Fin.sum_univ_succ] <;> ring
  · simp only [secondLawV, hr, Bool.true_eq_false, and_false, if_false]
    rw [mul_sum]
    apply sum_congr rfl; intro o _
    ring

/-- Original panel rule: inspection contributes at least its forced repetition. -/
theorem repetitionV_ge_inspect_of_retain_false (hv : v.Valid) (hr : v.retain = false)
    (π : ValidCausalPolicy Action Observation) :
    π.1 [] 0 * ((1 - v.p) / 2) ≤ repetitionV v π := by
  rw [repetitionV_eq]
  have hc := repetitionV_inspect_contribution v π
  rw [if_pos hr] at hc
  rw [← hc]
  apply Finset.single_le_sum (f := fun a : Action => ∑ o, π.1 [] a * startupDistP v.p o *
      ∑ b, π.1 [(a,o)] b * secondLawV v a b o) _ (mem_univ 0)
  intro a _
  apply sum_nonneg; intro o _
  apply mul_nonneg (mul_nonneg ((π.2 []).1 a) ((startupDistP_valid hv.1 hv.2).1 o))
  apply sum_nonneg; intro b _
  exact mul_nonneg ((π.2 _).1 b) ((secondLawV_valid v hv a b).1 o)

theorem noveltyPolicyV_repetition : repetitionV v noveltyPolicy = 0 := by
  rw [repetitionV_eq]
  simp only [noveltyPolicy, validDetPolicy, detPolicy]
  norm_num [secondLawV, pairDistP, colorMass, startupDistP, Fin.sum_univ_succ]
  norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]
  norm_num

/-- With the panel retained, inspection followed by the opposite pair never repeats. -/
def inspectNoveltyPolicy : ValidCausalPolicy Action Observation := validDetPolicy fun h =>
  if h = [] then 0 else if (h.headD (0,0)).2.val / 2 = 0 then 2 else 1

theorem inspectNoveltyPolicy_root : inspectNoveltyPolicy.1 [] 0 = 1 := by
  norm_num [inspectNoveltyPolicy, validDetPolicy, detPolicy]

theorem retained_inspectNovelty_repetition : repetitionV Variant.retained inspectNoveltyPolicy = 0 := by
  rw [repetitionV_eq]
  simp only [inspectNoveltyPolicy, validDetPolicy, detPolicy]
  norm_num [secondLawV, pairDistP, colorMass, startupDistP, Variant.retained, Fin.sum_univ_succ]
  norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]
  norm_num

theorem countObjectiveV_maximizer_iff (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, countObjectiveV v ρ ≤ countObjectiveV v π) ↔ repetitionV v π = 0 := by
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [countObjectiveV_eq v hv, countObjectiveV_eq v hv, noveltyPolicyV_repetition] at hh
    linarith [repetitionV_nonneg v hv π]
  · intro h ρ
    rw [countObjectiveV_eq v hv, countObjectiveV_eq v hv, h]
    linarith [repetitionV_nonneg v hv ρ]

theorem entropyObjectiveV_maximizer_iff (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, entropyObjectiveV v ρ ≤ entropyObjectiveV v π) ↔ repetitionV v π = 0 := by
  rw [← countObjectiveV_maximizer_iff v hv π]
  simp only [entropyObjectiveV_eq v hv, countObjectiveV_eq v hv,
    mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
  constructor <;> intro h ρ <;> have := h ρ <;> linarith

theorem pseudoCountObjectiveV_maximizer_iff (hv : v.Valid)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, pseudoCountObjectiveV v ρ ≤ pseudoCountObjectiveV v π) ↔ repetitionV v π = 0 := by
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    have hp := Real.sqrt_nonneg (2 : ℝ)
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hpos : 0 < 1 - 1 / Real.sqrt 2 := by
    have := (div_lt_one (by linarith : (0 : ℝ) < Real.sqrt 2)).mpr hs
    linarith
  rw [← countObjectiveV_maximizer_iff v hv π]
  simp only [pseudoCountObjectiveV_eq v hv, countObjectiveV_eq v hv]
  constructor
  · intro h ρ
    have hh := h ρ
    nlinarith
  · intro h ρ
    have hh := h ρ
    nlinarith

/-- Original panel rule with color `p < 1`: every two-step count, entropy and
pseudo-count maximizer skips inspection. -/
theorem colored_count_maximizer_skips (p : ℝ) (h0 : 0 ≤ p) (h1 : p < 1)
    (π : ValidCausalPolicy Action Observation)
    (h : ∀ ρ, countObjectiveV (Variant.colored p) ρ ≤ countObjectiveV (Variant.colored p) π) :
    π.1 [] 0 = 0 := by
  have hv := Variant.colored_valid p h0 h1.le
  have hz := (countObjectiveV_maximizer_iff _ hv π).mp h
  have hb := repetitionV_ge_inspect_of_retain_false _ hv rfl π
  rw [hz] at hb
  have hs := (π.2 []).1 0
  have hp : 0 < (1 - p) / 2 := by linarith
  simp only [Variant.colored_p] at hb
  nlinarith

/-- Panel retained: the two-step novelty rows have completing and noncompleting
maximizers; both the inspecting and the play novelty policies are optimal. -/
theorem retained_count_both_optimal :
    (∀ ρ, countObjectiveV Variant.retained ρ ≤ countObjectiveV Variant.retained inspectNoveltyPolicy) ∧
    (∀ ρ, countObjectiveV Variant.retained ρ ≤ countObjectiveV Variant.retained noveltyPolicy) ∧
    inspectNoveltyPolicy.1 [] 0 = 1 ∧ noveltyPolicy.1 [] 0 = 0 :=
  ⟨(countObjectiveV_maximizer_iff _ Variant.retained_valid _).mpr retained_inspectNovelty_repetition,
   (countObjectiveV_maximizer_iff _ Variant.retained_valid _).mpr (noveltyPolicyV_repetition _),
   inspectNoveltyPolicy_root, noveltyPolicy_root⟩

/-- Under the original variant the two-step law is the original two-step law. -/
theorem twoStepMassV_original (π : ValidCausalPolicy Action Observation)
    (x y : Action × Observation) : twoStepMassV Variant.original π x y = twoStepMass π x y := by
  by_cases hx : x.1 = 0 <;>
    simp [twoStepMassV, twoStepMass, secondLawV, secondLaw, hx, startupDistP_inv_two,
      pairDistP_inv_two, uniformDist] <;> ring

/-- Under the original variant the two-step count agrees with the original definition. -/
theorem countObjectiveV_original (π : ValidCausalPolicy Action Observation) :
    countObjectiveV Variant.original π = countObjective π := by
  simp only [countObjectiveV, countObjective, twoExpectationV, twoExpectation, twoStepMassV_original]

end
end IdExp.AlarmPanel
