import Formal.AlarmPanel
import Formal.AlarmPanelPrior
import Formal.ControlEntropy
import Formal.SurprisalDecomposition

/-!
# Literal two-observation objectives on the alarm/panel interface

All causal policies, including observation-dependent randomized second actions,
are feasible. The two-step prior-predictive law has a uniform startup label;
`twoStepMass_eq` connects it to the actual controlled response under the fair
isSome marginal. The reward horizon is exactly two observations; saying that
there is no alarm-time cutoff means the hypothesis class still contains every
natural alarm delay and infinity. It does not mean an infinite reward horizon.

These retained raw-label calculations have historical/supporting scope
(`claim:alarm-panel-finite-rewards`). `entropyObjective` is empirical observation
entropy, not physical-state occupancy. The selected state-entropy comparison is
in `StateOccupancyEntropy.lean`. The continuing pseudo-count theorem with scoring
horizon T >= 64 is in `AlarmPanelPseudoCountObjective.lean`.
-/
namespace IdExp.AlarmPanel
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The second observation law, after a given startup action. -/
def secondLaw (a b : Action) : Observation → ℝ :=
  if a = 0 then pointDist 0 else pairDist (b == 2)

/-- Full law of both retained action/observation pairs under the prior. -/
def twoStepMass (π : ValidCausalPolicy Action Observation)
    (x y : Action × Observation) : ℝ :=
  π.1 [] x.1 * (1/4) * π.1 [x] y.1 * secondLaw x.1 y.1 y.2

def twoExpectation (π : ValidCausalPolicy Action Observation)
    (f : (Action × Observation) → (Action × Observation) → ℝ) : ℝ :=
  ∑ x, ∑ y, twoStepMass π x y * f x y

theorem secondLaw_valid (a b : Action) : IsDist (secondLaw a b) := by
  by_cases h : a = 0
  · simpa [secondLaw,h] using pointDist_valid (0 : Observation)
  · simpa [secondLaw,h] using pairDist_valid (b == 2)

theorem secondLaw_response (θ : World) (x : Action × Observation) (a : Action) :
    response θ [x] a = secondLaw x.1 a := by
  funext o
  by_cases h : x.1 = 0 <;> simp [response, secondLaw, inspected, inspect, play1, h]

/-- The proposed finite law is the actual countable-prior predictive record law. -/
theorem twoStepMass_eq (π : ValidCausalPolicy Action Observation)
    (x y : Action × Observation) :
    (∫ θ, causalTraceProb π.1 (response θ) [x,y] ∂AlarmPanelPrior.prior) =
      twoStepMass π x y := by
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    simp [causalTraceProb, causalTraceProbFrom, secondLaw_response, response_root])]
  simp only [causalTraceProb, causalTraceProbFrom, List.nil_append,
    secondLaw_response, mul_one, response_root]
  rcases x with ⟨a,o⟩
  fin_cases a <;> fin_cases o <;>
    norm_num [twoStepMass, inspect, pairDist, uniformDist, Fin.ext_iff] <;> ring

/-- Exact causal/prior interpretation of every two-observation payoff used below. -/
theorem twoExpectation_causal (π : ValidCausalPolicy Action Observation)
    (f : (Action × Observation) → (Action × Observation) → ℝ) :
    (∫ θ, (∑ x, ∑ y, causalTraceProb π.1 (response θ) [x,y] * f x y)
      ∂AlarmPanelPrior.prior) = twoExpectation π f := by
  rw [AlarmPanelPrior.integral_none_some _ (by intro k; rfl)]
  simp only [twoExpectation,mul_sum,← sum_add_distrib]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  have he := twoStepMass_eq π x y
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    simp [causalTraceProb,causalTraceProbFrom,secondLaw_response,response_root])] at he
  rw [← he]
  ring

theorem twoStepMass_nonneg (π : ValidCausalPolicy Action Observation)
    (x y : Action × Observation) : 0 ≤ twoStepMass π x y := by
  exact mul_nonneg (mul_nonneg (mul_nonneg ((π.2 []).1 x.1) (by norm_num))
    ((π.2 [x]).1 y.1)) ((secondLaw_valid x.1 y.1).1 y.2)

theorem twoStepMass_fst (π : ValidCausalPolicy Action Observation) (x : Action × Observation) :
    (∑ y, twoStepMass π x y) = π.1 [] x.1 / 4 := by
  simp only [twoStepMass, Fintype.sum_prod_type]
  simp_rw [← mul_sum, (secondLaw_valid _ _).2, mul_one]
  rw [← mul_sum, (π.2 [x]).2]
  ring

theorem twoStepMass_valid (π : ValidCausalPolicy Action Observation) :
    IsDist (fun p : (Action × Observation) × (Action × Observation) =>
      twoStepMass π p.1 p.2) := by
  refine ⟨fun p => twoStepMass_nonneg π p.1 p.2, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [twoStepMass_fst]
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr := (π.2 []).2
  simp only [Fin.sum_univ_three] at hr ⊢
  linarith

theorem twoExpectation_const (π : ValidCausalPolicy Action Observation) (c : ℝ) :
    twoExpectation π (fun _ _ => c) = c := by
  simp only [twoExpectation, ← sum_mul, twoStepMass_fst]
  have hv := (twoStepMass_valid π).2
  rw [Fintype.sum_prod_type] at hv
  simp only [twoStepMass_fst] at hv
  rw [hv, one_mul]

/-- Probability that the two observed labels coincide. -/
def repetition (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectation π (fun x y => if x.2 = y.2 then 1 else 0)

theorem repetition_eq (π : ValidCausalPolicy Action Observation) :
    repetition π = ∑ a, ∑ o, π.1 [] a / 4 *
      ∑ b, π.1 [(a,o)] b * secondLaw a b o := by
  simp only [repetition, twoExpectation, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
  simp only [twoStepMass, sum_ite_eq, mem_univ, if_true]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro o _
  rw [mul_sum]
  apply sum_congr rfl; intro b _
  ring

theorem repetition_nonneg (π : ValidCausalPolicy Action Observation) : 0 ≤ repetition π := by
  unfold repetition twoExpectation
  apply sum_nonneg; intro x _
  apply sum_nonneg; intro y _
  apply mul_nonneg (twoStepMass_nonneg π x y)
  dsimp
  split_ifs <;> norm_num

theorem repetition_inspect_contribution (π : ValidCausalPolicy Action Observation) :
    (∑ o, π.1 [] 0 / 4 * ∑ b, π.1 [(0,o)] b * secondLaw 0 b o) = π.1 [] 0 / 4 := by
  simp only [secondLaw, if_true, pointDist, mul_ite, mul_one, mul_zero]
  simp only [sum_ite_irrel, (π.2 _).2, mul_ite, mul_one, mul_zero, sum_ite_eq,
    mem_univ, if_true]
  simp

theorem repetition_ge_inspect (π : ValidCausalPolicy Action Observation) :
    π.1 [] 0 / 4 ≤ repetition π := by
  rw [repetition_eq, ← repetition_inspect_contribution π]
  apply Finset.single_le_sum (f := fun a : Action => ∑ o, π.1 [] a / 4 *
      ∑ b, π.1 [(a,o)] b * secondLaw a b o) _ (mem_univ 0)
  intro a _
  apply sum_nonneg; intro o _
  apply mul_nonneg (div_nonneg ((π.2 []).1 a) (by norm_num))
  apply sum_nonneg; intro b _
  exact mul_nonneg ((π.2 _).1 b) ((secondLaw_valid a b).1 o)

/-- Root PLAY0; at the next tick select the pair opposite to the first label. -/
def noveltyPolicy : ValidCausalPolicy Action Observation := validDetPolicy fun h =>
  if h = [] then 1 else if (h.headD (1,0)).2.val / 2 = 0 then 2 else 1

theorem noveltyPolicy_repetition : repetition noveltyPolicy = 0 := by
  rw [repetition_eq]
  norm_num [noveltyPolicy, validDetPolicy, detPolicy, secondLaw, pairDist,
    pointDist, Fin.sum_univ_succ]
  norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]
  norm_num

/-- Actual first-visit label reward at two observations. -/
def countObjective (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectation π (fun x y => if x.2 = y.2 then 1 else 2)

theorem countObjective_eq (π : ValidCausalPolicy Action Observation) :
    countObjective π = 2 - repetition π := by
  rw [← twoExpectation_const π 2]
  simp only [countObjective, repetition, twoExpectation, ← sum_sub_distrib]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  split_ifs <;> ring

theorem countObjective_maximum (π : ValidCausalPolicy Action Observation) :
    countObjective π ≤ countObjective noveltyPolicy := by
  rw [countObjective_eq, countObjective_eq, noveltyPolicy_repetition]
  linarith [repetition_nonneg π]

theorem countObjective_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, countObjective ρ ≤ countObjective π) ↔ repetition π = 0 := by
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [countObjective_eq, countObjective_eq, noveltyPolicy_repetition] at hh
    linarith [repetition_nonneg π]
  · intro h ρ
    rw [countObjective_eq, countObjective_eq, h]
    linarith [repetition_nonneg ρ]

theorem countObjective_maximizer_skips_inspection (π : ValidCausalPolicy Action Observation)
    (h : ∀ ρ, countObjective ρ ≤ countObjective π) : π.1 [] 0 = 0 := by
  have hz := (countObjective_maximizer_iff π).mp h
  have hb := repetition_ge_inspect π
  linarith [(π.2 []).1 0]

/-- Empirical frequencies of the two raw observation labels. -/
def empiricalLaw (x y : Action × Observation) (o : Observation) : ℝ :=
  ((if x.2 = o then 1 else 0) + (if y.2 = o then 1 else 0)) / 2

/-- Expected entropy of the empirical frequencies of exactly two raw
observations. This is not entropy of discounted physical-state occupancy. -/
def entropyObjective (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectation π (fun x y => ent (empiricalLaw x y))

theorem empiricalLaw_entropy (x y : Action × Observation) :
    ent (empiricalLaw x y) = (if x.2 = y.2 then 0 else Real.log 2) := by
  rcases x with ⟨a,o⟩; rcases y with ⟨b,p⟩
  fin_cases o <;> fin_cases p <;>
    norm_num [empiricalLaw, ent, Fin.sum_univ_succ, Real.negMulLog, Real.log_div] <;>
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat] <;>
    norm_num [Real.negMulLog, Real.log_div] <;> ring

theorem entropyObjective_eq (π : ValidCausalPolicy Action Observation) :
    entropyObjective π = (1 - repetition π) * Real.log 2 := by
  rw [← twoExpectation_const π 1]
  simp only [entropyObjective, twoExpectation, empiricalLaw_entropy, repetition,
    twoExpectation, ← sum_sub_distrib, sum_mul]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  split_ifs <;> ring

theorem entropyObjective_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, entropyObjective ρ ≤ entropyObjective π) ↔ repetition π = 0 := by
  rw [← countObjective_maximizer_iff π]
  simp only [entropyObjective_eq, countObjective_eq,
    mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
  constructor <;> intro h ρ <;> have := h ρ <;> linarith

/-- The categorical count-one initialization pays 1 initially and either 1
or 1/sqrt(2) on the second visit. -/
def pseudoCountObjective (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectation π (fun x y => if x.2 = y.2 then 1 + 1 / Real.sqrt 2 else 2)

theorem pseudoCountObjective_eq (π : ValidCausalPolicy Action Observation) :
    pseudoCountObjective π = 2 - (1 - 1 / Real.sqrt 2) * repetition π := by
  calc
    _ = twoExpectation π (fun _ _ => 2) - (1 - 1 / Real.sqrt 2) * repetition π := by
      simp only [pseudoCountObjective, repetition, twoExpectation, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      split_ifs <;> ring
    _ = _ := by rw [twoExpectation_const]

theorem pseudoCountObjective_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, pseudoCountObjective ρ ≤ pseudoCountObjective π) ↔ repetition π = 0 := by
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    have hp := Real.sqrt_nonneg (2 : ℝ)
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hpos : 0 < 1 - 1 / Real.sqrt 2 := by
    have := (div_lt_one (by linarith : (0 : ℝ) < Real.sqrt 2)).mpr hs
    linarith
  rw [← countObjective_maximizer_iff π]
  simp only [pseudoCountObjective_eq, countObjective_eq]
  constructor
  · intro h ρ
    have hh := h ρ
    nlinarith
  · intro h ρ
    have hh := h ρ
    nlinarith

/-- Expected conditional score of both observations, conditioned on the
chosen action. The actual root predictive law is uniform by `twoStepMass_eq`;
the second predictive law is world-independent by `secondLaw_response`. -/
def conditionalScore (π : ValidCausalPolicy Action Observation)
    (g : (Observation → ℝ) → ℝ) : ℝ :=
  g uniformDist + ∑ a, ∑ o : Observation, π.1 [] a / 4 *
    ∑ b, π.1 [(a,o)] b * g (secondLaw a b)

theorem conditionalScore_eq (π : ValidCausalPolicy Action Observation)
    (g : (Observation → ℝ) → ℝ) (r i p : ℝ)
    (hr : g uniformDist = r)
    (hs : ∀ a b, g (secondLaw a b) = if a = 0 then i else p) :
    conditionalScore π g = r + π.1 [] 0 * i + (1-π.1 [] 0) * p := by
  simp only [conditionalScore,hr,hs,← sum_mul,(π.2 _).2,one_mul]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hroot := (π.2 []).2
  simp only [Fin.sum_univ_three] at hroot ⊢
  norm_num only [Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.val_ofNat]
  norm_num
  nlinarith [congrArg (fun x : ℝ => x * p) hroot]

theorem uniformDist_entropy : ent uniformDist = 2 * Real.log 2 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  norm_num [ent, uniformDist, Fin.sum_univ_succ,Real.negMulLog,Real.log_div,h4]
  ring

theorem secondLaw_entropy (a b : Action) :
    ent (secondLaw a b) = if a = 0 then 0 else Real.log 2 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [secondLaw,pointDist,pairDist,ent,Fin.sum_univ_succ,
      Real.negMulLog,Real.log_div] <;>
    norm_num only [Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.val_ofNat] <;>
    norm_num [Real.negMulLog,Real.log_div] <;> ring

/-- The expected exact conditional predictive surprisal, in nats. -/
def surprisalObjective (π : ValidCausalPolicy Action Observation) : ℝ := conditionalScore π ent

theorem surprisalObjective_eq (π : ValidCausalPolicy Action Observation) :
    surprisalObjective π = (3-π.1 [] 0) * Real.log 2 := by
  rw [surprisalObjective,conditionalScore_eq π ent _ _ _ uniformDist_entropy secondLaw_entropy]
  ring

/-- Actual squared error of the ideal probability-vector predictor against a
one-hot observation target, averaged over that same predictive distribution. -/
def oneHotRisk (p : Observation → ℝ) : ℝ :=
  ∑ o, p o * ∑ j : Observation, ((if j = o then 1 else 0) - p j)^2

theorem uniformDist_oneHotRisk : oneHotRisk uniformDist = 3/4 := by
  norm_num [oneHotRisk,uniformDist,Fin.sum_univ_succ]
  norm_num only [Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.val_ofNat]
  norm_num

theorem secondLaw_oneHotRisk (a b : Action) :
    oneHotRisk (secondLaw a b) = if a = 0 then 0 else 1/2 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [oneHotRisk,secondLaw,pointDist,pairDist,Fin.sum_univ_succ] <;>
    norm_num only [Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.val_ofNat] <;> norm_num

def predictionErrorObjective (π : ValidCausalPolicy Action Observation) : ℝ :=
  conditionalScore π oneHotRisk

theorem predictionErrorObjective_eq (π : ValidCausalPolicy Action Observation) :
    predictionErrorObjective π = 5/4 - π.1 [] 0/2 := by
  rw [predictionErrorObjective,
    conditionalScore_eq π oneHotRisk _ _ _ uniformDist_oneHotRisk secondLaw_oneHotRisk]
  ring

theorem noveltyPolicy_root : noveltyPolicy.1 [] 0 = 0 := by
  norm_num [noveltyPolicy,validDetPolicy,detPolicy]

theorem surprisalObjective_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, surprisalObjective ρ ≤ surprisalObjective π) ↔ π.1 [] 0 = 0 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [surprisalObjective_eq,surprisalObjective_eq,noveltyPolicy_root] at hh
    nlinarith [(π.2 []).1 0]
  · intro h ρ
    rw [surprisalObjective_eq,surprisalObjective_eq,h]
    nlinarith [(ρ.2 []).1 0]

theorem predictionErrorObjective_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, predictionErrorObjective ρ ≤ predictionErrorObjective π) ↔ π.1 [] 0 = 0 := by
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [predictionErrorObjective_eq,predictionErrorObjective_eq,noveltyPolicy_root] at hh
    linarith [(π.2 []).1 0]
  · intro h ρ
    rw [predictionErrorObjective_eq,predictionErrorObjective_eq,h]
    linarith [(ρ.2 []).1 0]

end
end IdExp.AlarmPanel
