import Formal.FourBitPosterior
import Formal.InformationDeficiencyCalibration

/-! Exact expected returns and permanent deficiency in the finite four-bit
example, with arbitrary history-dependent randomized continuation actions. -/
noncomputable section
namespace IdExp.FourBitPosterior
open Finset ScheduledReveal PosteriorMovement

def fullReward : Kind → ℝ | .hellinger => 3/2 | .absolute => 15/8

theorem stage_root (kind : Kind) (π : Policy) :
    stage kind π 0 = fullProbability π * fullReward kind +
      (1-fullProbability π)*fairReward kind := by
  have he (θ : World) (h : CausalFiniteTrace Action Observation 0) : record π 0 θ h=1 := by
    simp [record, ScheduledReveal.record, causalFiniteExperiment, causalTraceProb,
      causalTraceProbFrom, List.ofFn_zero]
  have hl (h : CausalFiniteTrace Action Observation 0) (a : Action) :
      localReward kind π 0 h a = if a then fullReward kind else fairReward kind := by
    rw [localReward, posterior_root]
    change finiteReward kind prior (fun θ => response θ (List.ofFn h) a) = _
    simp only [List.ofFn_zero]
    exact root_reward kind a
  simp only [stage, he, hl, List.ofFn_zero, one_mul, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte, sum_const, Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one]
  rw [← sum_mul, prior_valid.2, one_mul, probability_false]
  simp [CausalFiniteTrace, fullProbability]

theorem stage_next (kind : Kind) (π : Policy) (n : Fin 2) :
    stage kind π (n.val+1) = (1-fullProbability π)*fairReward kind := by
  have he (θ : World) (h : CausalFiniteTrace Action Observation (n.val+1)) :
      record π (n.val+1) θ h *
        (∑ a, π.1 (List.ofFn h) a * localReward kind π (n.val+1) h a) =
      (record π (n.val+1) θ h -
        if (h 0).1=true then record π (n.val+1) θ h else 0)*fairReward kind := by
    by_cases hh : record π (n.val+1) θ h=0
    · simp [hh]
    · simp only [local_positive kind π n θ h hh, ← sum_mul, (π.2 _).2, one_mul]
      cases hb : (h 0).1 <;> simp [hb]
  simp only [stage, he, ← sum_mul, sum_sub_distrib, (record_valid π _ _).2,
    root_mass signal π.1 π.2, ← sum_mul, prior_valid.2, one_mul]
  rfl

theorem stage_after_three (kind : Kind) (π : Policy) (n : ℕ) (hn : 3 ≤ n) :
    stage kind π n = 0 := by
  unfold stage
  apply sum_eq_zero; intro θ _
  suffices hz : (∑ h : CausalFiniteTrace Action Observation n,
      record π n θ h * ∑ a, π.1 (List.ofFn h) a * localReward kind π n h a)=0 by rw [hz, mul_zero]
  apply sum_eq_zero; intro h _
  by_cases hh : record π n θ h=0
  · simp [hh]
  · have hp := posterior_positive_valid π n θ h hh
    have hl (a : Action) : localReward kind π n h a=0 := by
      have hr : (fun η => response η (List.ofFn h) a) = fun _ (o : Observation) => if o=0 then 1 else 0 := by
        funext η o
        simp only [response, ScheduledReveal.response, List.length_ofFn,
          signal_after_three _ _ _ hn]
      rw [localReward, hr, finiteReward_constant kind _ hp.2]
    simp [hl]

/-- The literal expected source reward is an affine function of the initial
FULL probability; later actions contribute no additional information. -/
theorem objective_eq (kind : Kind) (γ : ℝ) (π : Policy) :
    objective kind γ π = fullProbability π * fullReward kind +
      (1-fullProbability π)*fairReward kind*(1+γ+γ^2) := by
  have he : (∑' n, γ^n*stage kind π n) = ∑ n ∈ range 3, γ^n*stage kind π n := by
    apply tsum_eq_sum
    intro n hn
    rw [stage_after_three kind π n (by simpa only [mem_range, not_lt] using hn), mul_zero]
  rw [objective, he]
  norm_num only [sum_range_succ, sum_range_zero, pow_zero, one_mul, pow_one, zero_add]
  have h1 : stage kind π 1=(1-fullProbability π)*fairReward kind := stage_next kind π (0:Fin 2)
  have h2 : stage kind π 2=(1-fullProbability π)*fairReward kind := stage_next kind π (1:Fin 2)
  rw [stage_root, h1, h2]
  ring

theorem partial_strict_near_one (kind : Kind) (γ : ℝ) (hγ : (9/10:ℝ) ≤ γ) :
    fullReward kind < fairReward kind*(1+γ+γ^2) := by
  have hg : (271/100:ℝ) ≤ 1+γ+γ^2 := by nlinarith [sq_nonneg (γ-9/10)]
  cases kind
  · have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
    have hn := Real.sqrt_nonneg (2:ℝ)
    have hc : (4/7:ℝ) < 2-Real.sqrt 2 := by nlinarith
    simp only [fullReward, fairReward]
    nlinarith [mul_le_mul_of_nonneg_left hg (show 0 ≤ 2-Real.sqrt 2 by linarith)]
  · simp only [fullReward, fairReward]; nlinarith

theorem objective_eq_max_iff (kind : Kind) (γ : ℝ) (hγ : (9/10:ℝ) ≤ γ) (π : Policy) :
    objective kind γ π = fairReward kind*(1+γ+γ^2) ↔ fullProbability π=0 := by
  rw [objective_eq]
  have hg := partial_strict_near_one kind γ hγ
  constructor
  · intro he; nlinarith
  · intro he; simp [he]

theorem objective_le (kind : Kind) (γ : ℝ) (hγ : (9/10:ℝ) ≤ γ) (π : Policy) :
    objective kind γ π ≤ fairReward kind*(1+γ+γ^2) := by
  rw [objective_eq]
  have hg := partial_strict_near_one kind γ hγ
  have hs := (probability_bounds π).1
  nlinarith

/-- Uniform posterior sampling is a total stochastic decoder, including null histories. -/
def decoder (π : Policy) (n : ℕ) := finitePosteriorSamplingRule prior (record π n)
theorem decoder_valid (π : Policy) (n : ℕ) : decoder π n ∈ stochasticRules _ _ :=
  finitePosteriorSamplingRule_valid prior prior_valid _ (record_valid π n)

theorem posterior_self (π : Policy) (n : ℕ) (hn : 3 ≤ n+1) (θ : World)
    (h : CausalFiniteTrace Action Observation (n+1)) (hh : record π (n+1) θ h ≠ 0) :
    posterior π (n+1) h θ = if (h 0).1 then 1 else 1/2 := by
  rw [posterior, posterior_cell signal π.1 n θ h hh]
  cases hb : (h 0).1
  · simp only [cellPosterior, cellSize, agree_after_three _ hn, hb]
    change cellPosterior signal false 3 θ θ = 1/2
    simp [post_three]
  · simp [post_full]

theorem decoder_self (π : Policy) (n : ℕ) (hn : 3 ≤ n+1) (θ : World)
    (h : CausalFiniteTrace Action Observation (n+1)) (hh : record π (n+1) θ h ≠ 0) :
    decoder π (n+1) h θ = if (h 0).1 then 1 else 1/2 := by
  have hm : finiteBayesMass prior (record π (n+1)) h ≠ 0 := by
    intro he
    have hj := finiteBayesPosterior_mul_mass prior _ prior_valid.1
      (fun η u => (record_valid π _ η).1 u) h θ
    change _ * finiteBayesMass prior (record π (n+1)) h = _ at hj
    rw [he, mul_zero] at hj
    exact (mul_ne_zero (prior_pos θ).ne' hh) hj.symm
  simpa only [decoder, finitePosteriorSamplingRule, if_neg hm] using posterior_self π n hn θ h hh

/-- Exact success probability of a decoder of the whole four-bit world. -/
theorem decoder_correct_mass (π : Policy) (n : ℕ) (hn : 3 ≤ n+1) (θ : World) :
    finiteDecisionLaw (record π (n+1)) (decoder π (n+1)) θ θ = (1+fullProbability π)/2 := by
  have he (h : CausalFiniteTrace Action Observation (n+1)) :
      record π (n+1) θ h * decoder π (n+1) h θ =
      (record π (n+1) θ h + if (h 0).1=true then record π (n+1) θ h else 0)/2 := by
    by_cases hh : record π (n+1) θ h=0
    · simp [hh]
    · rw [decoder_self π n hn θ h hh]
      cases hb : (h 0).1 <;> simp [hb] <;> ring
  simp only [finiteDecisionLaw, he, ← sum_div, sum_add_distrib,
    (record_valid π _ θ).2, root_mass signal π.1 π.2, fullProbability]

theorem deficiency_le (π : Policy) (n : ℕ) (hn : 3 ≤ n+1) :
    finiteDeficiency (record π (n+1)) (diracExp (id : World → World)) ≤ (1-fullProbability π)/2 := by
  apply finiteDeficiency_le_of_decoder _ _ (decoder π (n+1)) (decoder_valid π (n+1))
  intro θ
  rw [decodeErr_to_diracExp _ (record_valid π _) _ _ (decoder_valid π _)]
  simp only [id_eq]
  rw [decoder_correct_mass π n hn θ]
  linarith

 theorem pair_agree (n : ℕ) : Agree signal false n (0:World) (8:World) := by
   intro i
   by_cases hi : i.val<3
   · interval_cases hv : i.val <;> norm_num [signal, hv]
   · rw [signal_after_three _ _ _ (by omega), signal_after_three _ _ _ (by omega)]

/-- The two worlds differing only in the fourth bit remain indistinguishable
on every PARTIAL record, however long and however the policy randomizes. -/
theorem deficiency_ge (π : Policy) (n : ℕ) :
    (1-fullProbability π)/2 ≤ finiteDeficiency (record π (n+1)) (diracExp (id : World → World)) := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _ (record_valid π _) (diracExp_valid _))
  rintro c ⟨G,hG,herr⟩
  have h0 := herr (0:World)
  have h8 := herr (8:World)
  rw [decodeErr_to_diracExp _ (record_valid π _) _ _ hG] at h0 h8
  have hb : finiteDecisionLaw (record π (n+1)) G 0 0 +
      finiteDecisionLaw (record π (n+1)) G 8 8 ≤ 1+fullProbability π := by
    unfold finiteDecisionLaw
    rw [← sum_add_distrib]
    calc _ ≤ ∑ h : CausalFiniteTrace Action Observation (n+1),
        (record π (n+1) 0 h + if (h 0).1=true then record π (n+1) 8 h else 0) := by
          apply sum_le_sum; intro h _
          have hn0 := (record_valid π _ 0).1 h
          have hn8 := (record_valid π _ 8).1 h
          by_cases hi : (h 0).1=true
          · rw [if_pos hi]
            nlinarith [stochasticRules_le_one hG h (0:World), stochasticRules_le_one hG h (8:World)]
          · have hf : (h 0).1=false := Bool.eq_false_iff.mpr hi
            have he := row_eq_of_agree signal π.1 n (0:World) 8 h (by rw [hf]; exact pair_agree _)
            change record π (n+1) 0 h = record π (n+1) 8 h at he
            rw [if_neg hi, ← he]
            nlinarith [stochasticRules_add_le_one hG h (show (0:World)≠8 by decide)]
      _ = _ := by rw [sum_add_distrib, (record_valid π _ 0).2, root_mass signal π.1 π.2]; rfl
  simp only [id_eq] at h0 h8
  linarith

theorem deficiency_exact (π : Policy) (n : ℕ) (hn : 3 ≤ n+1) :
    finiteDeficiency (record π (n+1)) (diracExp (id : World → World)) = (1-fullProbability π)/2 :=
  le_antisymm (deficiency_le π n hn) (deficiency_ge π n)

theorem optimum_permanent_deficiency (kind : Kind) (γ : ℝ) (hγ : (9/10:ℝ) ≤ γ) (π : Policy)
    (hopt : objective kind γ π=fairReward kind*(1+γ+γ^2)) (n : ℕ) (hn : 3 ≤ n+1) :
    finiteDeficiency (record π (n+1)) (diracExp (id : World → World)) = 1/2 := by
  rw [deficiency_exact π n hn, (objective_eq_max_iff kind γ hγ π).mp hopt]
  norm_num

end IdExp.FourBitPosterior
