import Formal.ScheduledReveal
import Formal.PosteriorMovement

/-! The finite four-bit environment. FULL reveals the physical world at startup;
PARTIAL reveals its first three bits in successive observations. Both actions
remain legal forever but cannot change the initial mode. The fourth bit is
never observed in PARTIAL. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
namespace IdExp.FourBitPosterior
open Finset ScheduledReveal PosteriorMovement
abbrev World := Fin 16
abbrev Action := Bool
abbrev Observation := Fin 16
abbrev Policy := ValidCausalPolicy Action Observation

def signal (θ : World) (a : Action) (n : ℕ) : Observation :=
  if a then (if n=0 then θ else 0)
  else if n<3 then ⟨(θ.val / 2^n)%2, by have := Nat.mod_lt (θ.val / 2^n) (by decide : 0<2); omega⟩
  else 0
abbrev response := ScheduledReveal.response signal
abbrev record (π : Policy) (n : ℕ) := ScheduledReveal.record signal π.1 n
abbrev prior : World → ℝ := ScheduledReveal.uniform
abbrev posterior (π : Policy) (n : ℕ) := finiteBayesPosterior prior (record π n)
def fullProbability (π : Policy) : ℝ := π.1 [] true

 theorem prior_valid : IsDist prior := by constructor <;> norm_num [prior, uniform, Fin.sum_univ_succ]
 theorem prior_pos (θ : World) : 0 < prior θ := by norm_num [prior, uniform]
 theorem record_valid (π : Policy) (n : ℕ) : IsFiniteExperiment (record π n) :=
   ScheduledReveal.record_valid signal π.1 π.2 n
 theorem probability_bounds (π : Policy) : 0 ≤ fullProbability π ∧ fullProbability π ≤ 1 := by
   exact ⟨(π.2 []).1 true, (single_le_sum (fun b _ => (π.2 []).1 b) (mem_univ true)).trans_eq (π.2 []).2⟩
 theorem probability_false (π : Policy) : π.1 [] false = 1-fullProbability π := by
   have h := (π.2 []).2; simp only [Fintype.sum_bool] at h; unfold fullProbability; linarith
 theorem signal_after_three (θ : World) (a : Action) (n : ℕ) (hn : 3 ≤ n) : signal θ a n = 0 := by
   cases a <;> simp [signal, show ¬ n<3 by omega, show n≠0 by omega]
 theorem agree_full (n : ℕ) (θ η : World) : Agree signal true (n+1) θ η ↔ θ=η := by
   constructor
   · intro h; simpa [signal] using h 0
   · intro h; subst η; intro i; rfl
 theorem agree_partial_one (θ η : World) :
     Agree signal false 1 θ η ↔ θ.val%2=η.val%2 := by
   fin_cases θ <;> fin_cases η <;> decide
 theorem agree_partial_two (θ η : World) :
     Agree signal false 2 θ η ↔ θ.val%4=η.val%4 := by
   fin_cases θ <;> fin_cases η <;> decide
 theorem agree_partial_three (θ η : World) :
     Agree signal false 3 θ η ↔ θ.val%8=η.val%8 := by
   fin_cases θ <;> fin_cases η <;> decide
 theorem agree_after_three (n : ℕ) (hn : 3 ≤ n) (b : Bool) (θ η : World) :
     Agree signal b n θ η ↔ Agree signal b 3 θ η := by
   constructor
   · intro h i; exact h ⟨i.val, by omega⟩
   · intro h i
     by_cases hi : i.val<3
     · exact h ⟨i.val,hi⟩
     · rw [signal_after_three _ _ _ (by omega), signal_after_three _ _ _ (by omega)]

 theorem size_full (n : ℕ) (θ : World) : cellSize signal true (n+1) θ = 1 := by
   simp [cellSize, agree_full]
 theorem size_partial_one (θ : World) : cellSize signal false 1 θ = 8 := by
   have hc : (univ.filter (fun η : World => θ.val%2=η.val%2)).card=8 := by
     fin_cases θ <;> decide
   simpa [cellSize, agree_partial_one] using congrArg (fun x : ℕ => (x:ℝ)) hc
 theorem size_partial_two (θ : World) : cellSize signal false 2 θ = 4 := by
   have hc : (univ.filter (fun η : World => θ.val%4=η.val%4)).card=4 := by
     fin_cases θ <;> decide
   simpa [cellSize, agree_partial_two] using congrArg (fun x : ℕ => (x:ℝ)) hc
 theorem size_partial_three (θ : World) : cellSize signal false 3 θ = 2 := by
   have hc : (univ.filter (fun η : World => θ.val%8=η.val%8)).card=2 := by
     fin_cases θ <;> decide
   simpa [cellSize, agree_partial_three] using congrArg (fun x : ℕ => (x:ℝ)) hc
 theorem post_full (n : ℕ) (θ η : World) :
     cellPosterior signal true (n+1) θ η = if η=θ then 1 else 0 := by
   simp [cellPosterior, size_full, agree_full, eq_comm]
 theorem post_one (θ η : World) : cellPosterior signal false 1 θ η =
     if η.val%2=θ.val%2 then 1/8 else 0 := by
   simp [cellPosterior, size_partial_one, agree_partial_one, eq_comm]
 theorem post_two (θ η : World) : cellPosterior signal false 2 θ η =
     if η.val%4=θ.val%4 then 1/4 else 0 := by
   simp [cellPosterior, size_partial_two, agree_partial_two, eq_comm]
 theorem post_three (θ η : World) : cellPosterior signal false 3 θ η =
     if η.val%8=θ.val%8 then 1/2 else 0 := by
   simp [cellPosterior, size_partial_three, agree_partial_three, eq_comm]

 def finiteReward (kind : Kind) (p : World → ℝ) (q : World → Observation → ℝ) : ℝ :=
   ∑ θ, p θ * ∑ o, loss kind (q θ o) (∑ η, p η * q η o)
 theorem finiteReward_constant (kind : Kind) (p : World → ℝ) (hp : ∑ θ, p θ=1)
     (q : Observation → ℝ) : finiteReward kind p (fun _ => q) = 0 := by
   simp [finiteReward, ← sum_mul, hp]
 def channel (b : Action) (n : ℕ) (θ : World) (o : Observation) : ℝ :=
   if o = signal θ b n then 1 else 0
 def localReward (kind : Kind) (π : Policy) (n : ℕ)
     (h : CausalFiniteTrace Action Observation n) (a : Action) : ℝ :=
   finiteReward kind (posterior π n h) (fun θ => response θ (List.ofFn h) a)
 def stage (kind : Kind) (π : Policy) (n : ℕ) : ℝ :=
   ∑ θ, prior θ * ∑ h : CausalFiniteTrace Action Observation n,
     record π n θ h * ∑ a, π.1 (List.ofFn h) a * localReward kind π n h a
 def objective (kind : Kind) (γ : ℝ) (π : Policy) : ℝ := ∑' n, γ^n*stage kind π n

 theorem sqrt_two_inverse : (Real.sqrt 2)⁻¹ = Real.sqrt 2/2 := by
   apply inv_eq_of_mul_eq_one_right
   nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
 theorem signal_binary (θ : World) (n : ℕ) (hn : n<3) :
     signal θ false n = 0 ∨ signal θ false n = 1 := by
   have hm := Nat.mod_lt (θ.val/2^n) (by decide : 0<2)
   simp only [signal, Bool.false_eq_true, ↓reduceIte, if_pos hn]
   rcases (show (θ.val/2^n)%2=0 ∨ (θ.val/2^n)%2=1 by omega) with h | h
   · left; exact Fin.ext h
   · right; exact Fin.ext h

 theorem fair_binary_reward (kind : Kind) (p : World → ℝ) (hp : ∑ θ, p θ=1)
     (n : ℕ) (hn : n<3)
     (h0 : (∑ θ, p θ*channel false n θ 0)=1/2)
     (h1 : (∑ θ, p θ*channel false n θ 1)=1/2) :
     finiteReward kind p (channel false n)=fairReward kind := by
   have hm (o : Observation) : (∑ η, p η*channel false n η o) =
       if o=0 ∨ o=1 then 1/2 else 0 := by
     by_cases ho0 : o=0
     · simpa [ho0] using h0
     by_cases ho1 : o=1
     · simpa [ho1] using h1
     · rw [if_neg (not_or.mpr ⟨ho0,ho1⟩)]
       apply sum_eq_zero; intro η _
       rcases signal_binary η n hn with h | h <;> simp [channel, h, ho0, ho1]
   have hl (θ : World) : (∑ o, loss kind (channel false n θ o)
       (∑ η, p η*channel false n η o))=fairReward kind := by
     simp_rw [hm]
     simp only [channel]
     rcases signal_binary θ n hn with h | h <;> rw [h] <;> cases kind <;>
       simp only [loss, fairReward, Fin.sum_univ_succ] <;>
       simp only [Fin.ext_iff] <;>
       norm_num [Real.sqrt_div, sqrt_two_inverse] <;>
       nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
   simp only [finiteReward, hl, ← sum_mul, hp, one_mul]

 theorem root_reward (kind : Kind) (b : Bool) :
     finiteReward kind prior (channel b 0) =
       if b then (match kind with | .hellinger => 3/2 | .absolute => 15/8)
       else fairReward kind := by
   cases b
   · apply fair_binary_reward kind prior prior_valid.2 0 (by decide)
     · norm_num [prior, uniform, channel, signal, Fin.sum_univ_succ]
     · norm_num [prior, uniform, channel, signal, Fin.sum_univ_succ]
   · have hm (o : Observation) : (∑ η, prior η*channel true 0 η o)=(1/16:ℝ) := by
       simp [prior, uniform, channel, signal, mul_ite, eq_comm]
     have hs (θ : World) : (∑ o, loss kind (channel true 0 θ o) (1/16)) =
         loss kind 1 (1/16) + 15*loss kind 0 (1/16) := by
       have he (o : Observation) : loss kind (channel true 0 θ o) (1/16) =
           (if o=θ then loss kind 1 (1/16)-loss kind 0 (1/16) else 0) + loss kind 0 (1/16) := by
         by_cases ho : o=θ <;> simp [channel, signal, ho]
       simp only [he, sum_add_distrib, sum_ite_eq', mem_univ, if_true, sum_const,
         Fintype.card_fin, nsmul_eq_mul]
       norm_num [Observation] <;> ring
     unfold finiteReward
     simp_rw [hm, hs]
     rw [← sum_mul, prior_valid.2, one_mul]
     cases kind <;> norm_num [loss, Real.sqrt_div]

 theorem cell_next_reward (kind : Kind) (b : Bool) (θ : World) (n : Fin 2) :
     finiteReward kind (cellPosterior signal b (n.val+1) θ) (channel b (n.val+1)) =
       if b then 0 else fairReward kind := by
   cases b
   · refine fair_binary_reward kind _ ?_ _ (by omega) ?_ ?_
     · fin_cases n <;> fin_cases θ <;>
         norm_num [post_one, post_two, Fin.sum_univ_succ]
     · fin_cases n <;> fin_cases θ <;>
         norm_num [post_one, post_two, channel, signal, Fin.sum_univ_succ]
     · fin_cases n <;> fin_cases θ <;>
         norm_num [post_one, post_two, channel, signal, Fin.sum_univ_succ]
   · unfold finiteReward
     simp [post_full, channel, signal]

 theorem posterior_positive_valid (π : Policy) (n : ℕ) (θ : World)
     (h : CausalFiniteTrace Action Observation n) (hh : record π n θ h ≠ 0) :
     IsDist (posterior π n h) := by
   have hm : 0 < finiteBayesMass prior (record π n) h := by
     apply lt_of_lt_of_le (mul_pos (prior_pos θ) (lt_of_le_of_ne ((record_valid π n θ).1 h) hh.symm))
     exact single_le_sum (fun η _ => mul_nonneg (prior_valid.1 η) ((record_valid π n η).1 h)) (mem_univ θ)
   exact finiteBayesPosterior_mem_simplex prior _ prior_valid.1 (fun η u => (record_valid π n η).1 u) h hm.ne'
 theorem posterior_root (π : Policy) (h : CausalFiniteTrace Action Observation 0) :
     posterior π 0 h = prior := by
   funext θ
   have he (η : World) : record π 0 η h=1 := by
     simp [record, ScheduledReveal.record, causalFiniteExperiment, causalTraceProb,
       causalTraceProbFrom, List.ofFn_zero]
   simp [posterior, finiteBayesPosterior, he, prior_valid.2]

 theorem local_positive (kind : Kind) (π : Policy) (n : Fin 2) (θ : World)
     (h : CausalFiniteTrace Action Observation (n.val+1))
     (hh : record π (n.val+1) θ h ≠ 0) (a : Action) :
     localReward kind π (n.val+1) h a = if (h 0).1 then 0 else fairReward kind := by
   have hp : posterior π (n.val+1) h = cellPosterior signal (h 0).1 (n.val+1) θ := by
     funext η; exact posterior_cell signal π.1 n.val θ h hh η
   have hr : (fun η => response η (List.ofFn h) a) = channel (h 0).1 (n.val+1) := by
     funext η o; rw [List.ofFn_succ]; simp [response, ScheduledReveal.response, mode, channel]
   rw [localReward, hp, hr, cell_next_reward]

end IdExp.FourBitPosterior
