import Formal.CausalPosterior
import Formal.AlarmPanelNativeFailure
import Formal.FiniteBayes

/-! Deterministic observation schedules selected by the initial action.
All subsequent actions remain available, and all policies may randomize using
full retained history. Positive-record posteriors are uniform on the actual
schedule-equivalence cell under a uniform finite prior. -/
noncomputable section
namespace IdExp.ScheduledReveal
open Finset
variable {Θ A O : Type*} [Fintype Θ] [Fintype A] [Fintype O]
  [DecidableEq A] [DecidableEq O]
variable (signal : Θ → A → ℕ → O)

 def mode (h : CausalHistory A O) (a : A) : A := (h.head?.map Prod.fst).getD a
 def response (θ : Θ) : CausalResponse A O := fun h a o =>
   if o = signal θ (mode h a) h.length then 1 else 0
 theorem response_valid (θ : Θ) : IsCausalResponse (response signal θ) := by
   intro h a; constructor
   · intro o; unfold response; split <;> norm_num
   · simp [response]
 abbrev record (π : CausalPolicy A O) (n : ℕ) := causalFiniteExperiment π (response signal) n
 theorem record_valid (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (n : ℕ) :
     IsFiniteExperiment (record signal π n) :=
   causalFiniteExperiment_valid π hπ (response signal) (response_valid signal) n

 def Agree (b : A) (n : ℕ) (θ η : Θ) : Prop :=
   ∀ i : Fin n, signal θ b i.val = signal η b i.val
 instance agreeDecidable (b : A) (n : ℕ) (θ η : Θ) : Decidable (Agree signal b n θ η) :=
   inferInstanceAs (Decidable (∀ i : Fin n, _))

 theorem trace_response_ne_zero (π : CausalPolicy A O) (θ : Θ)
     (h : CausalHistory A O) (hh : causalTraceProb π (response signal θ) h ≠ 0)
     (i : Fin h.length) :
     response signal θ (h.take i.val) (h[i.val]).1 (h[i.val]).2 ≠ 0 := by
   have hprod : causalTraceProb π (response signal θ) (h.take i.val) *
       causalTraceProbFrom π (response signal θ) (h.take i.val) (h.drop i.val) ≠ 0 := by
     rwa [← causalTraceProb_append, List.take_append_drop]
   have htail := (mul_ne_zero_iff.mp hprod).2
   rw [List.drop_eq_getElem_cons i.isLt] at htail
   exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htail).1).2

 theorem mode_take {n : ℕ} (h : CausalFiniteTrace A O (n+1)) (i : Fin (n+1)) :
     mode ((List.ofFn h).take i.val) (h i).1 = (h 0).1 := by
   by_cases hi : i.val=0
   · have he : i=0 := Fin.ext hi
     simp [he, mode]
   · rw [List.ofFn_succ]
     cases hv : i.val with
     | zero => exact (hi hv).elim
     | succ j => simp [List.take_succ_cons, mode]

 theorem supported_signal (π : CausalPolicy A O) (θ : Θ) (n : ℕ)
     (h : CausalFiniteTrace A O (n+1)) (hh : record signal π (n+1) θ h ≠ 0)
     (i : Fin (n+1)) : (h i).2 = signal θ (h 0).1 i.val := by
   have he := trace_response_ne_zero signal π θ (List.ofFn h) hh
     ⟨i.val, by simpa using i.isLt⟩
   have hlen : ((List.ofFn h).take i.val).length = i.val := by
     simp only [List.length_take, List.length_ofFn]; omega
   simp only [List.getElem_ofFn, response, ne_eq, ite_eq_right_iff, one_ne_zero,
     imp_false, not_not] at he
   rwa [hlen, mode_take] at he

 theorem tail_eq (π : CausalPolicy A O) (b : A) (n : ℕ) (θ η : Θ)
     (ha : Agree signal b n θ η) (pre rest : CausalHistory A O)
     (hp : pre.head?.map Prod.fst = some b) (hl : pre.length+rest.length ≤ n) :
     causalTraceProbFrom π (response signal θ) pre rest =
       causalTraceProbFrom π (response signal η) pre rest := by
   induction rest generalizing pre with
   | nil => rfl
   | cons ao rest ih =>
     have hlen : pre.length < n := by simp only [List.length_cons] at hl; omega
     have he : response signal θ pre ao.1 ao.2 = response signal η pre ao.1 ao.2 := by
       simp only [response, mode, hp, Option.getD_some, ha ⟨pre.length, hlen⟩]
     simp only [causalTraceProbFrom, he]
     rw [ih (pre ++ [ao])]
     · cases pre with
       | nil => simp at hp
       | cons x xs => simpa using hp
     · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *; omega

 theorem row_eq_of_agree (π : CausalPolicy A O) (n : ℕ) (θ η : Θ)
     (h : CausalFiniteTrace A O (n+1)) (ha : Agree signal (h 0).1 (n+1) θ η) :
     record signal π (n+1) θ h = record signal π (n+1) η h := by
   change causalTraceProb π (response signal θ) (List.ofFn h) =
     causalTraceProb π (response signal η) (List.ofFn h)
   rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
   simp only [causalTraceProbFrom, List.nil_append]
   have he : response signal θ [] (h 0).1 (h 0).2 = response signal η [] (h 0).1 (h 0).2 := by
     have hh : signal θ (h 0).1 0 = signal η (h 0).1 0 := ha ⟨0, by omega⟩
     simp only [response, mode, List.head?_nil, Option.map_none, Option.getD_none,
       List.length_nil, hh]
     rfl
   rw [he, tail_eq signal π (h 0).1 (n+1) θ η ha _ _ (by simp) (by simp; omega)]

/-- Full-history likelihood is constant on the schedule cell and zero outside it.
The policy can use all previous actions and observations. -/
 theorem likelihood_cell (π : CausalPolicy A O) (n : ℕ) (θ : Θ)
     (h : CausalFiniteTrace A O (n+1)) (hh : record signal π (n+1) θ h ≠ 0) (η : Θ) :
     record signal π (n+1) η h =
       if Agree signal (h 0).1 (n+1) θ η then record signal π (n+1) θ h else 0 := by
   by_cases ha : Agree signal (h 0).1 (n+1) θ η
   · rw [if_pos ha]; exact (row_eq_of_agree signal π n θ η h ha).symm
   · rw [if_neg ha]
     by_contra he
     apply ha
     intro i
     rw [← supported_signal signal π θ n h hh i, ← supported_signal signal π η n h he i]

 def cellSize (b : A) (n : ℕ) (θ : Θ) : ℝ :=
   ∑ η : Θ, if Agree signal b n θ η then 1 else 0
 def cellPosterior (b : A) (n : ℕ) (θ η : Θ) : ℝ :=
   if Agree signal b n θ η then 1 / cellSize signal b n θ else 0
 def uniform (_ : Θ) : ℝ := 1 / Fintype.card Θ

/-- Bayes' ratio for the actual action-observation record, with no assumption
about the continuation policy or a supplied posterior formula. -/
 theorem posterior_cell [Nonempty Θ] (π : CausalPolicy A O) (n : ℕ) (θ : Θ)
     (h : CausalFiniteTrace A O (n+1)) (hh : record signal π (n+1) θ h ≠ 0) (η : Θ) :
     finiteBayesPosterior uniform (record signal π (n+1)) h η =
       cellPosterior signal (h 0).1 (n+1) θ η := by
   have hc : (Fintype.card Θ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
   have hm : (∑ c, uniform c * record signal π (n+1) c h) =
       (1/(Fintype.card Θ:ℝ))*record signal π (n+1) θ h * cellSize signal (h 0).1 (n+1) θ := by
     calc _ = ∑ c : Θ, (1/(Fintype.card Θ:ℝ))*record signal π (n+1) θ h *
         (if Agree signal (h 0).1 (n+1) θ c then 1 else 0) := by
           apply sum_congr rfl; intro c _
           rw [likelihood_cell signal π n θ h hh c]
           unfold uniform; split <;> ring
       _ = _ := by rw [← mul_sum]; rfl
   unfold finiteBayesPosterior
   rw [hm, likelihood_cell signal π n θ h hh]
   unfold cellPosterior uniform
   split <;> simp [*, div_mul_eq_div_mul_one_div, mul_div_mul_left, mul_div_mul_right]

 theorem firstExpectation (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
     (θ : Θ) (n : ℕ) (f : A × O → ℝ) :
     (∑ h : CausalFiniteTrace A O (n+1), record signal π (n+1) θ h * f (h 0)) =
       ∑ ao : A × O, π [] ao.1 * response signal θ [] ao.1 ao.2 * f ao := by
   rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A × O)).sum_comp, Fintype.sum_prod_type]
   have hc (ao : A × O) (rest : CausalFiniteTrace A O n) :
       (Fin.consEquiv (fun _ : Fin (n+1) => A × O)) (ao,rest) = Fin.cons ao rest := by
     funext i; exact Fin.consEquiv_apply _ _ i
   simp_rw [hc]
   change (∑ ao, ∑ rest : CausalFiniteTrace A O n,
     causalTraceProb π (response signal θ) (List.ofFn (Fin.cons ao rest)) * f ao) = _
   simp only [causalTraceProb, List.ofFn_cons, causalTraceProbFrom, List.nil_append]
   apply sum_congr rfl; intro ao _
   calc _ = (π [] ao.1 * response signal θ [] ao.1 ao.2 * f ao) *
       ∑ rest : CausalFiniteTrace A O n,
         causalTraceProbFrom π (response signal θ) [ao] (List.ofFn rest) := by
           rw [mul_sum]; apply sum_congr rfl; intro rest _; ring
     _ = _ := by rw [sum_causalTraceProbFrom π hπ _ (response_valid signal θ)]; ring

 theorem root_mass (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
     (θ : Θ) (n : ℕ) (b : A) :
     (∑ h : CausalFiniteTrace A O (n+1),
       if (h 0).1=b then record signal π (n+1) θ h else 0) = π [] b := by
   have he := firstExpectation signal π hπ θ n (fun ao => if ao.1=b then 1 else 0)
   simp only [mul_ite, mul_one, mul_zero] at he
   rw [he, Fintype.sum_prod_type]
   calc
     _ = (∑ a : A, if a=b then π [] a else 0) := by
       apply sum_congr rfl
       intro a _
       by_cases hab : a=b
       · simp only [hab, if_true]
         rw [← mul_sum, (response_valid signal θ [] b).2, mul_one]
       · simp [hab]
     _ = _ := by simp

end IdExp.ScheduledReveal
