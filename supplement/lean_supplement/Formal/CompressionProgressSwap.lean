import Formal.RewardProcessWitness
import Formal.DeterministicDeficiency

/-!
# Full-history scoring cannot distinguish two prior-predictively identical classes

The Boolean parameter `e` selects which root action reveals the fair world bit.
The other action draws one independent fair bit. All later observations repeat
the first observation. The complete action-observation record is retained.

Every policy has the same prior-marginal record law in both classes, although
the ordering of the two constant-action collectors reverses. The score may be
any real function of the full history, with no computability assumption.
-/
namespace IdExp.CompressionProgressSwap
open Finset
noncomputable section

abbrev World := Fin 2
abbrev History := CausalHistory Bool (Fin 2)
abbrev Policy := ValidCausalPolicy Bool (Fin 2)

def root (e a : Bool) (world o : World) : ℝ :=
  if a = e then if o = world then 1 else 0 else 1/2

theorem root_valid (e a : Bool) (world : World) : IsDist (root e a world) := by
  constructor
  · intro o; unfold root; split_ifs <;> norm_num
  · cases e <;> cases a <;> fin_cases world <;> norm_num [root, Fin.sum_univ_succ]

def response (e : Bool) (world : World) : CausalResponse Bool World := fun h a o =>
  if h = [] then root e a world o else if o = (h.headD (false,0)).2 then 1 else 0

theorem response_valid (e : Bool) (world : World) : IsCausalResponse (response e world) := by
  intro h a
  by_cases hh : h = []
  · have he : response e world h a = root e a world := by funext o; simp [response, hh]
    rw [he]
    exact root_valid e a world
  · constructor
    · intro o; simp only [response, hh, ↓reduceIte]; split_ifs <;> norm_num
    · simp [response, hh]

def policy (a : Bool) : Policy := validDetPolicy (fun _ => a)

theorem tail_eq (π : CausalPolicy Bool World) (e f : Bool) (world other : World)
    (pre rest : History) (hne : pre ≠ []) :
    causalTraceProbFrom π (response e world) pre rest =
      causalTraceProbFrom π (response f other) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom, response, hne, ↓reduceIte]
    rw [ih (pre ++ [ao]) (by simp)]

theorem root_sum (e a : Bool) (o : World) : root e a 0 o + root e a 1 o = 1 := by
  cases e <;> cases a <;> fin_cases o <;> norm_num [root]

/-- Exact equality of the prior mixtures, including every chosen action. -/
theorem average_trace_eq (π : CausalPolicy Bool World) (e f : Bool) (h : History) :
    (causalTraceProb π (response e 0) h + causalTraceProb π (response e 1) h) / 2 =
      (causalTraceProb π (response f 0) h + causalTraceProb π (response f 1) h) / 2 := by
  cases h with
  | nil => rfl
  | cons ao rest =>
    simp only [causalTraceProb, causalTraceProbFrom, response, ↓reduceIte, List.nil_append]
    rw [tail_eq π e f 0 0 [ao] rest (by simp),
      tail_eq π e f 1 0 [ao] rest (by simp),
      tail_eq π f f 1 0 [ao] rest (by simp)]
    have he := root_sum e ao.1 ao.2
    have hf := root_sum f ao.1 ao.2
    linear_combination (π [] ao.1 * causalTraceProbFrom π (response f 0) [ao] rest / 2) * (he - hf)

def averageExperiment (e : Bool) (π : Policy) (n : ℕ)
    (w : CausalFiniteTrace Bool World n) : ℝ :=
  (causalFiniteExperiment π.1 (response e) n 0 w +
    causalFiniteExperiment π.1 (response e) n 1 w) / 2

theorem averageExperiment_eq (e f : Bool) (π : Policy) (n : ℕ) :
    averageExperiment e π n = averageExperiment f π n := by
  funext w
  exact average_trace_eq π.1 e f (List.ofFn w)

def objective (e : Bool) (π : Policy) (n : ℕ)
    (F : CausalFiniteTrace Bool World n → ℝ) : ℝ :=
  ∑ w, averageExperiment e π n w * F w

theorem objective_eq (e f : Bool) (π : Policy) (n : ℕ)
    (F : CausalFiniteTrace Bool World n → ℝ) :
    objective e π n F = objective f π n F := by
  simp only [objective, averageExperiment_eq e f π n]

theorem record_one (e : Bool) (π : Policy) (world : World)
    (w : CausalFiniteTrace Bool World 1) :
    causalFiniteExperiment π.1 (response e) 1 world w =
      π.1 [] (w 0).1 * root e (w 0).1 world (w 0).2 := by
  simp [causalFiniteExperiment, causalTraceProb, List.ofFn_succ,
    causalTraceProbFrom, response]

theorem revealing_record (e : Bool) (world : World)
    (w : CausalFiniteTrace Bool World 1)
    (hw : causalFiniteExperiment (policy e).1 (response e) 1 world w ≠ 0) :
    (w 0).2 = world := by
  rw [record_one] at hw
  by_contra ho
  by_cases ha : (w 0).1 = e
  · simp [policy, validDetPolicy, detPolicy, root, ha, ho] at hw
  · simp [policy, validDetPolicy, detPolicy, ha] at hw

theorem revealing_greatest (e : Bool) : CausalFinitarilyGreatest (response e) (policy e) :=
  causalFinitarilyGreatest_of_revealing_prefix (response e) (response_valid e)
    (policy e) 1 (fun w => (w 0).2) (revealing_record e)

/-- Even arbitrary randomized continuations cannot recover the world after COIN. -/
theorem coin_prefix_independent (e : Bool) (π : Policy) (hroot : π.1 [] e = 0)
    (t : ℕ) : ClassIndependentFiniteExperiment (causalFiniteExperiment π.1 (response e) t) := by
  intro world other
  funext w
  unfold causalFiniteExperiment causalTraceProb
  cases hh : List.ofFn w with
  | nil => rfl
  | cons ao rest =>
    simp only [causalTraceProbFrom, List.nil_append]
    rw [tail_eq π.1 e e world other [ao] rest (by simp)]
    by_cases ha : ao.1 = e
    · simp [ha, hroot]
    · simp [response, root, ha]

theorem revealing_pairTV (e : Bool) :
    finiteTV (causalFiniteExperiment (policy e).1 (response e) 1 0)
      (causalFiniteExperiment (policy e).1 (response e) 1 1) = 1 := by
  let tr (world : World) : CausalFiniteTrace Bool World 1 := fun _ => (e, world)
  have he (world : World) : causalFiniteExperiment (policy e).1 (response e) 1 world =
      fun w => if w = tr world then 1 else 0 := by
    funext w
    have hw : w = tr world ↔ (w 0).1 = e ∧ (w 0).2 = world := by
      constructor
      · intro h; simp [h, tr]
      · rintro ⟨ha,ho⟩; funext i; fin_cases i; exact Prod.ext ha ho
    rw [record_one]
    by_cases ha : (w 0).1 = e <;> by_cases ho : (w 0).2 = world <;>
      simp [policy, validDetPolicy, detPolicy, root, ha, ho, hw]
  rw [he, he]
  apply finiteTV_pointMass_eq_one
  intro h
  have := congrArg (fun w => (w 0).2) h
  norm_num [tr] at this

/-- The missed one-step experiment has permanent minimax TV deficit one half. -/
theorem coin_deficiency (e : Bool) (π : Policy) (hroot : π.1 [] e = 0) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
      (causalFiniteExperiment (policy e).1 (response e) 1) = 1/2 := by
  rw [finiteDeficiency_classIndependent_binary_eq_half_pairTV _ _
    (causalFiniteExperiment_valid _ π.2 (response e) (response_valid e) t)
    (causalFiniteExperiment_valid _ (policy e).2 (response e) (response_valid e) 1)
    (coin_prefix_independent e π hroot t), revealing_pairTV]

theorem coin_strictly_dominated (e : Bool) (π : Policy) (hroot : π.1 [] e = 0) :
    CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) := by
  refine ⟨revealing_greatest e π, ?_⟩
  apply classIndependent_prefixes_not_finitarily_dominate (response e) (response_valid e)
    π (policy e) 1 (coin_prefix_independent e π hroot)
  rw [revealing_pairTV]
  norm_num

theorem constant_coin_strictly_dominated (e : Bool) :
    CausalFinitaryDominates (response e) (policy e) (policy (!e)) ∧
      ¬ CausalFinitaryDominates (response e) (policy (!e)) (policy e) := by
  apply coin_strictly_dominated
  cases e <;> simp [policy, validDetPolicy, detPolicy]

/-- No fixed full-history score strictly respects both native process orders. -/
theorem exists_score_order_failure (n : ℕ) (F : CausalFiniteTrace Bool World n → ℝ) :
    ∃ e : Bool,
      objective e (policy e) n F ≤ objective e (policy (!e)) n F ∧
      CausalFinitaryDominates (response e) (policy e) (policy (!e)) ∧
      ¬ CausalFinitaryDominates (response e) (policy (!e)) (policy e) := by
  rcases le_total (objective false (policy false) n F) (objective false (policy true) n F) with h | h
  · exact ⟨false, h, constant_coin_strictly_dominated false⟩
  · refine ⟨true, ?_, constant_coin_strictly_dominated true⟩
    simpa only [objective_eq true false, Bool.not_true] using h


/-- The obstruction also applies to any fixed aggregation of the identical
prefix-score sequences, including extended-valued complete returns. -/
theorem class_independent_score_failure {Value : Type*} [LinearOrder Value]
    (J : Bool → Policy → Value) (hJ : ∀ e f π, J e π = J f π) :
    ∃ e : Bool, J e (policy e) ≤ J e (policy (!e)) ∧
      CausalFinitaryDominates (response e) (policy e) (policy (!e)) ∧
      ¬ CausalFinitaryDominates (response e) (policy (!e)) (policy e) := by
  rcases le_total (J false (policy false)) (J false (policy true)) with h | h
  · exact ⟨false,h,constant_coin_strictly_dominated false⟩
  · refine ⟨true,?_,constant_coin_strictly_dominated true⟩
    simpa only [hJ true false, Bool.not_true] using h

end
end IdExp.CompressionProgressSwap
