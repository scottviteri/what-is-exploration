import Formal.StateOccupancyEntropy

/-! Every state-entropy optimizer is permanently deficient, despite observing
all physical states. The full record retains arbitrary adaptive later actions.
The target is the actual one-transition TEST experiment in the same MDP class. -/
namespace IdExp.StateOccupancyEntropy
open Finset Filter Topology
noncomputable section

theorem tail_independent (π : CausalPolicy Action State) (θ η : World)
    (pre rest : History) (b : Fin 2) (hpre : currentState pre = some b) :
    causalTraceProbFrom π (response θ) pre rest =
      causalTraceProbFrom π (response η) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    by_cases ho : ao.2 = some b
    · simp only [causalTraceProbFrom, response, hpre, transition, point, ho, if_true,
        mul_one]
      exact congrArg (fun x => π pre ao.1 * x)
        (ih (pre ++ [ao]) (by simpa using ho))
    · simp [causalTraceProbFrom, response, hpre, transition, point, ho]

/-- RANDOM at startup makes every full finite record independent of the model. -/
theorem random_prefix_independent (π : ValidCausalPolicy Action State)
    (hp : π.1 [] 0 = 0) (t : ℕ) :
    ClassIndependentFiniteExperiment (causalFiniteExperiment π.1 response t) := by
  intro θ η
  funext w
  unfold causalFiniteExperiment causalTraceProb
  cases hw : List.ofFn w with
  | nil => rfl
  | cons ao rest =>
    rcases ao with ⟨a,o⟩
    by_cases ha : a = 0
    · simp [causalTraceProbFrom, ha, hp]
    · have ha1 : a = 1 := by fin_cases a <;> simp_all
      subst a
      cases o with
      | none => simp [causalTraceProbFrom, response, transition, fair]
      | some b =>
        change (π.1 [] 1 * (1/2)) *
            causalTraceProbFrom π.1 (response θ) [(1,some b)] rest =
          (π.1 [] 1 * (1/2)) *
            causalTraceProbFrom π.1 (response η) [(1,some b)] rest
        rw [tail_independent π.1 θ η [(1, some b)] rest b (by simp [currentState])]

def testDecode (w : CausalFiniteTrace Action State 1) : World := (w 0).2.getD 0

theorem test_reveals (θ : World) (w : CausalFiniteTrace Action State 1)
    (hw : causalFiniteExperiment (purePolicy 0).1 response 1 θ w ≠ 0) :
    testDecode w = θ := by
  have he : causalFiniteExperiment (purePolicy 0).1 response 1 θ w =
      (if (w 0).1 = 0 then 1 else 0) *
        transition θ none (w 0).1 (w 0).2 := by
    simp [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
      List.ofFn_succ, purePolicy, response]
  rw [he] at hw
  have ha : (w 0).1 = 0 := by
    by_contra hn
    simp [hn] at hw
  rw [ha] at hw
  have ho : (w 0).2 = some θ := by
    by_contra hn
    simp [transition, point, hn] at hw
  simp [testDecode, ho]

theorem test_greatest : CausalFinitarilyGreatest response (purePolicy 0) :=
  causalFinitarilyGreatest_of_revealing_prefix response response_valid
    (purePolicy 0) 1 testDecode test_reveals

theorem test_pairTV :
    finiteTV (causalFiniteExperiment (purePolicy 0).1 response 1 0)
      (causalFiniteExperiment (purePolicy 0).1 response 1 1) = 1 := by
  have hz0 : (none : State) ≠ some (0 : Fin 2) := by decide
  have hz1 : (none : State) ≠ some (1 : Fin 2) := by decide
  unfold finiteTV
  rw [← (Equiv.funUnique (Fin 1) (Action × State)).symm.sum_comp]
  norm_num [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    List.ofFn_succ, purePolicy, response, transition, point, fair, Equiv.funUnique,
    Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_two, hz0, hz1]

/-- The exact loss persists at every collection time, not merely the reward horizon. -/
theorem random_deficiency (π : ValidCausalPolicy Action State)
    (hp : π.1 [] 0 = 0) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 response t)
      (causalFiniteExperiment (purePolicy 0).1 response 1) = 1/2 := by
  rw [finiteDeficiency_classIndependent_binary_eq_half_pairTV _ _
    (causalFiniteExperiment_valid π.1 π.2 response response_valid t)
    (causalFiniteExperiment_valid (purePolicy 0).1 (purePolicy 0).2 response response_valid 1)
    (random_prefix_independent π hp t), test_pairTV]

def eventualTestDeficiency (π : ValidCausalPolicy Action State) : ℝ :=
  sInf (Set.range fun t : ℕ => finiteDeficiency (causalFiniteExperiment π.1 response t)
    (causalFiniteExperiment (purePolicy 0).1 response 1))

theorem random_eventualDeficiency (π : ValidCausalPolicy Action State)
    (hp : π.1 [] 0 = 0) : eventualTestDeficiency π = 1/2 := by
  simp [eventualTestDeficiency, random_deficiency π hp]

theorem random_strictly_dominated (π : ValidCausalPolicy Action State)
    (hp : π.1 [] 0 = 0) :
    CausalFinitaryDominates response (purePolicy 0) π ∧
      ¬ CausalFinitaryDominates response π (purePolicy 0) := by
  refine ⟨test_greatest π, ?_⟩
  apply classIndependent_prefixes_not_finitarily_dominate response response_valid
    π (purePolicy 0) 1 (random_prefix_independent π hp)
  rw [test_pairTV]
  norm_num

/-- Attainment and all-optima permanent failure for the exact published objective,
separately in each MDP and at every proper discount. -/
theorem all_optima_failure (θ : World) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∃ π, ∀ ρ, objective ρ θ γ ≤ objective π θ γ) ∧
    ∀ π : ValidCausalPolicy Action State,
      (∀ ρ, objective ρ θ γ ≤ objective π θ γ) →
        (∀ t, finiteDeficiency (causalFiniteExperiment π.1 response t)
          (causalFiniteExperiment (purePolicy 0).1 response 1) = 1/2) ∧
        eventualTestDeficiency π = 1/2 ∧
        CausalFinitaryDominates response (purePolicy 0) π ∧
        ¬ CausalFinitaryDominates response π (purePolicy 0) := by
  refine ⟨⟨purePolicy 1, objective_attained θ γ hγ0 hγ1⟩, ?_⟩
  intro π hopt
  have hp := (objective_maximizer_iff π θ γ hγ0 hγ1).1 hopt
  exact ⟨random_deficiency π hp, random_eventualDeficiency π hp,
    random_strictly_dominated π hp⟩

/-- Any sequence of exact maximizers retains loss one half, including when its
proper discounts approach one. No limiting-policy convergence is assumed. -/
theorem optimizer_family_deficiency_limit
    (θ : World) (γ : ℕ → ℝ) (policies : ℕ → ValidCausalPolicy Action State)
    (hγ0 : ∀ n, 0 < γ n) (hγ1 : ∀ n, γ n < 1)
    (hopt : ∀ n ρ, objective ρ θ (γ n) ≤ objective (policies n) θ (γ n)) :
    Tendsto (fun n => eventualTestDeficiency (policies n)) atTop (𝓝 (1/2)) := by
  have he : (fun n => eventualTestDeficiency (policies n)) = fun _ => (1/2 : ℝ) := by
    funext n
    exact random_eventualDeficiency (policies n)
      ((objective_maximizer_iff (policies n) θ (γ n) (hγ0 n) (hγ1 n)).1 (hopt n))
  rw [he]
  exact tendsto_const_nhds

end
end IdExp.StateOccupancyEntropy
