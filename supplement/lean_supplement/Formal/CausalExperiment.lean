import Formal.CausalPathLaw
import Formal.FiniteBlackwell

/-!
# Finite experiments induced by causal policies

**Relevance:** direct current-paper ontology and process support.

The paper distinguishes a causal response kernel from the statistical
experiment a policy induces. This file makes that bridge literal. At horizon
`n`, the signal is the full length-`n` action-observation trace and its row in
world `theta` is the causal trace probability. We prove that every row is a
probability vector, that the experiment depends only on controlled-trace
equivalence classes, that its entries agree with causal path-law cylinders,
and that forgetting the newest coordinate is a stochastic garbling. Thus the
induced finite experiments form the growing Blackwell chain used throughout
the canonical paper.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset

variable {A O Θ : Type*} [Fintype A] [Fintype O]

/-- Full action-observation signals of an exact finite horizon. -/
abbrev CausalFiniteTrace (A O : Type*) (n : ℕ) := Fin n → A × O

/-- Product of the policy probabilities along a finite causal history. -/
noncomputable def causalPolicyProbFrom (π : CausalPolicy A O) :
    CausalHistory A O → CausalHistory A O → ℝ
  | _, [] => 1
  | h, ao :: rest => π h ao.1 * causalPolicyProbFrom π (h ++ [ao]) rest

noncomputable def causalPolicyProb (π : CausalPolicy A O)
    (h : CausalHistory A O) : ℝ :=
  causalPolicyProbFrom π [] h

/-- Trace probability factors into a policy term and the controlled response
likelihood. This makes quotient invariance transparent. -/
theorem causalTraceProbFrom_factor (π : CausalPolicy A O)
    (Q : CausalResponse A O) (pre rest : CausalHistory A O) :
    causalTraceProbFrom π Q pre rest =
      causalPolicyProbFrom π pre rest * causalResponseProbFrom Q pre rest := by
  induction rest generalizing pre with
  | nil => simp [causalTraceProbFrom, causalPolicyProbFrom, causalResponseProbFrom]
  | cons ao rest ih =>
      simp only [causalTraceProbFrom, causalPolicyProbFrom, causalResponseProbFrom]
      rw [ih]
      ring

theorem causalTraceProb_factor (π : CausalPolicy A O)
    (Q : CausalResponse A O) (h : CausalHistory A O) :
    causalTraceProb π Q h =
      causalPolicyProb π h * causalResponseProb Q h := by
  exact causalTraceProbFrom_factor π Q [] h

/-- Controlled-trace equivalent worlds induce identical finite history laws
under every policy. -/
theorem causalTraceProb_eq_of_causalBehEq (π : CausalPolicy A O)
    {Q Q' : CausalResponse A O} (hQQ' : CausalBehEq Q Q')
    (h : CausalHistory A O) :
    causalTraceProb π Q h = causalTraceProb π Q' h := by
  rw [causalTraceProb_factor, causalTraceProb_factor, hQQ' h]

/-- The probabilities of all length-`n` continuations from a realized prefix
sum to one. -/
theorem sum_causalTraceProbFrom (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (pre : CausalHistory A O) (n : ℕ) :
    ∑ w : CausalFiniteTrace A O n,
      causalTraceProbFrom π Q pre (List.ofFn w) = 1 := by
  induction n generalizing pre with
  | zero => simp [causalTraceProbFrom]
  | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A × O)).sum_comp]
      rw [Fintype.sum_prod_type]
      have hcons (ao : A × O) (rest : CausalFiniteTrace A O n) :
          (Fin.consEquiv (fun _ : Fin (n + 1) => A × O)) (ao, rest) =
            Fin.cons ao rest := by
        funext i
        exact Fin.consEquiv_apply _ _ i
      calc
        ∑ ao : A × O, ∑ rest : CausalFiniteTrace A O n,
            causalTraceProbFrom π Q pre
              (List.ofFn ((Fin.consEquiv (fun _ : Fin (n + 1) => A × O)) (ao, rest))) =
            ∑ ao : A × O, ∑ rest : CausalFiniteTrace A O n,
              π pre ao.1 * Q pre ao.1 ao.2 *
                causalTraceProbFrom π Q (pre ++ [ao]) (List.ofFn rest) := by
                  apply Finset.sum_congr rfl
                  intro ao _
                  apply Finset.sum_congr rfl
                  intro rest _
                  rw [hcons ao rest, List.ofFn_cons]
                  rfl
        _ = ∑ ao : A × O, (π pre ao.1 * Q pre ao.1 ao.2) *
              ∑ rest : CausalFiniteTrace A O n,
                causalTraceProbFrom π Q (pre ++ [ao]) (List.ofFn rest) := by
              apply Finset.sum_congr rfl
              intro ao _
              rw [Finset.mul_sum]
        _ = ∑ ao : A × O, π pre ao.1 * Q pre ao.1 ao.2 := by
              apply Finset.sum_congr rfl
              intro ao _
              rw [ih (pre ++ [ao]), mul_one]
        _ = 1 := by
              rw [Fintype.sum_prod_type]
              simp_rw [← Finset.mul_sum, (hQ pre _).2, mul_one]
              exact (hπ pre).2

/-- The finite statistical experiment induced by policy `π` on a family of
causal response laws. -/
noncomputable def causalFiniteExperiment (π : CausalPolicy A O)
    (Qs : Θ → CausalResponse A O) (n : ℕ) :
    FiniteExperiment Θ (CausalFiniteTrace A O n) :=
  fun θ w => causalTraceProb π (Qs θ) (List.ofFn w)

/-- The induced matrix is a genuine finite experiment. -/
theorem causalFiniteExperiment_valid (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    IsFiniteExperiment (causalFiniteExperiment π Qs n) := by
  intro θ
  constructor
  · intro w
    exact causalTraceProb_nonneg π hπ (Qs θ) (hQ θ) _
  · exact sum_causalTraceProbFrom π hπ (Qs θ) (hQ θ) [] n

/-- The induced experiment is well-defined on the paper's controlled-trace
quotient of causal response laws. -/
theorem causalFiniteExperiment_eq_of_behEq (π : CausalPolicy A O)
    {Qs Qs' : Θ → CausalResponse A O}
    (hQQ' : ∀ θ, CausalBehEq (Qs θ) (Qs' θ)) (n : ℕ) :
    causalFiniteExperiment π Qs n = causalFiniteExperiment π Qs' n := by
  funext θ w
  exact causalTraceProb_eq_of_causalBehEq π (hQQ' θ) (List.ofFn w)

/-- The finite matrix entry is exactly the corresponding path-law cylinder
probability. -/
theorem causalFiniteExperiment_cylinder
    [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (μ : Θ → MeasureTheory.Measure (CausalTraj A O))
    (hμ : ∀ θ, IsCausalPathLaw π (Qs θ) (μ θ))
    (n : ℕ) (θ : Θ) (w : CausalFiniteTrace A O n) :
    μ θ (causalCyl (List.ofFn w)) =
      ENNReal.ofReal (causalFiniteExperiment π Qs n θ w) := by
  exact (hμ θ).cylinder (List.ofFn w)

/-- Summing the probabilities of all one-step extensions recovers the prefix
probability. -/
theorem sum_causalTraceProb_extensions (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (h : CausalHistory A O) :
    ∑ ao : A × O, causalTraceProb π Q (h ++ [ao]) =
      causalTraceProb π Q h := by
  simp_rw [causalTraceProb_append_singleton]
  calc
    ∑ ao : A × O, causalTraceProb π Q h * π h ao.1 * Q h ao.1 ao.2 =
        causalTraceProb π Q h * ∑ ao : A × O, π h ao.1 * Q h ao.1 ao.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ao _
      ring
    _ = causalTraceProb π Q h := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, (hQ h _).2, mul_one]
      rw [(hπ h).2, mul_one]

/-- Deterministic decoder that forgets the newest action-observation pair. -/
noncomputable def causalPrefixRule (n : ℕ) :
    CausalFiniteTrace A O (n + 1) → CausalFiniteTrace A O n → ℝ := by
  classical
  exact fun w u => if u = Fin.init w then 1 else 0

theorem causalPrefixRule_mem_stochasticRules (n : ℕ) :
    causalPrefixRule (A := A) (O := O) n ∈
      stochasticRules (CausalFiniteTrace A O (n + 1))
        (CausalFiniteTrace A O n) := by
  classical
  intro w _
  constructor
  · intro u
    by_cases h : u = Fin.init w <;> simp [causalPrefixRule, h]
  · simp [causalPrefixRule]

/-- Forgetting the newest coordinate sends the horizon-`n+1` experiment
exactly to the horizon-`n` experiment. -/
theorem causalFiniteExperiment_prefix (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    finiteDecisionLaw (causalFiniteExperiment π Qs (n + 1))
      (causalPrefixRule n) = causalFiniteExperiment π Qs n := by
  classical
  funext θ u
  unfold finiteDecisionLaw causalFiniteExperiment
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hsnoc (ao : A × O) (pre : CausalFiniteTrace A O n) :
      (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)) (ao, pre) =
        Fin.snoc pre ao := by
    funext i
    exact Fin.snocEquiv_apply _ _ i
  calc
    ∑ ao : A × O, ∑ pre : CausalFiniteTrace A O n,
        causalTraceProb π (Qs θ)
          (List.ofFn ((Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)) (ao, pre))) *
            causalPrefixRule n
              ((Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)) (ao, pre)) u =
      ∑ ao : A × O, ∑ pre : CausalFiniteTrace A O n,
        causalTraceProb π (Qs θ) (List.ofFn pre ++ [ao]) *
          (if u = pre then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro ao _
      apply Finset.sum_congr rfl
      intro pre _
      rw [hsnoc ao pre, List.ofFn_succ_last]
      simp [causalPrefixRule]
    _ = ∑ ao : A × O,
        causalTraceProb π (Qs θ) (List.ofFn u ++ [ao]) := by simp
    _ = causalTraceProb π (Qs θ) (List.ofFn u) :=
      sum_causalTraceProb_extensions π hπ (Qs θ) (hQ θ) (List.ofFn u)

/-- The policy-induced finite experiments form the paper's growing Blackwell
chain, one exact prefix marginalization at a time. -/
theorem causalFiniteExperiment_prefix_blackwell (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs (n + 1)) := by
  refine ⟨causalPrefixRule n, causalPrefixRule_mem_stochasticRules n, ?_⟩
  exact causalFiniteExperiment_prefix π hπ Qs hQ n

/-- Every shorter policy experiment is an exact garbling of every longer one.
This packages repeated one-step prefix marginalization and is the formal
shorter-horizon bookkeeping used by finite-horizon universality. -/
theorem causalFiniteExperiment_prefix_blackwell_of_le
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {m n : ℕ} (hmn : m ≤ n) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs m)
      (causalFiniteExperiment π Qs n) := by
  exact Nat.le_induction
    (finiteBlackwellLE_refl (causalFiniteExperiment π Qs m))
    (fun k _ ih => finiteBlackwellLE_trans ih
      (causalFiniteExperiment_prefix_blackwell π hπ Qs hQ k))
    n hmn

end IdExp
