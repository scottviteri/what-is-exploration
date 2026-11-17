import Formal.PairedAlarm
import Formal.AlarmPanelPrior
import Formal.CausalUniversality

/-!
# Actual-prior expectations of finite simultaneous-alarm record scores

These helpers apply to any fixed real score on a finite collected record of the
simultaneous interface. They split a valid randomized history policy at its
startup action into an inspection branch and a play branch with the same later
rows, transfer bounds on supported records to the geometric-prior expectation,
and obtain a deterministic global optimizer from the finite causal Kuhn
decomposition. There is no assumed optimizer or supplied abstract objective.
-/

noncomputable section
namespace IdExp.PairedAlarm.PseudoCount
open Finset MeasureTheory

/-! ## Startup branches of a policy -/

/-- The policy with its root forced to inspect; later choices unchanged. -/
def inspectBranch (ρ : CausalPolicy Action Observation) : CausalPolicy Action Observation :=
  fun h a => if h = [] then (if a = inspect then 1 else 0) else ρ h a

/-- The policy with its root conditioned on not inspecting; later choices unchanged.
When the policy always inspects, an arbitrary play root is used with weight zero. -/
def playBranch (ρ : CausalPolicy Action Observation) : CausalPolicy Action Observation :=
  fun h a => if h = [] then
    (if inspectionProbability ρ = 1 then (if a = play0 then 1 else 0)
      else (if a = inspect then 0 else ρ [] a / (1 - inspectionProbability ρ)))
    else ρ h a

theorem inspectBranch_nil (ρ : CausalPolicy Action Observation) (a : Action) :
    inspectBranch ρ [] a = if a = inspect then 1 else 0 := by simp [inspectBranch]

theorem inspectBranch_cons (ρ : CausalPolicy Action Observation) (h : History) (hh : h ≠ [])
    (a : Action) : inspectBranch ρ h a = ρ h a := by simp [inspectBranch, hh]

theorem playBranch_nil (ρ : CausalPolicy Action Observation) (a : Action) :
    playBranch ρ [] a = (if inspectionProbability ρ = 1 then (if a = play0 then 1 else 0)
      else (if a = inspect then 0 else ρ [] a / (1 - inspectionProbability ρ))) := by
  simp [playBranch]

theorem playBranch_cons (ρ : CausalPolicy Action Observation) (h : History) (hh : h ≠ [])
    (a : Action) : playBranch ρ h a = ρ h a := by simp [playBranch, hh]

theorem inspectBranch_valid (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ) :
    IsCausalPolicy (inspectBranch ρ) := by
  intro h
  by_cases hh : h = []
  · subst hh
    constructor
    · intro a; rw [inspectBranch_nil]; split_ifs <;> norm_num
    · simp only [inspectBranch_nil]
      simp [inspect, Fin.sum_univ_succ]
  · constructor
    · intro a; rw [inspectBranch_cons ρ h hh]; exact (hρ h).1 a
    · simp only [inspectBranch_cons ρ h hh]; exact (hρ h).2

theorem playBranch_valid (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ) :
    IsCausalPolicy (playBranch ρ) := by
  intro h
  by_cases hh : h = []
  · subst hh
    by_cases hr : inspectionProbability ρ = 1
    · constructor
      · intro a; rw [playBranch_nil, if_pos hr]; split_ifs <;> norm_num
      · simp only [playBranch_nil, if_pos hr]
        simp [play0, Fin.sum_univ_succ]
    · have hlt : inspectionProbability ρ < 1 :=
        lt_of_le_of_ne (inspectionProbability_le_one ρ hρ) hr
      have hne : (1 - inspectionProbability ρ) ≠ 0 := by
        intro hz; linarith
      constructor
      · intro a
        rw [playBranch_nil, if_neg hr]
        split_ifs
        · exact le_rfl
        · exact div_nonneg ((hρ []).1 a) (by linarith)
      · simp only [playBranch_nil, if_neg hr]
        have hsum := (hρ []).2
        have hr0 : inspectionProbability ρ = ρ [] 0 := rfl
        rw [Fin.sum_univ_three] at hsum ⊢
        simp only [inspect]
        norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]
        norm_num
        field_simp
        linarith
  · constructor
    · intro a; rw [playBranch_cons ρ h hh]; exact (hρ h).1 a
    · simp only [playBranch_cons ρ h hh]; exact (hρ h).2

@[simp] theorem inspectBranch_root (ρ : CausalPolicy Action Observation) :
    inspectionProbability (inspectBranch ρ) = 1 := by
  show inspectBranch ρ [] inspect = 1
  rw [inspectBranch_nil, if_pos rfl]

@[simp] theorem playBranch_root (ρ : CausalPolicy Action Observation) :
    inspectionProbability (playBranch ρ) = 0 := by
  show playBranch ρ [] inspect = 0
  rw [playBranch_nil]
  have hne : ¬ (inspect = play0) := by decide
  split_ifs <;> simp_all

/-- Continuation probabilities only depend on the policy at nonempty histories. -/
theorem traceProbFrom_congr_policy (π π' : CausalPolicy Action Observation)
    (Q : CausalResponse Action Observation) (hp : ∀ h a, h ≠ [] → π h a = π' h a)
    (pre rest : History) (hpre : pre ≠ []) :
    causalTraceProbFrom π Q pre rest = causalTraceProbFrom π' Q pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [hp pre ao.1 hpre, ih (pre ++ [ao]) (by simp)]

/-- Every collected record is the startup mixture of its two branch records. -/
theorem experiment_branch_mixture (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ)
    (m : ℕ) (θ : World) (u : CausalFiniteTrace Action Observation (m+1)) :
    experiment ρ (m+1) θ u =
      inspectionProbability ρ * experiment (inspectBranch ρ) (m+1) θ u +
      (1 - inspectionProbability ρ) * experiment (playBranch ρ) (m+1) θ u := by
  have ht : ∀ π' : CausalPolicy Action Observation, experiment π' (m+1) θ u =
      π' [] (u 0).1 * response θ [] (u 0).1 (u 0).2 *
        causalTraceProbFrom π' (response θ) [u 0] (List.ofFn (fun i => u i.succ)) := by
    intro π'
    change causalTraceProb π' (response θ) (List.ofFn u) = _
    rw [causalTraceProb, List.ofFn_succ]
    simp only [causalTraceProbFrom, List.nil_append]
  rw [ht, ht, ht]
  rw [traceProbFrom_congr_policy (inspectBranch ρ) ρ _
      (fun h a hh => inspectBranch_cons ρ h hh a) _ _ (by simp),
    traceProbFrom_congr_policy (playBranch ρ) ρ _
      (fun h a hh => playBranch_cons ρ h hh a) _ _ (by simp)]
  generalize ha : (u 0).1 = a
  by_cases hi : a = inspect
  · subst hi
    rw [inspectBranch_nil, if_pos rfl, show playBranch ρ [] inspect = 0 from playBranch_root ρ,
      show ρ [] inspect = inspectionProbability ρ from rfl]
    ring
  · rw [inspectBranch_nil, if_neg hi, playBranch_nil]
    by_cases h1 : inspectionProbability ρ = 1
    · have hz : ρ [] a = 0 := by
        have hsum := (hρ []).2
        have hI : ρ [] inspect = 1 := h1
        have hrest : ∑ b ∈ univ.erase inspect, ρ [] b = 0 := by
          have := Finset.add_sum_erase univ (fun b => ρ [] b) (mem_univ inspect)
          linarith
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => (hρ []).1 b)).mp hrest a
          (Finset.mem_erase.mpr ⟨hi, mem_univ a⟩)
      rw [if_pos h1, hz, h1]
      ring
    · have hlt : inspectionProbability ρ < 1 :=
        lt_of_le_of_ne (inspectionProbability_le_one ρ hρ) h1
      have hne : (1 - inspectionProbability ρ) ≠ 0 := by intro hz; linarith
      rw [if_neg h1, if_neg hi]
      field_simp
      ring

/-! ## Prior expectation of a finite-record score -/

/-- Expected finite-record score under the fixed geometric alarm prior
`α(none) = 1/2`, `α(some k) = 2^{-(k+2)}`. -/
def recordObjective (π : CausalPolicy Action Observation) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) : ℝ :=
  ∫ θ, ∑ w, experiment π t θ w * F w ∂AlarmPanelPrior.prior

/-- Every real score on the finite record alphabet has an integrable expectation. -/
theorem recordObjective_integrable (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) :
    Integrable (fun θ => ∑ w, experiment π t θ w * F w) AlarmPanelPrior.prior := by
  exact integrable_finsetSum _ fun w _ =>
    (PulseBrierScore.likelihood_integrable _ (experiment_valid π hπ t) w).mul_const (F w)

/-- Literal startup mixture, valid for any fixed finite-record score and any
adaptive continuation of a valid collector. -/
theorem recordObjective_branch_mixture (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (n : ℕ)
    (F : CausalFiniteTrace Action Observation (n+1) → ℝ) :
    recordObjective π (n+1) F =
      inspectionProbability π * recordObjective (inspectBranch π) (n+1) F +
      (1-inspectionProbability π) * recordObjective (playBranch π) (n+1) F := by
  have hi := recordObjective_integrable (inspectBranch π) (inspectBranch_valid π hπ) (n+1) F
  have hp := recordObjective_integrable (playBranch π) (playBranch_valid π hπ) (n+1) F
  have hpoint (θ : World) : (∑ w, experiment π (n+1) θ w * F w) =
      inspectionProbability π * (∑ w, experiment (inspectBranch π) (n+1) θ w * F w) +
      (1-inspectionProbability π) * (∑ w, experiment (playBranch π) (n+1) θ w * F w) := by
    simp_rw [experiment_branch_mixture π hπ n θ, add_mul, mul_assoc]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  unfold recordObjective
  simp_rw [hpoint]
  rw [integral_add (hi.const_mul _) (hp.const_mul _), integral_const_mul, integral_const_mul]

/-- A bound only on positive-mass records bounds the worldwise expectation. -/
theorem recordExpectation_le_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ) (θ : World)
    (hF : ∀ w, experiment π t θ w ≠ 0 → F w ≤ C) :
    (∑ w, experiment π t θ w * F w) ≤ C := by
  calc
    (∑ w, experiment π t θ w * F w) ≤ ∑ w, experiment π t θ w * C := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : experiment π t θ w = 0
      · simp [hw]
      · exact mul_le_mul_of_nonneg_left (hF w hw) ((experiment_valid π hπ t θ).1 w)
    _ = C := by rw [← Finset.sum_mul, (experiment_valid π hπ t θ).2, one_mul]

/-- The corresponding supported lower bound for the worldwise expectation. -/
theorem le_recordExpectation_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ) (θ : World)
    (hF : ∀ w, experiment π t θ w ≠ 0 → C ≤ F w) :
    C ≤ ∑ w, experiment π t θ w * F w := by
  calc
    C = ∑ w, experiment π t θ w * C := by
      rw [← Finset.sum_mul, (experiment_valid π hπ t θ).2, one_mul]
    _ ≤ ∑ w, experiment π t θ w * F w := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : experiment π t θ w = 0
      · simp [hw]
      · exact mul_le_mul_of_nonneg_left (hF w hw) ((experiment_valid π hπ t θ).1 w)

/-- Uniform supported-record upper bounds transfer to the actual-prior objective. -/
theorem recordObjective_le_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ)
    (hF : ∀ θ w, experiment π t θ w ≠ 0 → F w ≤ C) :
    recordObjective π t F ≤ C := by
  have h := integral_mono (recordObjective_integrable π hπ t F) (integrable_const C)
    (fun θ => recordExpectation_le_of_support π hπ t F C θ (hF θ))
  simpa [recordObjective] using h

/-- Uniform supported-record lower bounds transfer to the actual-prior objective. -/
theorem le_recordObjective_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ)
    (hF : ∀ θ w, experiment π t θ w ≠ 0 → C ≤ F w) :
    C ≤ recordObjective π t F := by
  have h := integral_mono (integrable_const C) (recordObjective_integrable π hπ t F)
    (fun θ => le_recordExpectation_of_support π hπ t F C θ (hF θ))
  simpa [recordObjective] using h

/-! ## Attainment by a deterministic finite plan -/

/-- The actual finite experiment is a world-independent mixture of deterministic
causal plans. -/
theorem experiment_kuhn (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (t : ℕ) (θ : World) (w : CausalFiniteTrace Action Observation t) :
    experiment π t θ w = ∑ τ : CausalPlan Action Observation t,
      kuhnWeight π t τ * experiment (causalPolicyOfPlan t τ) t θ w :=
  congrFun (congrFun (causalFiniteExperiment_kuhn_decomposition π hπ response t) θ) w

/-- Prior expectation preserves the causal Kuhn decomposition of the record score. -/
theorem recordObjective_kuhn (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (t : ℕ) (F : CausalFiniteTrace Action Observation t → ℝ) :
    recordObjective π t F = ∑ τ : CausalPlan Action Observation t,
      kuhnWeight π t τ * recordObjective (causalPolicyOfPlan t τ) t F := by
  have hpoint (θ : World) : (∑ w, experiment π t θ w * F w) =
      ∑ τ : CausalPlan Action Observation t,
        kuhnWeight π t τ * (∑ w, experiment (causalPolicyOfPlan t τ) t θ w * F w) := by
    simp_rw [experiment_kuhn π hπ t θ, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ _
    simp only [Finset.mul_sum, mul_assoc]
  unfold recordObjective
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun τ _ =>
    (recordObjective_integrable _ (isCausalPolicy_causalPolicyOfPlan t τ) t F).const_mul _)]
  simp only [integral_const_mul]

/-- A deterministic causal plan actually attains the maximum over all valid
adaptive policies for every fixed finite-record score. -/
theorem exists_maximizing_plan (t : ℕ) (F : CausalFiniteTrace Action Observation t → ℝ) :
    ∃ τ : CausalPlan Action Observation t, ∀ ρ : CausalPolicy Action Observation,
      IsCausalPolicy ρ → recordObjective ρ t F ≤ recordObjective (causalPolicyOfPlan t τ) t F := by
  obtain ⟨τ, _, hτ⟩ := Finset.exists_max_image
    (Finset.univ : Finset (CausalPlan Action Observation t))
    (fun τ => recordObjective (causalPolicyOfPlan t τ) t F) Finset.univ_nonempty
  refine ⟨τ, fun ρ hρ => ?_⟩
  rw [recordObjective_kuhn ρ hρ t F]
  calc
    (∑ σ : CausalPlan Action Observation t,
        kuhnWeight ρ t σ * recordObjective (causalPolicyOfPlan t σ) t F) ≤
      ∑ σ : CausalPlan Action Observation t,
        kuhnWeight ρ t σ * recordObjective (causalPolicyOfPlan t τ) t F := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hτ σ (Finset.mem_univ σ)) (kuhnWeight_nonneg ρ hρ t σ)
    _ = _ := by rw [← Finset.sum_mul, (kuhnWeight_isDist ρ hρ t).2, one_mul]

end IdExp.PairedAlarm.PseudoCount
