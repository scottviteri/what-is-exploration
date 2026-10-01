import Formal.AlarmPanelVariantChain

/-!
# Startup-family reference calculations

Checks actual finite-record branch expectations and geometric-prior integration,
the three-action collector mixture, closed-simplex optimizer/error classification
when both PLAY reference values coincide, and finite-softmax endpoint qualification.
The integrated reference values come from one fixed record reward:
this file does not verify the Python evaluator, infer branch symmetry for an
arbitrary policy-dependent reward, or prove sampled training convergence.
-/

noncomputable section
namespace IdExp
open Finset MeasureTheory

namespace AlarmPanel

/-- Expected value of a fixed record reward, conditional on one world. -/
def finiteRecordReward (v : Variant) (π : CausalPolicy Action Observation)
    (m : ℕ) (θ : World) (reward : CausalFiniteTrace Action Observation (m+1) → ℝ) : ℝ :=
  ∑ u, experimentV v π (m+1) θ u * reward u

/-- Actual causal records give the affine startup decomposition. The same
record reward is used on all branches, including any deterministic learner updates. -/
theorem finiteRecordReward_branch_mixture (v : Variant)
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (m : ℕ) (θ : World) (reward : CausalFiniteTrace Action Observation (m+1) → ℝ) :
    finiteRecordReward v π m θ reward =
      inspectionProbability π * finiteRecordReward v (inspectBranch π) m θ reward +
      (1-inspectionProbability π) * finiteRecordReward v (playBranch π) m θ reward := by
  unfold finiteRecordReward
  simp_rw [experimentV_branch_mixture v π hπ m θ, add_mul, mul_assoc]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]


/-- Every finite-record reward is integrable under the actual countable prior.
No boundedness or integrability premise is needed beyond a real reward on the
finite record alphabet and validity of the response and policy. -/
theorem finiteRecordReward_integrable (v : Variant) (hv : v.Valid)
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (m : ℕ) (reward : CausalFiniteTrace Action Observation (m+1) → ℝ) :
    Integrable (fun θ => finiteRecordReward v π m θ reward) AlarmPanelPrior.prior := by
  unfold finiteRecordReward
  exact integrable_finsetSum _ fun u _ =>
    (PulseBrierScore.likelihood_integrable _ (experimentV_valid v hv π hπ (m+1)) u).mul_const
      (reward u)

/-- Prior-averaged finite return of one fixed record reward. -/
def priorRecordReward (v : Variant) (π : CausalPolicy Action Observation)
    (m : ℕ) (reward : CausalFiniteTrace Action Observation (m+1) → ℝ) : ℝ :=
  ∫ θ, finiteRecordReward v π m θ reward ∂AlarmPanelPrior.prior

/-- The actual prior-averaged return has the same startup branch decomposition.
Both branch integrability obligations are discharged for the geometric prior. -/
theorem priorRecordReward_branch_mixture (v : Variant) (hv : v.Valid)
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (m : ℕ) (reward : CausalFiniteTrace Action Observation (m+1) → ℝ) :
    priorRecordReward v π m reward =
      inspectionProbability π * priorRecordReward v (inspectBranch π) m reward +
      (1-inspectionProbability π) * priorRecordReward v (playBranch π) m reward := by
  have hi := finiteRecordReward_integrable v hv (inspectBranch π) (inspectBranch_valid π hπ)
    m reward
  have hp := finiteRecordReward_integrable v hv (playBranch π) (playBranch_valid π hπ)
    m reward
  unfold priorRecordReward
  simp_rw [finiteRecordReward_branch_mixture v π hπ m _ reward]
  rw [integral_add (hi.const_mul _) (hp.const_mul _), integral_const_mul, integral_const_mul]

end AlarmPanel

namespace StartupPolicyReferences

abbrev Startup := Fin 3 → ℝ

/-- Conditional startup means, with the two PLAY means equal. -/
def score (inspectValue playValue : ℝ) (p : Startup) : ℝ :=
  ∑ a, p a * (if a = 0 then inspectValue else playValue)

/-- Analytic inspection deficiency of an alarm collector. -/
def error (p : Startup) : ℝ := (1-p 0)/2

/-- One actual startup distribution for each inspection probability. -/
def mixture (s : ℝ) : Startup := fun a => if a = 0 then s else (1-s)/2

@[simp] theorem mixture_inspect (s : ℝ) : mixture s 0 = s := by simp [mixture]

theorem mixture_valid (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) : IsDist (mixture s) := by
  constructor
  · intro a
    unfold mixture
    split_ifs <;> linarith
  · simp [mixture, Fin.sum_univ_three]
    ring

theorem inspection_le_one (p : Startup) (hp : IsDist p) : p 0 ≤ 1 := by
  have hsum := hp.2
  simp only [Fin.sum_univ_three] at hsum
  linarith [hp.1 1, hp.1 2]

/-- The three-action expected reference reward reduces to the affine form. -/
theorem score_eq (inspectValue playValue : ℝ) (p : Startup) (hp : IsDist p) :
    score inspectValue playValue p = p 0 * inspectValue + (1-p 0) * playValue := by
  have hsum := hp.2
  simp only [Fin.sum_univ_three] at hsum
  have hs : p 1 + p 2 = 1 - p 0 := by linarith
  calc
    score inspectValue playValue p = p 0 * inspectValue + (p 1 + p 2) * playValue := by
      simp [score, Fin.sum_univ_three]
      ring
    _ = _ := by rw [hs]

/-- Reference values enter through an explicit equality of the two PLAY
returns; the theorem does not establish that symmetry for a reward evaluator. -/
theorem score_of_equal_play (values p : Startup) (hplay : values 1 = values 2) :
    (∑ a, p a * values a) = score (values 0) (values 1) p := by
  simp [score, Fin.sum_univ_three, ← hplay]

/-- Literal fixed-continuation collector: the startup distribution is learned,
and every later action is an independent fair choice of the two PLAY actions. -/
def collector (p : Startup) : CausalPolicy AlarmPanel.Action AlarmPanel.Observation :=
  fun h => if h = [] then p else mixture 0

theorem collector_valid (p : Startup) (hp : IsDist p) : IsCausalPolicy (collector p) := by
  intro h
  unfold collector
  split_ifs
  · exact hp
  · exact mixture_valid 0 le_rfl (by norm_num)

@[simp] theorem collector_inspection (p : Startup) :
    AlarmPanel.inspectionProbability (collector p) = p 0 := by
  simp [collector, AlarmPanel.inspectionProbability, AlarmPanel.inspect]

/-- A forced startup action; continuation is still supplied by `collector`. -/
def forcedStartup (a : Fin 3) : Startup := fun b => if b = a then 1 else 0

theorem forcedStartup_valid (a : Fin 3) : IsDist (forcedStartup a) := by
  constructor
  · intro b; simp only [forcedStartup]; split_ifs <;> norm_num
  · simp [forcedStartup]

/-- The literal collector record is the mixture of its three forced-startup
records. The full retained action labels are included. -/
theorem collector_experiment_mixture (v : AlarmPanel.Variant) (p : Startup)
    (m : ℕ) (θ : AlarmPanel.World)
    (u : CausalFiniteTrace AlarmPanel.Action AlarmPanel.Observation (m+1)) :
    AlarmPanel.experimentV v (collector p) (m+1) θ u =
      ∑ a, p a * AlarmPanel.experimentV v (collector (forcedStartup a)) (m+1) θ u := by
  have ht (q : Startup) : AlarmPanel.experimentV v (collector q) (m+1) θ u =
      q (u 0).1 * AlarmPanel.responseV v θ [] (u 0).1 (u 0).2 *
        causalTraceProbFrom (collector p) (AlarmPanel.responseV v θ) [u 0]
          (List.ofFn (fun i => u i.succ)) := by
    change causalTraceProb (collector q) (AlarmPanel.responseV v θ) (List.ofFn u) = _
    rw [causalTraceProb, List.ofFn_succ]
    simp only [causalTraceProbFrom, List.nil_append]
    rw [AlarmPanel.traceProbFrom_congr_policy (collector q) (collector p) _
      (fun h a hh => by simp [collector, hh]) _ _ (by simp)]
    simp [collector]
  simp_rw [ht]
  simp [forcedStartup, ite_mul, mul_ite]
  split_ifs <;> ring

/-- Worldwise finite return with one fixed reward on the full record. -/
theorem collector_finiteReward_mixture (v : AlarmPanel.Variant) (p : Startup)
    (m : ℕ) (θ : AlarmPanel.World)
    (reward : CausalFiniteTrace AlarmPanel.Action AlarmPanel.Observation (m+1) → ℝ) :
    AlarmPanel.finiteRecordReward v (collector p) m θ reward =
      ∑ a, p a * AlarmPanel.finiteRecordReward v (collector (forcedStartup a)) m θ reward := by
  unfold AlarmPanel.finiteRecordReward
  simp_rw [collector_experiment_mixture v p m θ, sum_mul, mul_assoc]
  rw [sum_comm]
  simp_rw [mul_sum]

/-- Prior integration preserves the three forced-startup reference values;
all finite-record integrability obligations are discharged. -/
theorem collector_priorReward_mixture (v : AlarmPanel.Variant) (hv : v.Valid)
    (p : Startup) (m : ℕ)
    (reward : CausalFiniteTrace AlarmPanel.Action AlarmPanel.Observation (m+1) → ℝ) :
    AlarmPanel.priorRecordReward v (collector p) m reward =
      ∑ a, p a * AlarmPanel.priorRecordReward v (collector (forcedStartup a)) m reward := by
  unfold AlarmPanel.priorRecordReward
  simp_rw [collector_finiteReward_mixture v p m _ reward]
  rw [integral_finsetSum _ (fun a _ =>
    (AlarmPanel.finiteRecordReward_integrable v hv _
      (collector_valid _ (forcedStartup_valid a)) m reward).const_mul (p a))]
  simp_rw [integral_const_mul]

/-- The actual integrated collector return equals the optimized affine score
when its two forced PLAY reference values coincide. This premise concerns the
specified record reward; it is not silently assumed for every evaluator. -/
theorem collector_priorReward_eq_score (v : AlarmPanel.Variant) (hv : v.Valid)
    (p : Startup) (m : ℕ)
    (reward : CausalFiniteTrace AlarmPanel.Action AlarmPanel.Observation (m+1) → ℝ)
    (hplay : AlarmPanel.priorRecordReward v (collector (forcedStartup 1)) m reward =
      AlarmPanel.priorRecordReward v (collector (forcedStartup 2)) m reward) :
    AlarmPanel.priorRecordReward v (collector p) m reward =
      score (AlarmPanel.priorRecordReward v (collector (forcedStartup 0)) m reward)
        (AlarmPanel.priorRecordReward v (collector (forcedStartup 1)) m reward) p := by
  rw [collector_priorReward_mixture v hv]
  exact score_of_equal_play _ p hplay

/-- The generic error coordinate is the actual all-world inspection deficiency
of the frozen fixed-continuation collector at every positive collection time. -/
theorem collector_inspection_deficiency (v : AlarmPanel.Variant) (hv : v.Valid)
    (p : Startup) (hp : IsDist p) (n : ℕ) :
    finiteDeficiency (AlarmPanel.experimentV v (collector p) (n+1))
      (AlarmPanel.experimentV v AlarmPanel.inspectPolicy 1) = error p := by
  rw [AlarmPanel.inspection_deficiencyV_exact v hv _ (collector_valid p hp) n,
    collector_inspection]
  rfl

/-- A closed-family reference optimum includes deterministic endpoints. -/
def Maximizes (inspectValue playValue : ℝ) (p : Startup) : Prop :=
  ∀ q : Startup, IsDist q → score inspectValue playValue q ≤ score inspectValue playValue p

theorem maximizes_iff_inspects (inspectValue playValue : ℝ) (h : playValue < inspectValue)
    (p : Startup) (hp : IsDist p) :
    Maximizes inspectValue playValue p ↔ p 0 = 1 := by
  constructor
  · intro hm
    have hb := hm (mixture 1) (mixture_valid 1 (by norm_num) le_rfl)
    rw [score_eq _ _ _ (mixture_valid 1 (by norm_num) le_rfl), score_eq _ _ _ hp,
      mixture_inspect] at hb
    have := inspection_le_one p hp
    nlinarith
  · intro hs q hq
    rw [score_eq _ _ _ hq, score_eq _ _ _ hp, hs]
    have := inspection_le_one q hq
    nlinarith

theorem maximizes_iff_plays (inspectValue playValue : ℝ) (h : inspectValue < playValue)
    (p : Startup) (hp : IsDist p) :
    Maximizes inspectValue playValue p ↔ p 0 = 0 := by
  constructor
  · intro hm
    have hb := hm (mixture 0) (mixture_valid 0 le_rfl (by norm_num))
    rw [score_eq _ _ _ (mixture_valid 0 le_rfl (by norm_num)), score_eq _ _ _ hp,
      mixture_inspect] at hb
    nlinarith [hp.1 0]
  · intro hs q hq
    rw [score_eq _ _ _ hq, score_eq _ _ _ hp, hs]
    nlinarith [hq.1 0]

theorem maximizes_of_equal (value : ℝ) (p : Startup) (hp : IsDist p) :
    Maximizes value value p := by
  intro q hq
  rw [score_eq _ _ _ hq, score_eq _ _ _ hp]
  ring_nf
  exact le_rfl

theorem error_mem_interval (p : Startup) (hp : IsDist p) : error p ∈ Set.Icc (0 : ℝ) (1/2) := by
  have := inspection_le_one p hp
  have := hp.1 0
  simp only [Set.mem_Icc, error]
  constructor <;> linarith

/-- Every claimed error is attained by a closed-simplex startup distribution. -/
theorem exists_error_iff (d : ℝ) :
    (∃ p : Startup, IsDist p ∧ error p = d) ↔ d ∈ Set.Icc (0 : ℝ) (1/2) := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact error_mem_interval p hp
  · intro hd
    refine ⟨mixture (1-2*d), mixture_valid _ (by linarith [hd.2]) (by linarith [hd.1]), ?_⟩
    simp [error]

theorem tied_optimal_error_iff (value d : ℝ) :
    (∃ p : Startup, IsDist p ∧ Maximizes value value p ∧ error p = d) ↔
      d ∈ Set.Icc (0 : ℝ) (1/2) := by
  constructor
  · rintro ⟨p, hp, _, he⟩
    exact (exists_error_iff d).1 ⟨p, hp, he⟩
  · intro hd
    obtain ⟨p, hp, he⟩ := (exists_error_iff d).2 hd
    exact ⟨p, hp, maximizes_of_equal value p hp, he⟩

theorem inspect_optimal_error_iff (inspectValue playValue d : ℝ) (h : playValue < inspectValue) :
    (∃ p : Startup, IsDist p ∧ Maximizes inspectValue playValue p ∧ error p = d) ↔ d = 0 := by
  constructor
  · rintro ⟨p, hp, hm, he⟩
    have hs := (maximizes_iff_inspects inspectValue playValue h p hp).1 hm
    simpa [error, hs] using he.symm
  · intro hd
    subst d
    have hp := mixture_valid 1 (by norm_num) le_rfl
    exact ⟨mixture 1, hp, (maximizes_iff_inspects inspectValue playValue h _ hp).2
      (mixture_inspect 1), by norm_num [error]⟩

theorem play_optimal_error_iff (inspectValue playValue d : ℝ) (h : inspectValue < playValue) :
    (∃ p : Startup, IsDist p ∧ Maximizes inspectValue playValue p ∧ error p = d) ↔ d = 1/2 := by
  constructor
  · rintro ⟨p, hp, hm, he⟩
    have hs := (maximizes_iff_plays inspectValue playValue h p hp).1 hm
    simpa [error, hs] using he.symm
  · intro hd
    subst d
    have hp := mixture_valid 0 le_rfl (by norm_num)
    exact ⟨mixture 0, hp, (maximizes_iff_plays inspectValue playValue h _ hp).2
      (mixture_inspect 0), by norm_num [error]⟩

/-- The finite three-logit startup parametrization. -/
def softmax (u : Startup) : Startup := fun a => Real.exp (u a) / ∑ b, Real.exp (u b)

theorem softmax_normalizer_pos (u : Startup) : 0 < ∑ b, Real.exp (u b) := by
  exact sum_pos (fun b _ => Real.exp_pos _) univ_nonempty

theorem softmax_pos (u : Startup) (a : Fin 3) : 0 < softmax u a :=
  div_pos (Real.exp_pos _) (softmax_normalizer_pos u)

theorem softmax_valid (u : Startup) : IsDist (softmax u) := by
  constructor
  · intro a; exact (softmax_pos u a).le
  · simp only [softmax, ← sum_div]
    exact div_self (softmax_normalizer_pos u).ne'

theorem softmax_lt_one (u : Startup) (a : Fin 3) : softmax u a < 1 := by
  apply (div_lt_one (softmax_normalizer_pos u)).2
  simp only [Fin.sum_univ_three]
  fin_cases a
  · change Real.exp (u 0) < Real.exp (u 0) + Real.exp (u 1) + Real.exp (u 2)
    linarith [Real.exp_pos (u 1), Real.exp_pos (u 2)]
  · change Real.exp (u 1) < Real.exp (u 0) + Real.exp (u 1) + Real.exp (u 2)
    linarith [Real.exp_pos (u 0), Real.exp_pos (u 2)]
  · change Real.exp (u 2) < Real.exp (u 0) + Real.exp (u 1) + Real.exp (u 2)
    linarith [Real.exp_pos (u 0), Real.exp_pos (u 1)]

/-- Finite logits cannot attain a strict closed-family endpoint optimum.
This is a parametrization fact, not a training convergence theorem. -/
theorem softmax_not_maximizes (inspectValue playValue : ℝ) (hne : inspectValue ≠ playValue)
    (u : Startup) : ¬ Maximizes inspectValue playValue (softmax u) := by
  intro hm
  rcases lt_or_gt_of_ne hne with h | h
  · have hz := (maximizes_iff_plays inspectValue playValue h _ (softmax_valid u)).1 hm
    have := softmax_pos u 0
    linarith
  · have ho := (maximizes_iff_inspects inspectValue playValue h _ (softmax_valid u)).1 hm
    have := softmax_lt_one u 0
    linarith

@[simp] theorem softmax_zero (a : Fin 3) : softmax (fun _ => 0) a = 1/3 := by
  norm_num [softmax, Fin.sum_univ_three]

@[simp] theorem initial_error : error (softmax (fun _ => 0)) = 1/3 := by
  norm_num [error]

/-- The supplied inspection reward's mean is its startup probability. -/
theorem inspection_control (p : Startup) : score 1 0 p = p 0 := by
  simp [score]

end StartupPolicyReferences
end IdExp
