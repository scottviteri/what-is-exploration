import Formal.AlarmPanelNativeFailure
import Formal.PredictiveTransport
import Formal.FiniteDecoderAttainment

/-! Sharp native audit, with the source and target at their literal horizons.
A world-independent decoder guesses the missing bit and replays every known
monitor coordinate, while regenerating the panel's known random colors. -/
noncomputable section
namespace IdExp.AlarmPanel
open Finset

 def Compatible (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (b : Bool) (θ : World) : Prop :=
   θ.isSome = b ∧ ∀ k (hk : 2*k+2 < n+1), (h ⟨2*k+2,hk⟩).2 = monitorLabel θ k

 def compatibleWorld (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1)) (b : Bool) : World := by
   classical
   exact if hh : ∃ θ, Compatible n h b θ then Classical.choose hh else none

 theorem supported_compatible (π : CausalPolicy Action Observation) (θ : World)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment π (n+1) θ h ≠ 0) : Compatible n h θ.isSome θ :=
  ⟨rfl, fun k hk => supported_monitor π θ (n+1) k hk h hh⟩

 theorem compatibleWorld_correct (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (θ : World) (hh : Compatible n h θ.isSome θ) :
    Compatible n h θ.isSome (compatibleWorld n h θ.isSome) := by
  classical
  have hex : ∃ η, Compatible n h θ.isSome η := ⟨θ,hh⟩
  simp only [compatibleWorld, dif_pos hex]
  exact Classical.choose_spec hex

 theorem compatible_experiment_eq (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (b : Bool) {θ η : World} (hθ : Compatible n h b θ) (hη : Compatible n h b η)
    (ρ : CausalPolicy Action Observation) (m : ℕ) (hm : m ≤ n+1) :
    experiment ρ m θ = experiment ρ m η := by
  have hb : θ.isSome = η.isSome := hθ.1.trans hη.1.symm
  have hmon : MonitorEquivalent (n+1) θ η := by
    intro k hk
    have he := (hθ.2 k hk).symm.trans (hη.2 k hk)
    by_cases hx : θ = some k <;> by_cases hy : η = some k <;>
      simp_all [monitorLabel]
  funext w
  apply traceProbFrom_congr_before ρ (response θ) (response η) m
  · intro pre hpre a
    by_cases hp : pre = []
    · subst pre; funext o; simp only [response_root, hb]
    · exact response_eq_of_monitors (n+1) hmon pre
        (by have := List.length_pos_iff.mpr hp; exact this) (by omega) a
  · simp

 theorem supported_inspection_bit (π : CausalPolicy Action Observation) (θ : World)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment π (n+1) θ h ≠ 0) (hi : (h 0).1 = inspect) :
    decide (2 ≤ (h 0).2.val) = θ.isSome := by
  have he := experiment_response_ne_zero π θ (n+1) h hh 0
  simp only [Fin.val_zero, List.take_zero, response_root, hi, ↓reduceIte] at he
  have ho := (h 0).2.isLt
  cases hb : θ.isSome <;>
    simp only [hb, pairDist, Bool.false_eq_true, ↓reduceIte] at he ⊢
  · have hv : (h 0).2.val / 2 = 0 := by by_contra hv; simp [hv] at he
    have hv' : ¬2 ≤ (h 0).2.val := by omega
    simp [hv']
  · have hv : (h 0).2.val / 2 = 1 := by by_contra hv; simp [hv] at he
    have hv' : 2 ≤ (h 0).2.val := by omega
    simp [hv']

 def guessedReplay (ρ : CausalPolicy Action Observation) (m n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1)) (b : Bool) :=
   experiment ρ m (compatibleWorld n h b)

 def auditReplay (ρ : CausalPolicy Action Observation) (m n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    : CausalFiniteTrace Action Observation m → ℝ :=
   if (h 0).1 = inspect then guessedReplay ρ m n h (decide (2 ≤ (h 0).2.val))
   else fun u => (guessedReplay ρ m n h false u + guessedReplay ρ m n h true u)/2

 theorem auditReplay_valid (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ)
    (m n : ℕ) : auditReplay ρ m n ∈ stochasticRules _ _ := by
  intro h _
  by_cases hi : (h 0).1 = inspect
  · simpa only [auditReplay, if_pos hi, guessedReplay] using experiment_valid ρ hρ m (compatibleWorld n h (decide (2 ≤ (h 0).2.val)))
  · constructor
    · intro u
      simp only [auditReplay, if_neg hi]
      exact div_nonneg (add_nonneg (experiment_valid ρ hρ m _ |>.1 u)
        (experiment_valid ρ hρ m _ |>.1 u)) (by norm_num)
    · simp only [auditReplay, if_neg hi, ← Finset.sum_div, Finset.sum_add_distrib, guessedReplay]
      rw [(experiment_valid ρ hρ m _).2, (experiment_valid ρ hρ m _).2]
      norm_num

 theorem half_mixture_tv {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : IsDist p) (hq : IsDist q) : finiteTV (fun x => (p x+q x)/2) p ≤ 1/2 := by
  have he : finiteTV (fun x => (p x+q x)/2) p = finiteTV q p /2 := by
    unfold finiteTV
    have ht (x : X) : |(p x+q x)/2-p x| = |q x-p x|/2 := by
      rw [show (p x+q x)/2-p x = (q x-p x)/2 by ring, abs_div]
      norm_num
    simp_rw [ht]
    rw [← Finset.sum_div]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right (finiteTV_le_one_of_isDist q p hq hp) (by norm_num)

 theorem guessedReplay_correct (π ρ : CausalPolicy Action Observation) (θ : World)
    (m n : ℕ) (hm : m ≤ n+1) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment π (n+1) θ h ≠ 0) : guessedReplay ρ m n h θ.isSome = experiment ρ m θ := by
  exact compatible_experiment_eq n h θ.isSome
    (compatibleWorld_correct n h θ (supported_compatible π θ n h hh))
    (supported_compatible π θ n h hh) ρ m hm

 theorem auditReplay_row_bound (π ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ)
    (θ : World) (m n : ℕ) (hm : m ≤ n+1)
    (h : CausalFiniteTrace Action Observation (n+1)) (hh : experiment π (n+1) θ h ≠ 0) :
    finiteTV (auditReplay ρ m n h) (experiment ρ m θ) ≤
      if (h 0).1 = inspect then 0 else 1/2 := by
  have hc := guessedReplay_correct π ρ θ m n hm h hh
  by_cases hi : (h 0).1 = inspect
  · simp only [auditReplay, if_pos hi, supported_inspection_bit π θ n h hh hi]
    rw [hc]
    simp [finiteTV]
  · simp only [auditReplay, if_neg hi]
    cases hb : θ.isSome
    · rw [hb] at hc
      rw [hc]
      exact half_mixture_tv _ _ (experiment_valid ρ hρ m θ) (experiment_valid ρ hρ m _)
    · rw [hb] at hc
      rw [hc]
      have he : (fun u => (guessedReplay ρ m n h false u + experiment ρ m θ u)/2) =
          (fun u => (experiment ρ m θ u + guessedReplay ρ m n h false u)/2) := by funext u; ring
      rw [he]
      exact half_mixture_tv _ _ (experiment_valid ρ hρ m θ) (experiment_valid ρ hρ m _)

/-- Every finite native record within the observed horizon can be simulated
with the same sharp missing-bit bound. -/
 theorem auditReplay_error_le (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m ≤ n+1) (θ : World) :
    decodeErr (experiment π (n+1)) (experiment ρ m) (auditReplay ρ m n) θ ≤
      (1-inspectionProbability π)/2 := by
  apply (PredictiveTransport.decodeErr_le_weighted_rowTV _ (experiment_valid π hπ _) _ _ θ).trans
  calc
    _ ≤ ∑ h : CausalFiniteTrace Action Observation (n+1),
        experiment π (n+1) θ h * (if (h 0).1 = inspect then 0 else 1/2) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hh : experiment π (n+1) θ h = 0
      · simp [hh]
      · exact mul_le_mul_of_nonneg_left (auditReplay_row_bound π ρ hρ θ m n hm h hh)
          ((experiment_valid π hπ _ θ).1 h)
    _ = _ := by
      have ht (h : CausalFiniteTrace Action Observation (n+1)) :
          experiment π (n+1) θ h * (if (h 0).1 = inspect then 0 else 1/2) =
          (experiment π (n+1) θ h - (if (h 0).1 = inspect then experiment π (n+1) θ h else 0))/2 := by
        split_ifs <;> ring
      simp_rw [ht]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, (experiment_valid π hπ _ θ).2,
        rootInspection_mass π hπ θ n]

 theorem policy_deficiency_le (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m ≤ n+1) :
    finiteDeficiency (experiment π (n+1)) (experiment ρ m) ≤ (1-inspectionProbability π)/2 :=
  finiteDeficiency_le_of_decoder _ _ (auditReplay ρ m n) (auditReplay_valid ρ hρ m n) _
    (auditReplay_error_le π ρ hπ hρ m n hm)

 theorem alwaysInspect_blackwell (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m ≤ n+1)
    (hs : inspectionProbability π = 1) :
    FiniteBlackwellLE (experiment ρ m) (experiment π (n+1)) := by
  refine ⟨auditReplay ρ m n, auditReplay_valid ρ hρ m n, ?_⟩
  funext θ u
  have he := auditReplay_error_le π ρ hπ hρ m n hm θ
  rw [hs] at he
  norm_num at he
  exact (decodeErr_eq_zero_iff _ _ _ θ).1
    (le_antisymm he (decodeErr_nonneg _ _ _ θ)) u

/-- The exact finite audit includes every native target up to depth `m`.
Both horizon bounds are essential: `1 ≤ m ≤ n+1`. -/
 theorem native_audit_exact (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (m n : ℕ) (hm0 : 1 ≤ m) (hm : m ≤ n+1) :
    causalNativeDeficiencyUpTo (experiment π (n+1)) response m = (1-inspectionProbability π)/2 := by
  apply le_antisymm
  · apply (causalNativeDeficiency_le_iff_all_policy _ (experiment_valid π hπ _) response response_valid m _).2
    intro ρ hρ t ht
    exact policy_deficiency_le π ρ hπ hρ t n (by omega)
  · rw [← inspection_deficiency_exact π hπ n]
    rw [causalNativeDeficiencyUpTo_eq_terminal _ (experiment_valid π hπ _) response response_valid]
    exact finiteDeficiency_causalPolicy_le_native_of_le _ (experiment_valid π hπ _)
      inspectPolicy inspectPolicy_valid response response_valid hm0


@[simp] theorem inspectPolicy_inspectionProbability : inspectionProbability inspectPolicy = 1 := by
  simp [inspectionProbability, inspectPolicy, detPolicy]

 theorem sufficient_iff_inspectionProbability_one (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) :
    CausalNativelySufficient response ⟨π,hπ⟩ ↔ inspectionProbability π = 1 := by
  rw [causalNativelySufficient_iff_finitarilyGreatest response response_valid]
  constructor
  · intro hg
    have hs := inspectionProbability_le_one π hπ
    by_contra hsne
    have hslt : inspectionProbability π < 1 := lt_of_le_of_ne hs hsne
    obtain ⟨T,hT⟩ := hg ⟨inspectPolicy,inspectPolicy_valid⟩ 1
      ((1-inspectionProbability π)/4) (by linarith)
    have hbad := hT (T+1) (by omega)
    change finiteDeficiency (experiment π (T+1)) (experiment inspectPolicy 1) < _ at hbad
    rw [inspection_deficiency_exact π hπ T] at hbad
    linarith
  · intro hs ρ m ε hε
    refine ⟨max m 1, ?_⟩
    intro t ht
    cases t with
    | zero => omega
    | succ n =>
      have hb := policy_deficiency_le π ρ.1 hπ ρ.2 m n (by omega)
      rw [hs] at hb
      norm_num at hb
      exact lt_of_le_of_lt hb hε

 theorem inspection_natively_sufficient :
    CausalNativelySufficient response ⟨inspectPolicy,inspectPolicy_valid⟩ :=
  (sufficient_iff_inspectionProbability_one inspectPolicy inspectPolicy_valid).2
    inspectPolicy_inspectionProbability

 theorem inspection_finitarily_greatest :
    CausalFinitarilyGreatest response ⟨inspectPolicy,inspectPolicy_valid⟩ :=
  (causalNativelySufficient_iff_finitarilyGreatest response response_valid _).1
    inspection_natively_sufficient

/-- Every non-inspecting root mixture is strictly dominated by the displayed
sufficient policy, including arbitrary randomized adaptive continuations. -/
 theorem inspection_strictly_dominates (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hs : inspectionProbability π < 1) :
    CausalFinitaryDominates response ⟨inspectPolicy,inspectPolicy_valid⟩ ⟨π,hπ⟩ ∧
      ¬ CausalFinitaryDominates response ⟨π,hπ⟩ ⟨inspectPolicy,inspectPolicy_valid⟩ := by
  refine ⟨inspection_finitarily_greatest ⟨π,hπ⟩, ?_⟩
  intro hd
  obtain ⟨T,hT⟩ := hd 1 ((1-inspectionProbability π)/4) (by linarith)
  have hbad := hT (T+1) (by omega)
  change finiteDeficiency (experiment π (T+1)) (experiment inspectPolicy 1) < _ at hbad
  rw [inspection_deficiency_exact π hπ T] at hbad
  linarith

/-- Inspection already simulates every policy at the same positive horizon. -/
 theorem inspection_same_horizon_deficiency_zero (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    finiteDeficiency (experiment inspectPolicy (n+1)) (experiment ρ (n+1)) = 0 := by
  apply le_antisymm
  · have hb := policy_deficiency_le inspectPolicy ρ inspectPolicy_valid hρ (n+1) n le_rfl
    simpa using hb
  · exact finiteDeficiency_nonneg_of_valid _ _ (experiment_valid inspectPolicy inspectPolicy_valid _)
      (experiment_valid ρ hρ _)


 theorem inspection_same_horizon_replay_law (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    finiteDecisionLaw (experiment inspectPolicy (n+1)) (auditReplay ρ (n+1) n) = experiment ρ (n+1) := by
  funext θ u
  unfold finiteDecisionLaw
  have he : ∀ h, experiment inspectPolicy (n+1) θ h * auditReplay ρ (n+1) n h u =
      experiment inspectPolicy (n+1) θ h * experiment ρ (n+1) θ u := by
    intro h
    by_cases hh : experiment inspectPolicy (n+1) θ h = 0
    · simp [hh]
    · have hi := (inspect_supported_root θ (n+1) (by omega) h hh).1
      change (h 0).1 = inspect at hi
      simp only [auditReplay, if_pos hi, supported_inspection_bit inspectPolicy θ n h hh hi]
      rw [guessedReplay_correct inspectPolicy ρ θ (n+1) n le_rfl h hh]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid inspectPolicy inspectPolicy_valid _ θ).2, one_mul]

 theorem inspection_same_horizon_blackwell (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    FiniteBlackwellLE (experiment ρ (n+1)) (experiment inspectPolicy (n+1)) :=
  ⟨auditReplay ρ (n+1) n, auditReplay_valid ρ hρ (n+1) n,
    inspection_same_horizon_replay_law ρ hρ n⟩


 theorem row_none_zero_if_inspected (π : CausalPolicy Action Observation) (k n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment π (n+1) (some k) h ≠ 0) (hi : (h 0).1 = inspect) :
    experiment π (n+1) none h = 0 := by
  by_contra hn
  have hkbit := supported_inspection_bit π (some k) n h hh hi
  have hnbit := supported_inspection_bit π none n h hn hi
  simp only [Option.isSome_none, Option.isSome_some] at hkbit hnbit
  rw [hnbit] at hkbit
  contradiction

end IdExp.AlarmPanel
