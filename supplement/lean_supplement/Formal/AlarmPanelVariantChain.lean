import Formal.AlarmPanelVariantVariance

/-!
# The exact all-policy chain on the alarm/panel interface

For any two randomized history policies with startup inspection probabilities
`s` (source) and `r` (target), and source horizon at least the positive target
horizon, the directed deficiency is exactly `max (r - s) 0 / 2`, in every valid
variant. Startup inspection probability therefore orders every policy.

Lower bound: the never world and a pulse world later than both horizons have
uninspected rows in common; their target rows differ by `r` and their source
rows by `s`, so any decoder has error at least `(r - s)/2` by contraction and
the triangle inequality. Upper bound: the target record is the root mixture of
its inspection branch and its play branch. Inspected source records simulate
either branch exactly; uninspected records simulate the play branch exactly and
the inspection branch with a fair guess of the bit. Allocating inspected source
mass to the target's inspection branch first leaves guessing only on the mass
`max (r - s) 0`, at error one half.
-/

noncomputable section
namespace IdExp.AlarmPanel
open Finset

variable (v : Variant)

/-! ## Total-variation tools -/

/-- A stochastic rule contracts total variation between two rows. -/
theorem finiteTV_decision_le {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    finiteTV (fun y => ∑ x, p x * G x y) (fun y => ∑ x, q x * G x y) ≤ finiteTV p q := by
  unfold finiteTV
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ y, |(∑ x, p x * G x y) - ∑ x, q x * G x y|)
        = ∑ y, |∑ x, (p x - q x) * G x y| := by
          apply sum_congr rfl; intro y _
          rw [← sum_sub_distrib]
          congr 1; apply sum_congr rfl; intro x _; ring
    _ ≤ ∑ y, ∑ x, |p x - q x| * G x y := by
          apply sum_le_sum; intro y _
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          apply sum_le_sum; intro x _
          rw [abs_mul, abs_of_nonneg ((hG x (Set.mem_univ _)).1 y)]
    _ = ∑ x, |p x - q x| * ∑ y, G x y := by
          rw [sum_comm]; apply sum_congr rfl; intro x _; rw [mul_sum]
    _ = ∑ x, |p x - q x| := by
          apply sum_congr rfl; intro x _; rw [(hG x (Set.mem_univ _)).2, mul_one]

theorem decodeErr_eq_finiteTV {Θ X Y : Type*} [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) (θ : Θ) :
    decodeErr E F G θ = finiteTV (finiteDecisionLaw E G θ) (F θ) := rfl

/-! ## Branch policies of the target -/

/-- The target with its root forced to inspect; later choices unchanged. -/
def inspectBranch (ρ : CausalPolicy Action Observation) : CausalPolicy Action Observation :=
  fun h a => if h = [] then (if a = inspect then 1 else 0) else ρ h a

/-- The target with its root conditioned on not inspecting; later choices unchanged.
When the target always inspects, an arbitrary play root is used with weight zero. -/
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

/-- The target record is the root mixture of its two branch records. -/
theorem experimentV_branch_mixture (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ)
    (m : ℕ) (θ : World) (u : CausalFiniteTrace Action Observation (m+1)) :
    experimentV v ρ (m+1) θ u =
      inspectionProbability ρ * experimentV v (inspectBranch ρ) (m+1) θ u +
      (1 - inspectionProbability ρ) * experimentV v (playBranch ρ) (m+1) θ u := by
  have ht : ∀ π' : CausalPolicy Action Observation, experimentV v π' (m+1) θ u =
      π' [] (u 0).1 * responseV v θ [] (u 0).1 (u 0).2 *
        causalTraceProbFrom π' (responseV v θ) [u 0] (List.ofFn (fun i => u i.succ)) := by
    intro π'
    change causalTraceProb π' (responseV v θ) (List.ofFn u) = _
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

/-! ## Compatibility facts for the play branch -/

theorem compatibleWorld_spec (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1)) (b : Bool)
    (hex : ∃ η, Compatible n h b η) : Compatible n h b (compatibleWorld n h b) := by
  classical
  simp only [compatibleWorld, dif_pos hex]
  exact Classical.choose_spec hex

theorem monitorEquivalent_of_compatible (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    {b b' : Bool} {θ η : World} (hθ : Compatible n h b θ) (hη : Compatible n h b' η) :
    MonitorEquivalent (n+1) θ η := by
  intro k hk
  have he := (hθ.2 k hk).symm.trans (hη.2 k hk)
  by_cases hx : θ = some k <;> by_cases hy : η = some k <;> simp_all [monitorLabel]

/-- A late pulse world is compatible with every supported record's monitors. -/
theorem exists_compatible_true (π : CausalPolicy Action Observation) (θ : World) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1)) (hh : experimentV v π (n+1) θ h ≠ 0) :
    ∃ η, Compatible n h true η := by
  cases hθ : θ.isSome
  · refine ⟨some (n+1), rfl, ?_⟩
    intro k hk
    have hm := supportedV_monitor v π θ (n+1) k hk h hh
    rw [hm]
    have hn : θ = none := Option.not_isSome_iff_eq_none.mp (by simp [hθ])
    subst hn
    have hne : n + 1 ≠ k := by omega
    simp [monitorLabel, hne]
  · exact ⟨θ, hθ, fun k hk => supportedV_monitor v π θ (n+1) k hk h hh⟩

theorem MonitorEquivalent.mono {n m : ℕ} (hmn : m ≤ n) {θ η : World}
    (he : MonitorEquivalent n θ η) : MonitorEquivalent m θ η :=
  fun k hk => he k (by omega)

/-- A policy that never inspects has monitor-determined records. -/
theorem no_inspection_rowsV_eq (π : CausalPolicy Action Observation)
    (hs : inspectionProbability π = 0) (n : ℕ) {θ η : World}
    (he : MonitorEquivalent n θ η) : experimentV v π n θ = experimentV v π n η := by
  funext h
  cases n with
  | zero => simp [experimentV, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  | succ n =>
    change causalTraceProb π (responseV v θ) (List.ofFn h) =
      causalTraceProb π (responseV v η) (List.ofFn h)
    rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
    simp only [causalTraceProbFrom, responseV_root]
    by_cases hi : (h 0).1 = inspect
    · simp [hi, inspectionProbability] at hs ⊢
      rw [hs]
      simp
    · simp only [if_neg hi]
      rw [traceProbFromV_eq_of_monitors v π (n+1) he _ _ (by simp) (by simp; omega)]

/-- Uninspected source records simulate the play branch exactly from any
monitor-compatible late world. -/
theorem playBranch_replay_correct (π ρ : CausalPolicy Action Observation) (θ : World)
    (m n : ℕ) (hm : m+1 ≤ n+1) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experimentV v π (n+1) θ h ≠ 0) :
    guessedReplayV v (playBranch ρ) (m+1) n h true = experimentV v (playBranch ρ) (m+1) θ := by
  unfold guessedReplayV
  have hc := compatibleWorld_spec n h true (exists_compatible_true v π θ n h hh)
  have hθ := supportedV_compatible v π θ n h hh
  exact no_inspection_rowsV_eq v (playBranch ρ) (playBranch_root ρ) (m+1)
    ((monitorEquivalent_of_compatible n h hc hθ).mono hm)

/-! ## The chain decoder -/

/-- Fraction of inspected source records assigned to the target's inspection branch. -/
def inspectShare (s r : ℝ) : ℝ := if s = 0 then 1 else min s r / s

/-- Fraction of uninspected source records assigned to the target's inspection branch. -/
def guessShare (s r : ℝ) : ℝ := if s = 1 then 0 else (r - min s r) / (1 - s)

theorem inspectShare_mass (s r : ℝ) (hr : 0 ≤ r) : s * inspectShare s r = min s r := by
  unfold inspectShare
  split_ifs with h
  · subst h; simp [min_eq_left hr]
  · field_simp

theorem guessShare_mass (s r : ℝ) (hr : r ≤ 1) : (1 - s) * guessShare s r = r - min s r := by
  unfold guessShare
  split_ifs with h
  · subst h; simp [min_eq_right hr]
  · have : (1 - s) ≠ 0 := by intro hz; apply h; linarith
    field_simp

theorem inspectShare_bounds (s r : ℝ) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    0 ≤ inspectShare s r ∧ inspectShare s r ≤ 1 := by
  unfold inspectShare
  split_ifs with h
  · norm_num
  · have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm h)
    constructor
    · exact div_nonneg (le_min hs hr) hpos.le
    · rw [div_le_one hpos]; exact min_le_left _ _

theorem guessShare_bounds (s r : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr1 : r ≤ 1) :
    0 ≤ guessShare s r ∧ guessShare s r ≤ 1 := by
  unfold guessShare
  split_ifs with h
  · norm_num
  · have hpos : 0 < 1 - s := by
      have : s < 1 := lt_of_le_of_ne hs1 h
      linarith
    constructor
    · exact div_nonneg (by linarith [min_le_right s r]) hpos.le
    · rw [div_le_one hpos]
      by_cases hsr : s ≤ r
      · rw [min_eq_left hsr]; linarith
      · rw [min_eq_right (not_le.mp hsr).le]; linarith

def chainDecoder (α q : ℝ) (ρ : CausalPolicy Action Observation) (m n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1)) :
    CausalFiniteTrace Action Observation (m+1) → ℝ :=
  if (h 0).1 = inspect then
    fun u => α * guessedReplayV v (inspectBranch ρ) (m+1) n h (decide (2 ≤ (h 0).2.val)) u +
      (1 - α) * guessedReplayV v (playBranch ρ) (m+1) n h (decide (2 ≤ (h 0).2.val)) u
  else
    fun u => q * ((guessedReplayV v (inspectBranch ρ) (m+1) n h false u +
      guessedReplayV v (inspectBranch ρ) (m+1) n h true u) / 2) +
      (1 - q) * guessedReplayV v (playBranch ρ) (m+1) n h true u

theorem mixture_isDist {X : Type*} [Fintype X] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) :
    IsDist (fun x => a * p x + (1 - a) * q x) := by
  constructor
  · intro x
    exact add_nonneg (mul_nonneg ha0 (hp.1 x)) (mul_nonneg (by linarith) (hq.1 x))
  · rw [sum_add_distrib, ← mul_sum, ← mul_sum, hp.2, hq.2]; ring

theorem half_mixture_isDist {X : Type*} [Fintype X] (p q : X → ℝ) (hp : IsDist p)
    (hq : IsDist q) : IsDist (fun x => (p x + q x) / 2) := by
  constructor
  · intro x; exact div_nonneg (add_nonneg (hp.1 x) (hq.1 x)) (by norm_num)
  · rw [← sum_div, sum_add_distrib, hp.2, hq.2]; norm_num

theorem chainDecoder_valid (hv : v.Valid) (α q : ℝ) (hα : 0 ≤ α ∧ α ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)
    (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ) (m n : ℕ) :
    chainDecoder v α q ρ m n ∈ stochasticRules _ _ := by
  intro h _
  have hI := experimentV_valid v hv (inspectBranch ρ) (inspectBranch_valid ρ hρ) (m+1)
  have hP := experimentV_valid v hv (playBranch ρ) (playBranch_valid ρ hρ) (m+1)
  by_cases hi : (h 0).1 = inspect
  · simp only [chainDecoder, if_pos hi]
    exact mixture_isDist α hα.1 hα.2 _ _ (hI _) (hP _)
  · simp only [chainDecoder, if_neg hi]
    exact mixture_isDist q hq.1 hq.2 _ _ (half_mixture_isDist _ _ (hI _) (hI _)) (hP _)

/-- Rows of the chain decoder on supported source records. -/
theorem chainDecoder_inspected (π ρ : CausalPolicy Action Observation) (α q : ℝ) (θ : World)
    (m n : ℕ) (hm : m+1 ≤ n+1) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experimentV v π (n+1) θ h ≠ 0) (hi : (h 0).1 = inspect) :
    chainDecoder v α q ρ m n h = fun u => α * experimentV v (inspectBranch ρ) (m+1) θ u +
      (1 - α) * experimentV v (playBranch ρ) (m+1) θ u := by
  simp only [chainDecoder, if_pos hi, supportedV_inspection_bit v π θ n h hh hi,
    guessedReplayV_correct v π _ θ (m+1) n hm h hh]

theorem chainDecoder_uninspected (π ρ : CausalPolicy Action Observation) (α q : ℝ) (θ : World)
    (m n : ℕ) (hm : m+1 ≤ n+1) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experimentV v π (n+1) θ h ≠ 0) (hi : ¬ (h 0).1 = inspect) :
    chainDecoder v α q ρ m n h =
      fun u => q * ((guessedReplayV v (inspectBranch ρ) (m+1) n h false u +
        guessedReplayV v (inspectBranch ρ) (m+1) n h true u) / 2) +
        (1 - q) * experimentV v (playBranch ρ) (m+1) θ u := by
  simp only [chainDecoder, if_neg hi, playBranch_replay_correct v π ρ θ m n hm h hh]

/-- The fair guess of the inspection branch has total variation at most one half. -/
theorem guess_tv_le (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (θ : World) (m n : ℕ) (hm : m+1 ≤ n+1)
    (h : CausalFiniteTrace Action Observation (n+1)) (hh : experimentV v π (n+1) θ h ≠ 0) :
    finiteTV (fun u => (guessedReplayV v (inspectBranch ρ) (m+1) n h false u +
      guessedReplayV v (inspectBranch ρ) (m+1) n h true u) / 2)
      (experimentV v (inspectBranch ρ) (m+1) θ) ≤ 1/2 := by
  have hI := experimentV_valid v hv (inspectBranch ρ) (inspectBranch_valid ρ hρ) (m+1)
  have hc := guessedReplayV_correct v π (inspectBranch ρ) θ (m+1) n hm h hh
  cases hb : θ.isSome
  · rw [hb] at hc; rw [hc]
    exact half_mixture_tv _ _ (hI θ) (hI _)
  · rw [hb] at hc; rw [hc]
    have he : (fun u => (guessedReplayV v (inspectBranch ρ) (m+1) n h false u +
        experimentV v (inspectBranch ρ) (m+1) θ u) / 2) =
        (fun u => (experimentV v (inspectBranch ρ) (m+1) θ u +
          guessedReplayV v (inspectBranch ρ) (m+1) n h false u) / 2) := by
      funext u; ring
    rw [he]
    exact half_mixture_tv _ _ (hI θ) (hI _)

/-- Error of the chain decoder in every world. -/
theorem chainDecoder_error_le (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m+1 ≤ n+1) (θ : World) :
    decodeErr (experimentV v π (n+1)) (experimentV v ρ (m+1))
      (chainDecoder v (inspectShare (inspectionProbability π) (inspectionProbability ρ))
        (guessShare (inspectionProbability π) (inspectionProbability ρ)) ρ m n) θ ≤
      (inspectionProbability ρ - min (inspectionProbability π) (inspectionProbability ρ)) / 2 := by
  have hs1 : inspectionProbability π ≤ 1 := inspectionProbability_le_one π hπ
  have hs0 : 0 ≤ inspectionProbability π := inspectionProbability_nonneg π hπ
  have hr1 : inspectionProbability ρ ≤ 1 := inspectionProbability_le_one ρ hρ
  have hr0 : 0 ≤ inspectionProbability ρ := inspectionProbability_nonneg ρ hρ
  have hsα := inspectShare_mass (inspectionProbability π) (inspectionProbability ρ) hr0
  have hsq := guessShare_mass (inspectionProbability π) (inspectionProbability ρ) hr1
  have hq0 := (guessShare_bounds (inspectionProbability π) (inspectionProbability ρ) hs0 hs1 hr1).1
  set s := inspectionProbability π with hs_def
  set r := inspectionProbability ρ with hr_def
  set α := inspectShare s r with hα_def
  set q := guessShare s r with hq_def
  set E := experimentV v π (n+1) with hE_def
  set FI := experimentV v (inspectBranch ρ) (m+1) with hFI_def
  set FP := experimentV v (playBranch ρ) (m+1) with hFP_def
  set G := chainDecoder v α q ρ m n with hG_def
  set M : CausalFiniteTrace Action Observation (n+1) →
      CausalFiniteTrace Action Observation (m+1) → ℝ :=
    fun h u => (guessedReplayV v (inspectBranch ρ) (m+1) n h false u +
      guessedReplayV v (inspectBranch ρ) (m+1) n h true u) / 2 with hM_def
  have hEv := experimentV_valid v hv π hπ (n+1)
  -- the decision law, split by the source root action
  have hlaw : ∀ u, finiteDecisionLaw E G θ u =
      s * (α * FI θ u + (1 - α) * FP θ u) +
      (∑ h, if (h 0).1 = inspect then 0 else E θ h * (q * M h u + (1 - q) * FP θ u)) := by
    intro u
    unfold finiteDecisionLaw
    have hsplit : ∀ h, E θ h * G h u =
        (if (h 0).1 = inspect then E θ h else 0) * (α * FI θ u + (1 - α) * FP θ u) +
        (if (h 0).1 = inspect then 0 else E θ h * (q * M h u + (1 - q) * FP θ u)) := by
      intro h
      by_cases hh : E θ h = 0
      · simp [hh]
      · by_cases hi : (h 0).1 = inspect
        · simp only [if_pos hi, add_zero]
          rw [show G h = fun u => α * FI θ u + (1 - α) * FP θ u from
            chainDecoder_inspected v π ρ α q θ m n hm h hh hi]
        · simp only [if_neg hi, zero_mul, zero_add]
          rw [show G h = fun u => q * M h u + (1 - q) * FP θ u from
            chainDecoder_uninspected v π ρ α q θ m n hm h hh hi]
    simp_rw [hsplit]
    rw [sum_add_distrib, ← sum_mul, rootInspectionV_mass v hv π hπ θ n]
  have hmass : (∑ h, if (h 0).1 = inspect then 0 else E θ h) = 1 - s := by
    have h1 := (hEv θ).2
    have h2 := rootInspectionV_mass v hv π hπ θ n
    have h3 : ∀ h : CausalFiniteTrace Action Observation (n+1),
        (if (h 0).1 = inspect then 0 else E θ h) =
          E θ h - (if (h 0).1 = inspect then E θ h else 0) := by
      intro h; split_ifs <;> ring
    simp_rw [h3]
    rw [sum_sub_distrib, h1, h2]
  -- the difference to the target law
  have hdiff : ∀ u, finiteDecisionLaw E G θ u - experimentV v ρ (m+1) θ u =
      q * ∑ h, (if (h 0).1 = inspect then 0 else E θ h * (M h u - FI θ u)) := by
    intro u
    rw [hlaw, experimentV_branch_mixture v ρ hρ m θ u]
    have hr : (∑ h, if (h 0).1 = inspect then 0 else E θ h * (q * M h u + (1 - q) * FP θ u)) =
        q * (∑ h, if (h 0).1 = inspect then 0 else E θ h * M h u) +
          ((1 - q) * FP θ u) * (1 - s) := by
      have e : ∀ h : CausalFiniteTrace Action Observation (n+1),
          (if (h 0).1 = inspect then 0 else E θ h * (q * M h u + (1 - q) * FP θ u)) =
          q * (if (h 0).1 = inspect then 0 else E θ h * M h u) +
          ((1 - q) * FP θ u) * (if (h 0).1 = inspect then 0 else E θ h) := by
        intro h; split_ifs <;> ring
      simp_rw [e]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hmass]
    have hl : (∑ h, if (h 0).1 = inspect then 0 else E θ h * (M h u - FI θ u)) =
        (∑ h, if (h 0).1 = inspect then 0 else E θ h * M h u) - FI θ u * (1 - s) := by
      have e : ∀ h : CausalFiniteTrace Action Observation (n+1),
          (if (h 0).1 = inspect then 0 else E θ h * (M h u - FI θ u)) =
          (if (h 0).1 = inspect then 0 else E θ h * M h u) -
          FI θ u * (if (h 0).1 = inspect then 0 else E θ h) := by
        intro h; split_ifs <;> ring
      simp_rw [e]
      rw [sum_sub_distrib, ← mul_sum, hmass]
    rw [hr, hl]
    linear_combination (FI θ u - FP θ u) * hsα + (FI θ u - FP θ u) * hsq
  -- bound the total variation
  rw [decodeErr_eq_finiteTV]
  unfold finiteTV
  simp_rw [hdiff]
  calc
    (1/2 : ℝ) * ∑ u, |q * ∑ h, (if (h 0).1 = inspect then 0 else E θ h * (M h u - FI θ u))|
        ≤ (1/2 : ℝ) * ∑ u, ∑ h, (if (h 0).1 = inspect then 0 else
            q * E θ h * |M h u - FI θ u|) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply sum_le_sum; intro u _
          rw [abs_mul, abs_of_nonneg hq0]
          calc q * |∑ h, (if (h 0).1 = inspect then 0 else E θ h * (M h u - FI θ u))|
              ≤ q * ∑ h, |if (h 0).1 = inspect then 0 else E θ h * (M h u - FI θ u)| :=
                mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hq0
            _ = ∑ h, (if (h 0).1 = inspect then 0 else q * E θ h * |M h u - FI θ u|) := by
                rw [mul_sum]; apply sum_congr rfl; intro h _
                split_ifs
                · simp
                · rw [abs_mul, abs_of_nonneg ((hEv θ).1 h)]; ring
    _ = ∑ h, (if (h 0).1 = inspect then 0 else q * E θ h * finiteTV (M h) (FI θ)) := by
          rw [sum_comm, mul_sum]
          apply sum_congr rfl; intro h _
          split_ifs
          · simp
          · simp only [finiteTV, mul_sum]
            apply sum_congr rfl; intro u _; ring
    _ ≤ ∑ h, (if (h 0).1 = inspect then 0 else q * E θ h * (1/2)) := by
          apply sum_le_sum; intro h _
          split_ifs
          · exact le_rfl
          · by_cases hh : E θ h = 0
            · simp [hh]
            · exact mul_le_mul_of_nonneg_left (guess_tv_le v hv π ρ hρ θ m n hm h hh)
                (mul_nonneg hq0 ((hEv θ).1 h))
    _ = q * (1 - s) / 2 := by
          rw [← hmass, mul_sum, sum_div]
          apply sum_congr rfl; intro h _
          split_ifs <;> ring
    _ = _ := by rw [mul_comm, hsq]

/-! ## The chain -/

theorem chain_le (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m+1 ≤ n+1) :
    finiteDeficiency (experimentV v π (n+1)) (experimentV v ρ (m+1)) ≤
      max (inspectionProbability ρ - inspectionProbability π) 0 / 2 := by
  have hb := chainDecoder_error_le v hv π ρ hπ hρ m n hm
  have hle := finiteDeficiency_le_of_decoder _ _ _
    (chainDecoder_valid v hv _ _ (inspectShare_bounds _ _ (inspectionProbability_nonneg π hπ)
      (inspectionProbability_nonneg ρ hρ)) (guessShare_bounds _ _
      (inspectionProbability_nonneg π hπ) (inspectionProbability_le_one π hπ)
      (inspectionProbability_le_one ρ hρ)) ρ hρ m n) _ hb
  refine hle.trans (le_of_eq ?_)
  by_cases hsr : inspectionProbability π ≤ inspectionProbability ρ
  · rw [min_eq_left hsr, max_eq_left (by linarith)]
  · rw [min_eq_right (not_le.mp hsr).le, max_eq_right (by linarith)]; ring

/-- The never world and a pulse world beyond both horizons agree off inspection. -/
theorem late_row_eq_uninspected (π : CausalPolicy Action Observation) (m n : ℕ)
    (hm : m+1 ≤ n+1) (h : CausalFiniteTrace Action Observation (m+1)) (hi : (h 0).1 ≠ inspect) :
    experimentV v π (m+1) (some (n+1)) h = experimentV v π (m+1) none h := by
  change causalTraceProb π (responseV v (some (n+1))) (List.ofFn h) =
    causalTraceProb π (responseV v none) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, responseV_root, if_neg hi]
  rw [traceProbFromV_late_eq v π (n+1) _ _ (by simp) (by simp; omega)]

theorem rowV_none_zero_if_inspected (π : CausalPolicy Action Observation) (k n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experimentV v π (n+1) (some k) h ≠ 0) (hi : (h 0).1 = inspect) :
    experimentV v π (n+1) none h = 0 := by
  by_contra hn
  have hkbit := supportedV_inspection_bit v π (some k) n h hh hi
  have hnbit := supportedV_inspection_bit v π none n h hn hi
  simp only [Option.isSome_none, Option.isSome_some] at hkbit hnbit
  rw [hnbit] at hkbit
  contradiction

/-- Total variation between the never row and a late row is the inspection probability. -/
theorem late_rows_tv (hv : v.Valid) (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (m n : ℕ) (hm : m+1 ≤ n+1) :
    finiteTV (experimentV v π (m+1) none) (experimentV v π (m+1) (some (n+1))) =
      inspectionProbability π := by
  unfold finiteTV
  have hrow : ∀ h : CausalFiniteTrace Action Observation (m+1),
      |experimentV v π (m+1) none h - experimentV v π (m+1) (some (n+1)) h| =
        (if (h 0).1 = inspect then experimentV v π (m+1) none h else 0) +
        (if (h 0).1 = inspect then experimentV v π (m+1) (some (n+1)) h else 0) := by
    intro h
    by_cases hi : (h 0).1 = inspect
    · simp only [if_pos hi]
      have h0 := (experimentV_valid v hv π hπ (m+1) none).1 h
      have h1 := (experimentV_valid v hv π hπ (m+1) (some (n+1))).1 h
      by_cases hz : experimentV v π (m+1) (some (n+1)) h = 0
      · rw [hz]; simp [abs_of_nonneg h0]
      · rw [rowV_none_zero_if_inspected v π (n+1) m h hz hi]
        simp [abs_of_nonneg h1]
    · simp only [if_neg hi, late_row_eq_uninspected v π m n hm h hi]; simp
  simp_rw [hrow]
  rw [sum_add_distrib, rootInspectionV_mass v hv π hπ none m,
    rootInspectionV_mass v hv π hπ (some (n+1)) m]
  ring

theorem chain_ge (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m+1 ≤ n+1) :
    (inspectionProbability ρ - inspectionProbability π) / 2 ≤
      finiteDeficiency (experimentV v π (n+1)) (experimentV v ρ (m+1)) := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
    (experimentV_valid v hv π hπ _) (experimentV_valid v hv ρ hρ _))
  rintro c ⟨G, hG, herr⟩
  have hn := herr none
  have hk := herr (some (n+1))
  rw [decodeErr_eq_finiteTV] at hn hk
  have hsrc := late_rows_tv v hv π hπ n n le_rfl
  have htgt := late_rows_tv v hv ρ hρ m n hm
  have hcon := finiteTV_decision_le (experimentV v π (n+1) none)
    (experimentV v π (n+1) (some (n+1))) G hG
  change finiteTV (finiteDecisionLaw (experimentV v π (n+1)) G none)
    (finiteDecisionLaw (experimentV v π (n+1)) G (some (n+1))) ≤ _ at hcon
  have htri := finiteTV_triangle (experimentV v ρ (m+1) none)
    (finiteDecisionLaw (experimentV v π (n+1)) G none) (experimentV v ρ (m+1) (some (n+1)))
  have htri2 := finiteTV_triangle (finiteDecisionLaw (experimentV v π (n+1)) G none)
    (finiteDecisionLaw (experimentV v π (n+1)) G (some (n+1)))
    (experimentV v ρ (m+1) (some (n+1)))
  rw [finiteTV_symm] at hn
  linarith

/-- **Exact all-policy chain.** For source horizon `t ≥ n ≥ 1`, the deficiency of
the source record to the target record is `max (r - s) 0 / 2`. -/
theorem chain_exact (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m+1 ≤ n+1) :
    finiteDeficiency (experimentV v π (n+1)) (experimentV v ρ (m+1)) =
      max (inspectionProbability ρ - inspectionProbability π) 0 / 2 := by
  apply le_antisymm (chain_le v hv π ρ hπ hρ m n hm)
  rcases le_or_gt (inspectionProbability ρ) (inspectionProbability π) with hle | hlt
  · rw [max_eq_right (by linarith)]
    simp only [zero_div]
    exact finiteDeficiency_nonneg_of_valid _ _ (experimentV_valid v hv π hπ _)
      (experimentV_valid v hv ρ hρ _)
  · rw [max_eq_left (by linarith)]
    exact chain_ge v hv π ρ hπ hρ m n hm

/-- The original interface. -/
theorem chain_exact_original (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m+1 ≤ n+1) :
    finiteDeficiency (experiment π (n+1)) (experiment ρ (m+1)) =
      max (inspectionProbability ρ - inspectionProbability π) 0 / 2 := by
  have h := chain_exact Variant.original Variant.original_valid π ρ hπ hρ m n hm
  rwa [experimentV_original, experimentV_original] at h

/-- Deficiency to the depth-zero record is zero. -/
theorem deficiency_to_trivial (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (t : ℕ) :
    finiteDeficiency (experimentV v π t) (experimentV v ρ 0) = 0 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (fun _ _ => 1)
    · intro h _
      constructor
      · intro u; norm_num
      · simp
    · intro θ
      apply le_of_eq
      rw [decodeErr_eq_finiteTV]
      have he : finiteDecisionLaw (experimentV v π t) (fun _ _ => (1:ℝ)) θ =
          experimentV v ρ 0 θ := by
        funext u
        unfold finiteDecisionLaw
        simp only [mul_one, (experimentV_valid v hv π hπ t θ).2]
        simp [experimentV, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
      rw [he]
      simp [finiteTV]
  · exact finiteDeficiency_nonneg_of_valid _ _ (experimentV_valid v hv π hπ _)
      (experimentV_valid v hv ρ hρ _)

/-- Finitary domination on this interface is exactly the order of inspection probabilities. -/
theorem finitaryDominates_iff (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) :
    CausalFinitaryDominates (responseV v) ⟨π,hπ⟩ ⟨ρ,hρ⟩ ↔
      inspectionProbability ρ ≤ inspectionProbability π := by
  constructor
  · intro hd
    by_contra hnle
    have hlt : inspectionProbability π < inspectionProbability ρ := not_le.mp hnle
    obtain ⟨T, hT⟩ := hd 1 ((inspectionProbability ρ - inspectionProbability π)/4) (by linarith)
    have hbad := hT (T+1) (by omega)
    change finiteDeficiency (experimentV v π (T+1)) (experimentV v ρ 1) < _ at hbad
    rw [chain_exact v hv π ρ hπ hρ 0 T (by omega), max_eq_left (by linarith)] at hbad
    linarith
  · intro hle m ε hε
    refine ⟨m, ?_⟩
    intro t ht
    cases m with
    | zero =>
      change finiteDeficiency (experimentV v π t) (experimentV v ρ 0) < ε
      rw [deficiency_to_trivial v hv π ρ hπ hρ t]; exact hε
    | succ m =>
      cases t with
      | zero => omega
      | succ n =>
        change finiteDeficiency (experimentV v π (n+1)) (experimentV v ρ (m+1)) < ε
        rw [chain_exact v hv π ρ hπ hρ m n (by omega), max_eq_right (by linarith)]
        simpa using hε

end IdExp.AlarmPanel
