import Formal.AlarmPanelControl

/-!
# Multi-step physical sensor channels on the alarm/panel interface

The channel input is an open-loop action sequence of length `n`; its output is
only the last raw sensor reading. The recursive definition executes the literal
response and marginalizes every intermediate sensor. Horizon zero uses an
arbitrary constant sentinel; all empowerment extension claims have `n ≥ 1`.
-/
namespace IdExp.AlarmPanel.Control
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Execute an imposed action sequence, retaining only the terminal sensor. -/
def terminalChannel (θ : World) (h : History) :
    (n : ℕ) → FiniteExperiment (Fin n → Action) Observation
  | 0 => fun _ => pointDist 0
  | 1 => fun a => response θ h (a 0)
  | n + 2 => fun a o => ∑ x : Observation,
      response θ h (a 0) x * terminalChannel θ (h ++ [(a 0, x)]) (n + 1) (Fin.tail a) o

theorem terminalChannel_valid (θ : World) (h : History) (n : ℕ) :
    IsFiniteExperiment (terminalChannel θ h n) := by
  induction n using Nat.twoStepInduction generalizing h with
  | zero => intro a; exact pointDist_valid 0
  | one => intro a; exact response_valid θ h (a 0)
  | more n ih0 ih1 =>
    intro a
    constructor
    · intro o
      exact sum_nonneg fun x _ => mul_nonneg ((response_valid θ h (a 0)).1 x)
        ((ih1 (h ++ [(a 0, x)]) (Fin.tail a)).1 o)
    · change (∑ o : Observation, ∑ x : Observation,
        response θ h (a 0) x * terminalChannel θ (h ++ [(a 0, x)]) (n + 1) (Fin.tail a) o) = 1
      rw [sum_comm]
      simp only [← mul_sum, (ih1 _ _).2, mul_one, (response_valid θ h (a 0)).2]

theorem inspected_append_nonempty (h : History) (hh : h ≠ []) (r : History) :
    inspected (h ++ r) ↔ inspected h := by
  cases h with
  | nil => contradiction
  | cons ao hs => simp [inspected]

/-- At positive starting time, only the mode, clock, and final action remain. -/
theorem terminalChannel_tail (θ : World) (h : History) (hh : h ≠ []) (n : ℕ)
    (a : Fin (n + 1) → Action) (o : Observation) :
    terminalChannel θ h (n + 1) a o =
      if (h.length + n) % 2 = 1 then
        (if inspected h then pointDist 0 o else pairDist (a (Fin.last n) == play1) o)
      else pointDist (monitorLabel θ ((h.length + n - 2) / 2)) o := by
  induction n generalizing h with
  | zero => simp [terminalChannel, response, hh]
  | succ n ih =>
    rw [terminalChannel]
    have he (x : Observation) :
        terminalChannel θ (h ++ [(a 0, x)]) (n + 1) (Fin.tail a) o =
          if (h.length + (n + 1)) % 2 = 1 then
            (if inspected h then pointDist 0 o else pairDist (a (Fin.last (n + 1)) == play1) o)
          else pointDist (monitorLabel θ ((h.length + (n + 1) - 2) / 2)) o := by
      rw [ih _ (by simp)]
      simp only [List.length_append, List.length_singleton,
        inspected_append_nonempty h hh, Fin.tail, Fin.succ_last]
      congr 3 <;> omega
    simp_rw [he]
    rw [← sum_mul, (response_valid θ h (a 0)).2, one_mul]

/-- Constant channels have zero capacity for arbitrary finite probe alphabets. -/
theorem probe_point_capacity {I : Type*} [Fintype I] [Nonempty I] (o : Observation) :
    capacity (fun _ : I => pointDist o) = 0 := by
  have he : (fun _ : I => pointDist o) = diracExp (fun _ : I => o) := by
    funext a x
    simp [pointDist, diracExp, eq_comm]
  rw [he, capacity_dirac_const]

/-- The two constant PLAY sequences provide a capacity-achieving probe. -/
def probeInput (n : ℕ) (a : Fin (n + 1) → Action) : ℝ :=
  (if a = (fun _ => play0) then 1 / 2 else 0) +
  (if a = (fun _ => play1) then 1 / 2 else 0)

theorem probeInput_valid (n : ℕ) : IsDist (probeInput n) := by
  constructor
  · intro a
    exact add_nonneg (by split <;> norm_num) (by split <;> norm_num)
  · norm_num [probeInput, sum_add_distrib]

def terminalPanel (n : ℕ) : FiniteExperiment (Fin (n + 1) → Action) Observation :=
  fun a => pairDist (a (Fin.last n) == play1)

theorem terminalPanel_valid (n : ℕ) : IsFiniteExperiment (terminalPanel n) :=
  fun a => pairDist_valid _

theorem terminalPanel_information (n : ℕ) (ν : (Fin (n + 1) → Action) → ℝ)
    (hν : IsDist ν) :
    finiteBayesInformation ν (terminalPanel n) =
      ent (finiteBayesMass ν (terminalPanel n)) - Real.log 2 := by
  rw [finiteBayesInformation_eq_ent_mass_sub ν hν _ (terminalPanel_valid n)]
  simp only [terminalPanel, pairDist_entropy, ← sum_mul, hν.2, one_mul]

theorem probeInput_mass (n : ℕ) :
    finiteBayesMass (probeInput n) (terminalPanel n) = uniformDist := by
  funext o
  simp only [finiteBayesMass, probeInput, add_mul, sum_add_distrib, ite_mul, zero_mul]
  simp only [sum_ite_eq', mem_univ, if_true, terminalPanel]
  fin_cases o <;> norm_num [pairDist, play0, play1, uniformDist, Fin.ext_iff]

theorem terminalPanel_capacity (n : ℕ) : capacity (terminalPanel n) = Real.log 2 := by
  have hv : finiteBayesInformation (probeInput n) (terminalPanel n) = Real.log 2 := by
    rw [terminalPanel_information n _ (probeInput_valid n), probeInput_mass, uniformDist_entropy]
    ring
  have hb (ν : (Fin (n + 1) → Action) → ℝ) (hν : IsDist ν) :
      finiteBayesInformation ν (terminalPanel n) ≤ Real.log 2 := by
    have hm : IsDist (finiteBayesMass ν (terminalPanel n)) := by
      constructor
      · exact finiteBayesMass_nonneg _ _ hν.1 (fun a o => (terminalPanel_valid n a).1 o)
      · unfold finiteBayesMass
        rw [sum_comm]
        simp only [← mul_sum, (terminalPanel_valid n _).2, mul_one, hν.2]
    have hh := ent_le_log_card _ hm
    norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hh
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h4] at hh
    rw [terminalPanel_information n ν hν]
    linarith
  have hmax : IsMaxOn (fun ν => finiteBayesInformation ν (terminalPanel n))
      (stdSimplex ℝ (Fin (n + 1) → Action)) (probeInput n) := by
    apply isMaxOn_iff.2
    intro ν hν
    rw [hv]
    exact hb ν hν
  rw [capacity_eq_of_isMaxOn _ (probeInput_valid n) hmax, hv]

/-- Multi-step empowerment, measured in nats, for the actual terminal channel. -/
def multiStepCapacity (θ : World) (h : History) (n : ℕ) : ℝ :=
  capacity (terminalChannel θ h n)

theorem multiStepCapacity_tail (θ : World) (h : History) (hh : h ≠ []) (n : ℕ) :
    multiStepCapacity θ h (n + 1) =
      if (h.length + n) % 2 = 1 ∧ ¬ inspected h then Real.log 2 else 0 := by
  by_cases hp : (h.length + n) % 2 = 1
  · by_cases hi : inspected h
    · have he : terminalChannel θ h (n + 1) = fun _ => pointDist 0 := by
        funext a o; simp [terminalChannel_tail θ h hh, hp, hi]
      simp [multiStepCapacity, he, probe_point_capacity, hp, hi]
    · have he : terminalChannel θ h (n + 1) = terminalPanel n := by
        funext a o; simp [terminalChannel_tail θ h hh, hp, hi, terminalPanel]
      simp [multiStepCapacity, he, terminalPanel_capacity, hp, hi]
  · have he : terminalChannel θ h (n + 1) =
        fun _ => pointDist (monitorLabel θ ((h.length + n - 2) / 2)) := by
      funext a o; simp [terminalChannel_tail θ h hh, hp]
    simp [multiStepCapacity, he, probe_point_capacity, hp]

/-- The startup channel at horizon at least two, before taking its capacity. -/
theorem terminalChannel_root (θ : World) (n : ℕ) (a : Fin (n + 2) → Action)
    (o : Observation) :
    terminalChannel θ [] (n + 2) a o =
      if (n + 1) % 2 = 1 then
        (if a 0 = inspect then pointDist 0 o else pairDist (a (Fin.last (n + 1)) == play1) o)
      else pointDist (monitorLabel θ ((n + 1 - 2) / 2)) o := by
  rw [terminalChannel]
  have he (x : Observation) :
      terminalChannel θ ([] ++ [(a 0, x)]) (n + 1) (Fin.tail a) o =
        if (n + 1) % 2 = 1 then
          (if a 0 = inspect then pointDist 0 o else pairDist (a (Fin.last (n + 1)) == play1) o)
        else pointDist (monitorLabel θ ((n + 1 - 2) / 2)) o := by
    rw [terminalChannel_tail θ _ (by simp)]
    simp [inspected, Fin.tail, Nat.add_comm]
  simp_rw [he]
  rw [← sum_mul, (response_valid θ [] (a 0)).2, one_mul]

/-- Startup capacity is constant over finite alarm delays; this supplies the
actual prior integral without an unproved integrability assumption. -/
theorem multiStepCapacity_root_some (n k : ℕ) :
    multiStepCapacity (some k) [] (n + 1) = multiStepCapacity (some 0) [] (n + 1) := by
  cases n with
  | zero =>
    have he : terminalChannel (some k) [] 1 = terminalChannel (some 0) [] 1 := by
      funext a o
      simp [terminalChannel, response]
    exact congrArg capacity he
  | succ n =>
    by_cases hp : (n + 1) % 2 = 1
    · have he : terminalChannel (some k) [] (n + 2) = terminalChannel (some 0) [] (n + 2) := by
        funext a o
        simp [terminalChannel_root, hp]
      exact congrArg capacity he
    · have he (θ : World) : terminalChannel θ [] (n + 2) =
          fun _ => pointDist (monitorLabel θ ((n + 1 - 2) / 2)) := by
        funext a o; simp [terminalChannel_root, hp]
      simp [multiStepCapacity, he, probe_point_capacity]

end
end IdExp.AlarmPanel.Control
