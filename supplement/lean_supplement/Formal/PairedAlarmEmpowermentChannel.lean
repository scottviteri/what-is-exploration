import Formal.PairedAlarm
import Formal.ControlChannelCapacity

/-!
# Terminal-channel components for actual-world paired-alarm block empowerment

The selected objective is in `PairedAlarmBlockChannel`: full observation blocks
and undiscounted cumulative return. This file supplies terminal-channel lemmas
used in its component sum. Its one-bit terminal capacity is not the n-bit block
capacity, and this file defines no average or discounted policy objective.

Fix a world `θ`, a visited history `h`, and a probe length `n`. A hypothetical
probe chooses an open-loop action sequence `U ∈ A^n` from a distribution `ν` on
`Fin n → Action`, executes it through the literal response law `response θ`,
and keeps only the final raw observation `Y_n`, now a (display, monitor) pair.
The intermediate observations are marginalized; the output contains no copy of
the actions. The terminal-sensor capacity is `max_ν I_ν(U; Y_n)`,
measured in bits: the natural-log capacity `capacity` divided by `log 2`.

After startup the monitor coordinate is fixed by the world and the clock, so it
is a constant output coordinate of the fixed-world channel. The display
coordinate depends only on the startup mode and the final probe action. Hence,
for every `n ≥ 1`, every world, and every nonempty history, this terminal capacity is
one bit outside inspection mode and zero inside it; the probe length introduces
no parity. At the empty history the capacity depends on the world only through
the startup display law, so it is constant over the finite alarm times.

Horizon zero uses an arbitrary constant sentinel; every claim has `n ≥ 1`.
-/

noncomputable section

namespace IdExp.PairedAlarm.Empowerment

open Finset

/-! ## Generic finite-channel facts -/

section Generic

variable {I X : Type*} [Fintype I] [Nonempty I] [Fintype X]

/-- A constant channel carries no information about its input, whatever the
constant output law. -/
theorem capacity_constChannel (p : X → ℝ) (hp : IsDist p) :
    capacity (fun _ : I => p) = 0 := by
  classical
  have hval (ν : I → ℝ) (hν : IsDist ν) :
      finiteBayesInformation ν (fun _ : I => p) = 0 := by
    rw [finiteBayesInformation_eq_ent_mass_sub ν hν _ (fun _ => hp)]
    have hm : finiteBayesMass ν (fun _ : I => p) = p := by
      funext x
      simp only [finiteBayesMass, ← sum_mul, hν.2, one_mul]
    rw [hm, ← sum_mul, hν.2, one_mul, sub_self]
  have hmax : IsMaxOn (fun ν => finiteBayesInformation ν (fun _ : I => p))
      (stdSimplex ℝ I) (uniformPrior I) := by
    apply isMaxOn_iff.2
    intro ν hν
    rw [hval ν hν, hval _ isDist_uniformPrior]
  rw [capacity_eq_of_isMaxOn _ isDist_uniformPrior hmax, hval _ isDist_uniformPrior]

/-- Capacity of a valid finite channel is nonnegative. -/
theorem capacity_nonneg_of_valid (E : FiniteExperiment I X) (hE : IsFiniteExperiment E) :
    0 ≤ capacity E := by
  classical
  exact (finiteBayesInformation_nonneg _ isDist_uniformPrior E hE).trans
    (information_le_capacity E hE isDist_uniformPrior)

/-- Capacity is at most the logarithm of the output alphabet size. -/
theorem capacity_le_log_card_output [Nonempty X] (E : FiniteExperiment I X)
    (hE : IsFiniteExperiment E) : capacity E ≤ Real.log (Fintype.card X) := by
  classical
  obtain ⟨ν, hν, hmax⟩ := exists_capacity_achieving E hE
  rw [capacity_eq_of_isMaxOn E hν hmax, finiteBayesInformation_eq_ent_mass_sub ν hν E hE]
  have hm : IsDist (finiteBayesMass ν E) := by
    constructor
    · exact finiteBayesMass_nonneg _ _ hν.1 (fun a x => (hE a).1 x)
    · unfold finiteBayesMass
      rw [sum_comm]
      simp only [← mul_sum, (hE _).2, mul_one, hν.2]
  have h1 := ent_le_log_card _ hm
  have h2 : 0 ≤ ∑ a, ν a * ent (E a) :=
    sum_nonneg fun a _ => mul_nonneg (hν.1 a) (ent_nonneg_of_isDist _ (hE a))
  linarith

end Generic

/-! ## A constant monitor coordinate does not change capacity -/

/-- Appending a constant monitor bit to a display channel is an invertible
deterministic relabeling of its output, so capacity is unchanged. -/
theorem capacity_prodLaw_pointMonitor {I : Type*} [Fintype I] [Nonempty I]
    (D : FiniteExperiment I Display) (hD : IsFiniteExperiment D) (m : Monitor) :
    capacity (fun a => prodLaw (D a) (pointMonitor m)) = capacity D := by
  classical
  have hE : IsFiniteExperiment (fun a => prodLaw (D a) (pointMonitor m)) :=
    fun a => prodLaw_valid (hD a) (pointMonitor_valid m)
  -- Forget the monitor coordinate.
  let G : Observation → Display → ℝ := fun o d => if d = o.1 then 1 else 0
  have hG : G ∈ stochasticRules Observation Display := by
    intro o _
    constructor
    · intro d; dsimp only [G]; split <;> norm_num
    · simp [G]
  have hGE : finiteDecisionLaw (fun a => prodLaw (D a) (pointMonitor m)) G = D := by
    funext a d
    simp only [finiteDecisionLaw, G, prodLaw, Fintype.sum_prod_type, pointMonitor]
    simp
  -- Reinsert the constant monitor coordinate.
  let G' : Display → Observation → ℝ := fun d o => if o = (d, m) then 1 else 0
  have hG' : G' ∈ stochasticRules Display Observation := by
    intro d _
    constructor
    · intro o; dsimp only [G']; split <;> norm_num
    · simp [G']
  have hG'D : finiteDecisionLaw D G' = fun a => prodLaw (D a) (pointMonitor m) := by
    funext a o
    obtain ⟨d, m'⟩ := o
    simp only [finiteDecisionLaw, G', prodLaw, pointMonitor, Prod.mk.injEq]
    by_cases hm : m' = m <;> simp [hm]
  apply le_antisymm
  · calc capacity (fun a => prodLaw (D a) (pointMonitor m))
        = capacity (finiteDecisionLaw D G') := by rw [hG'D]
      _ ≤ capacity D := capacity_garble_le D hD G' hG'
  · calc capacity D
        = capacity (finiteDecisionLaw (fun a => prodLaw (D a) (pointMonitor m)) G) := by
          rw [hGE]
      _ ≤ _ := capacity_garble_le _ hE G hG

/-! ## The terminal display channel in play mode -/

theorem pairDist_entropy (b : Bool) : ent (pairDist b) = Real.log 2 := by
  cases b <;> norm_num [ent, pairDist, Fin.sum_univ_succ, Real.negMulLog, Real.log_div] <;> ring

theorem uniformDist_entropy : ent uniformDist = 2 * Real.log 2 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  norm_num [ent, uniformDist, Fin.sum_univ_succ, Real.negMulLog, Real.log_div, h4]
  ring

/-- In play mode the terminal display is `2B + C`, with `B` the group of the
final probe action and `C` a fresh fair color. -/
def terminalPanel (n : ℕ) : FiniteExperiment (Fin (n + 1) → Action) Display :=
  fun a => pairDist (a (Fin.last n) == play1)

theorem terminalPanel_valid (n : ℕ) : IsFiniteExperiment (terminalPanel n) :=
  fun _ => pairDist_valid _

/-- The fair choice between the two constant PLAY sequences. -/
def probeInput (n : ℕ) (a : Fin (n + 1) → Action) : ℝ :=
  (if a = (fun _ => play0) then 1 / 2 else 0) +
  (if a = (fun _ => play1) then 1 / 2 else 0)

theorem probeInput_valid (n : ℕ) : IsDist (probeInput n) := by
  constructor
  · intro a
    exact add_nonneg (by split <;> norm_num) (by split <;> norm_num)
  · norm_num [probeInput, sum_add_distrib]

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

/-- One bit (in nats, `log 2`) of terminal display capacity in play mode. -/
theorem terminalPanel_capacity (n : ℕ) : capacity (terminalPanel n) = Real.log 2 := by
  have hv : finiteBayesInformation (probeInput n) (terminalPanel n) = Real.log 2 := by
    rw [terminalPanel_information n _ (probeInput_valid n), probeInput_mass,
      uniformDist_entropy]
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

/-! ## The literal open-loop terminal channel -/

/-- A point mass on one raw observation; used only as the horizon-zero sentinel. -/
def pointObs (x o : Observation) : ℝ := if o = x then 1 else 0

theorem pointObs_valid (x : Observation) : IsDist (pointObs x) := by
  constructor
  · intro o; unfold pointObs; split <;> norm_num
  · simp [pointObs]

/-- Execute an imposed open-loop action sequence through the literal response
law from history `h`, marginalizing every intermediate observation and retaining
only the terminal raw observation (display, monitor). -/
def terminalChannel (θ : World) (h : History) :
    (n : ℕ) → FiniteExperiment (Fin n → Action) Observation
  | 0 => fun _ => pointObs (0, 0)
  | 1 => fun a => response θ h (a 0)
  | n + 2 => fun a o => ∑ x : Observation,
      response θ h (a 0) x * terminalChannel θ (h ++ [(a 0, x)]) (n + 1) (Fin.tail a) o

theorem terminalChannel_valid (θ : World) (h : History) (n : ℕ) :
    IsFiniteExperiment (terminalChannel θ h n) := by
  induction n using Nat.twoStepInduction generalizing h with
  | zero => intro a; exact pointObs_valid (0, 0)
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

theorem inspected_append_of_ne_nil (h : History) (hh : h ≠ []) (r : History) :
    inspected (h ++ r) ↔ inspected h := by
  cases h with
  | nil => contradiction
  | cons ao hs =>
    obtain ⟨a, o⟩ := ao
    simp only [List.cons_append, inspected_cons]

/-- After startup the display law depends only on the startup mode. -/
theorem panelDisplay_append (h : History) (hh : h ≠ []) (r : History) (a : Action) :
    panelDisplay (h ++ r) a = panelDisplay h a := by
  by_cases hi : inspected h
  · have hi' : inspected (h ++ r) := (inspected_append_of_ne_nil h hh r).2 hi
    simp only [panelDisplay, if_pos hi, if_pos hi']
  · have hi' : ¬ inspected (h ++ r) := fun hr => hi ((inspected_append_of_ne_nil h hh r).1 hr)
    simp only [panelDisplay, if_neg hi, if_neg hi']

/-- From a nonempty history, the terminal observation of an `(n+1)`-step probe
is the startup-mode display of the final probe action, paired with the
world's monitor bit at the terminal clock. Earlier probe actions and all
intermediate observations drop out. -/
theorem terminalChannel_tail (θ : World) (h : History) (hh : h ≠ []) (n : ℕ)
    (a : Fin (n + 1) → Action) :
    terminalChannel θ h (n + 1) a =
      prodLaw (panelDisplay h (a (Fin.last n)))
        (pointMonitor (monitorLabel θ (h.length + n - 1))) := by
  induction n generalizing h with
  | zero =>
    funext o
    simp only [terminalChannel, response_tick θ h _ o hh, prodLaw, Fin.last_zero,
      Nat.add_zero]
  | succ n ih =>
    funext o
    rw [terminalChannel]
    have he (x : Observation) :
        terminalChannel θ (h ++ [(a 0, x)]) (n + 1) (Fin.tail a) o =
          prodLaw (panelDisplay h (a (Fin.last (n + 1))))
            (pointMonitor (monitorLabel θ (h.length + (n + 1) - 1))) o := by
      rw [ih _ (by simp)]
      have hl : (h ++ [(a 0, x)]).length + n - 1 = h.length + (n + 1) - 1 := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [panelDisplay_append h hh, hl]
      simp only [Fin.tail, Fin.succ_last]
    simp_rw [he]
    rw [← sum_mul, (response_valid θ h (a 0)).2, one_mul]

/-! ## Terminal-sensor capacity in bits -/

/-- Capacity of the final observation of an `n`-step probe, in bits.
The paper's full-block capacity is `BlockChannel.blockCapacity`, which retains
all `n` observations. This terminal component is one bit in PLAY mode, whereas
the full block has capacity `n` bits after startup. -/
def multiStepCapacity (θ : World) (h : History) (n : ℕ) : ℝ :=
  capacity (terminalChannel θ h n) / Real.log 2

/-- The display coordinate alone: zero in inspection mode, `log 2` in play mode. -/
theorem panelDisplay_capacity (h : History) (n : ℕ) :
    capacity (fun a : Fin (n + 1) → Action => panelDisplay h (a (Fin.last n))) =
      if inspected h then 0 else Real.log 2 := by
  by_cases hi : inspected h
  · have he : (fun a : Fin (n + 1) → Action => panelDisplay h (a (Fin.last n))) =
        fun _ => pointDisplay 0 := by
      funext a; simp only [panelDisplay, if_pos hi]
    rw [he, capacity_constChannel _ (pointDisplay_valid 0), if_pos hi]
  · have he : (fun a : Fin (n + 1) → Action => panelDisplay h (a (Fin.last n))) =
        terminalPanel n := by
      funext a; simp only [panelDisplay, if_neg hi, terminalPanel]
    rw [he, terminalPanel_capacity, if_neg hi]

theorem multiStepCapacity_tail (θ : World) (h : History) (hh : h ≠ []) (n : ℕ) :
    multiStepCapacity θ h (n + 1) = if inspected h then 0 else 1 := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have he : terminalChannel θ h (n + 1) = fun a =>
      prodLaw (panelDisplay h (a (Fin.last n)))
        (pointMonitor (monitorLabel θ (h.length + n - 1))) := by
    funext a
    exact terminalChannel_tail θ h hh n a
  rw [multiStepCapacity, he,
    capacity_prodLaw_pointMonitor _ (fun a => panelDisplay_valid h (a (Fin.last n))),
    panelDisplay_capacity]
  by_cases hi : inspected h <;> simp [hi, hl]

/-- **Terminal capacity after startup.** For every probe length `n ≥ 1`, every world,
and every nonempty history, the terminal-observation capacity is one bit if the
history did not start with inspection and zero otherwise. -/
theorem multiStepCapacity_of_ne_nil (n : ℕ) (hn : 1 ≤ n) (θ : World) (h : History)
    (hh : h ≠ []) : multiStepCapacity θ h n = if inspected h then 0 else 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact multiStepCapacity_tail θ h hh m

/-! ## The startup channel -/

theorem terminalChannel_root_one (θ : World) (a : Fin 1 → Action) :
    terminalChannel θ [] 1 a = prodLaw (rootDisplay θ (a 0)) (pointMonitor 0) := by
  funext o
  simp [terminalChannel, prodLaw]

/-- The display law at the end of a probe of length at least two that starts at
the empty history: its first action fixes the mode, its last action the group. -/
def rootProbeDisplay (n : ℕ) (a : Fin (n + 2) → Action) : Display → ℝ :=
  if a 0 = inspect then pointDisplay 0 else pairDist (a (Fin.last (n + 1)) == play1)

theorem rootProbeDisplay_valid (n : ℕ) : IsFiniteExperiment (rootProbeDisplay n) := by
  intro a
  unfold rootProbeDisplay
  split
  · exact pointDisplay_valid 0
  · exact pairDist_valid _

theorem terminalChannel_root_succ (θ : World) (n : ℕ) (a : Fin (n + 2) → Action) :
    terminalChannel θ [] (n + 2) a =
      prodLaw (rootProbeDisplay n a) (pointMonitor (monitorLabel θ n)) := by
  funext o
  rw [terminalChannel]
  have he (x : Observation) :
      terminalChannel θ ([] ++ [(a 0, x)]) (n + 1) (Fin.tail a) o =
        prodLaw (rootProbeDisplay n a) (pointMonitor (monitorLabel θ n)) o := by
    rw [terminalChannel_tail θ _ (by simp) n]
    have hp : panelDisplay ([] ++ [(a 0, x)]) (Fin.tail a (Fin.last n)) =
        rootProbeDisplay n a := by
      have hlast : Fin.tail a (Fin.last n) = a (Fin.last (n + 1)) := by
        simp only [Fin.tail, Fin.succ_last]
      rw [hlast]
      by_cases ha : a 0 = inspect
      · have hi : inspected ([] ++ [(a 0, x)]) := by simp [ha]
        simp only [panelDisplay, rootProbeDisplay, if_pos hi, if_pos ha]
      · have hi : ¬ inspected ([] ++ [(a 0, x)]) := by simp [ha]
        simp only [panelDisplay, rootProbeDisplay, if_neg hi, if_neg ha]
    have hl : ([] ++ [(a 0, x)] : History).length + n - 1 = n := by simp
    rw [hp, hl]
  simp_rw [he]
  rw [← sum_mul, (response_valid θ [] (a 0)).2, one_mul]

/-- For probes of length at least two, the startup capacity does not depend on
the world at all: the world enters only through a constant monitor bit. -/
theorem multiStepCapacity_root_succ (θ : World) (n : ℕ) :
    multiStepCapacity θ [] (n + 2) =
      capacity (rootProbeDisplay n) / Real.log 2 := by
  have hc : terminalChannel θ [] (n + 2) =
      fun a => prodLaw (rootProbeDisplay n a) (pointMonitor (monitorLabel θ n)) := by
    funext a
    exact terminalChannel_root_succ θ n a
  rw [multiStepCapacity, hc, capacity_prodLaw_pointMonitor _ (rootProbeDisplay_valid n)]

/-- The startup capacity is constant over the finite alarm times. -/
theorem multiStepCapacity_root_some (n k : ℕ) :
    multiStepCapacity (some k) [] (n + 1) = multiStepCapacity (some 0) [] (n + 1) := by
  cases n with
  | zero =>
    have he : terminalChannel (some k) [] 1 = terminalChannel (some 0) [] 1 := by
      funext a
      rw [terminalChannel_root_one, terminalChannel_root_one]
      simp [rootDisplay]
    rw [multiStepCapacity, multiStepCapacity, he]
  | succ n =>
    rw [multiStepCapacity_root_succ, multiStepCapacity_root_succ]

/-! ## Bounds -/

theorem multiStepCapacity_nonneg (θ : World) (h : History) (n : ℕ) :
    0 ≤ multiStepCapacity θ h n :=
  div_nonneg (capacity_nonneg_of_valid _ (terminalChannel_valid θ h n))
    (Real.log_nonneg (by norm_num))

/-- Every value is at most `log₂ 8 = 3` bits, the size of the raw alphabet. -/
theorem multiStepCapacity_le_three (θ : World) (h : History) (n : ℕ) :
    multiStepCapacity θ h n ≤ 3 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := capacity_le_log_card_output _ (terminalChannel_valid θ h n)
  have hcard : (Fintype.card Observation : ℝ) = 2 ^ 3 := by
    simp only [Observation, Display, Monitor, Fintype.card_prod, Fintype.card_fin]
    norm_num
  rw [hcard, Real.log_pow] at hc
  rw [multiStepCapacity, div_le_iff₀ hl]
  push_cast at hc
  linarith

end IdExp.PairedAlarm.Empowerment
