import Formal.CausalBehaviorExperiment
import Formal.DeterministicDeficiency

/-!
# The current paired alarm with deterministic startup

A variant of `Formal.AlarmPanel` in which inspection startup is deterministic,
PLAY startup is deterministic, and every observation after startup
reports the panel display and the alarm monitor together, instead of
alternating panel ticks with monitor ticks.

Three actions, observations `Fin 4 × Fin 2` (display label, monitor bit), and
the same countable alarm-time class `Option ℕ`. The first action alone selects
the mode. The startup observation carries the startup display label and a
constant monitor bit `0`; alarm tick `k` is reported by the observation made
after a history of length `k+1`, so it occupies trace position `k+1`.
-/

noncomputable section

namespace IdExp.PairedAlarm

open Finset

abbrev Action := Fin 3
abbrev Display := Fin 4
abbrev Monitor := Fin 2
abbrev Observation := Display × Monitor
abbrev World := Option ℕ
abbrev History := CausalHistory Action Observation

def inspect : Action := 0
def play0 : Action := 1
def play1 : Action := 2

/-- Whether the startup action was inspection; false on the empty history. -/
def inspected (h : History) : Prop := (h.head?).map Prod.fst = some inspect
instance (h : History) : Decidable (inspected h) := inferInstanceAs
  (Decidable ((h.head?).map Prod.fst = some inspect))

/-- A fresh fair color attached to a specified high bit. -/
def pairDist (b : Bool) (d : Display) : ℝ :=
  if d.val / 2 = (if b then 1 else 0) then 1 / 2 else 0

/-- A uniform display marginal used by channel-capacity calculations. This is
not the startup response under PLAY, which is `pointDisplay 0`. -/
def uniformDist (_ : Display) : ℝ := 1 / 4

/-- The prior-predictive INSPECT display under the fair prior on the hidden
startup bit. Its uncertainty is over worlds, not an environmental startup coin:
`rootDisplay θ inspect` is a point mass for each fixed world `θ`. -/
def evenCoin (d : Display) : ℝ := if d.val = 0 ∨ d.val = 2 then 1 / 2 else 0

def pointDisplay (x d : Display) : ℝ := if d = x then 1 else 0

def pointMonitor (x m : Monitor) : ℝ := if m = x then 1 else 0

/-- Product of a display law and a monitor law. -/
def prodLaw (f : Display → ℝ) (g : Monitor → ℝ) (o : Observation) : ℝ := f o.1 * g o.2

/-- Pulse index is counted from zero. -/
def monitorLabel (θ : World) (k : ℕ) : Monitor := if θ = some k then 1 else 0

/-- The startup display law. -/
def rootDisplay (θ : World) (a : Action) : Display → ℝ :=
  if a = inspect then pointDisplay (if θ.isSome then 2 else 0) else pointDisplay 0

/-- The later display law; it does not depend on the world. -/
def panelDisplay (h : History) (a : Action) : Display → ℝ :=
  if inspected h then pointDisplay 0 else pairDist (a == play1)

/-- The literal response law, including arbitrary off-support histories. -/
def response (θ : World) : CausalResponse Action Observation := fun h a =>
  if h = [] then prodLaw (rootDisplay θ a) (pointMonitor 0)
  else prodLaw (panelDisplay h a) (pointMonitor (monitorLabel θ (h.length - 1)))

@[simp] theorem pairDist_valid (b : Bool) : IsDist (pairDist b) := by
  constructor
  · intro o; exact ite_nonneg (by norm_num) (by norm_num)
  · cases b <;> norm_num [pairDist, Fin.sum_univ_succ]

@[simp] theorem uniformDist_valid : IsDist uniformDist := by
  constructor
  · intro o; norm_num [uniformDist]
  · norm_num [uniformDist, Fin.sum_univ_succ]

@[simp] theorem evenCoin_valid : IsDist evenCoin := by
  constructor
  · intro d; unfold evenCoin; split_ifs <;> norm_num
  · norm_num [evenCoin, Fin.sum_univ_succ]

@[simp] theorem pointDisplay_valid (x : Display) : IsDist (pointDisplay x) := by
  constructor
  · intro o; unfold pointDisplay; split <;> norm_num
  · simp [pointDisplay]

@[simp] theorem pointDisplay_ne_zero_iff (x d : Display) :
    pointDisplay x d ≠ 0 ↔ d = x := by
  simp [pointDisplay]

theorem pointDisplay_highBit (b : Bool) (d : Display)
    (h : pointDisplay (if b then 2 else 0) d ≠ 0) :
    decide (2 ≤ d.val) = b := by
  rw [pointDisplay_ne_zero_iff] at h
  subst d
  cases b <;> decide

@[simp] theorem pointMonitor_valid (x : Monitor) : IsDist (pointMonitor x) := by
  constructor
  · intro o; unfold pointMonitor; split <;> norm_num
  · simp [pointMonitor]

theorem sum_prodLaw (f : Display → ℝ) (g : Monitor → ℝ) :
    ∑ o, prodLaw f g o = (∑ d, f d) * (∑ m, g m) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  rfl

theorem prodLaw_valid {f : Display → ℝ} {g : Monitor → ℝ}
    (hf : IsDist f) (hg : IsDist g) : IsDist (prodLaw f g) := by
  constructor
  · intro o; exact mul_nonneg (hf.1 o.1) (hg.1 o.2)
  · rw [sum_prodLaw, hf.2, hg.2, one_mul]

theorem rootDisplay_valid (θ : World) (a : Action) : IsDist (rootDisplay θ a) := by
  unfold rootDisplay; split
  · exact pointDisplay_valid _
  · exact pointDisplay_valid 0

theorem panelDisplay_valid (h : History) (a : Action) : IsDist (panelDisplay h a) := by
  unfold panelDisplay; split
  · exact pointDisplay_valid _
  · exact pairDist_valid _

theorem response_valid (θ : World) : IsCausalResponse (response θ) := by
  intro h a
  unfold response
  split
  · exact prodLaw_valid (rootDisplay_valid θ a) (pointMonitor_valid 0)
  · exact prodLaw_valid (panelDisplay_valid h a) (pointMonitor_valid _)

noncomputable def behavior (θ : World) : CausalBehavior Action Observation :=
  CausalBehavior.ofResponse (response θ) (response_valid θ)

@[simp] theorem response_root (θ : World) (a : Action) (o : Observation) :
    response θ [] a o = rootDisplay θ a o.1 * pointMonitor 0 o.2 := by
  simp [response, prodLaw]

theorem response_tick (θ : World) (h : History) (a : Action) (o : Observation)
    (hh : h ≠ []) :
    response θ h a o =
      panelDisplay h a o.1 * pointMonitor (monitorLabel θ (h.length - 1)) o.2 := by
  simp [response, hh, prodLaw]

@[simp] theorem inspected_cons (a : Action) (o : Observation) (h : History) :
    inspected ((a,o)::h) ↔ a = inspect := by simp [inspected]

@[simp] theorem not_inspected_nil : ¬ inspected ([] : History) := by simp [inspected]

/-- Actual finite collected experiments, with the full action-observation record. -/
noncomputable def experiment (π : CausalPolicy Action Observation) (t : ℕ) :
    FiniteExperiment World (CausalFiniteTrace Action Observation t) :=
  causalFiniteExperiment π response t

theorem experiment_valid (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ) : IsFiniteExperiment (experiment π t) :=
  causalFiniteExperiment_valid π hπ response response_valid t

theorem experiment_behavior (π : CausalPolicy Action Observation) (t : ℕ) :
    experiment π t = causalBehaviorFiniteExperiment π behavior t := by
  symm
  exact causalBehaviorFiniteExperiment_ofResponse π response response_valid t

/-- Root inspection probability; later choices are unrestricted. -/
def inspectionProbability (π : CausalPolicy Action Observation) : ℝ := π [] inspect

theorem inspectionProbability_nonneg (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) : 0 ≤ inspectionProbability π := (hπ []).1 _

theorem inspectionProbability_le_one (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) : inspectionProbability π ≤ 1 := by
  have hsum := (hπ []).2
  have h0 := (hπ []).1 (0 : Action)
  have h1 := (hπ []).1 (1 : Action)
  have h2 := (hπ []).1 (2 : Action)
  simp only [Fin.sum_univ_succ] at hsum
  change π [] 0 ≤ 1
  norm_num at hsum
  linarith

end IdExp.PairedAlarm
