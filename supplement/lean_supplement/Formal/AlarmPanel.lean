import Formal.CausalBehaviorExperiment
import Formal.DeterministicDeficiency

/-!
# The shared alarm and panel controlled interface

Three actions, four raw observations and a countable alarm-time class. The
first action alone selects the mode. All policies retain every monitor tick.
The displayed response is a presentation of a normalized controlled behavior.
-/

noncomputable section

namespace IdExp.AlarmPanel

abbrev Action := Fin 3
abbrev Observation := Fin 4
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
def pairDist (b : Bool) (o : Observation) : ℝ :=
  if o.val / 2 = (if b then 1 else 0) then 1 / 2 else 0

def uniformDist (_ : Observation) : ℝ := 1 / 4

def pointDist (x o : Observation) : ℝ := if o = x then 1 else 0

/-- Pulse index is counted from zero. -/
def monitorLabel (θ : World) (k : ℕ) : Observation := if θ = some k then 1 else 0

/-- The literal response law, including arbitrary off-support histories. -/
def response (θ : World) : CausalResponse Action Observation := fun h a o =>
  if h = [] then
    if a = inspect then pairDist θ.isSome o else uniformDist o
  else if h.length % 2 = 1 then
    if inspected h then pointDist 0 o else pairDist (a == play1) o
  else pointDist (monitorLabel θ ((h.length - 2) / 2)) o

@[simp] theorem pairDist_valid (b : Bool) : IsDist (pairDist b) := by
  constructor
  · intro o; exact ite_nonneg (by norm_num) (by norm_num)
  · cases b <;> norm_num [pairDist, Fin.sum_univ_succ]

@[simp] theorem uniformDist_valid : IsDist uniformDist := by
  constructor
  · intro o; norm_num [uniformDist]
  · norm_num [uniformDist, Fin.sum_univ_succ]

@[simp] theorem pointDist_valid (x : Observation) : IsDist (pointDist x) := by
  constructor
  · intro o; unfold pointDist; split <;> norm_num
  · simp [pointDist]

 theorem response_valid (θ : World) : IsCausalResponse (response θ) := by
  intro h a
  unfold response
  split
  · split
    · exact pairDist_valid _
    · exact uniformDist_valid
  · split
    · split
      · exact pointDist_valid _
      · exact pairDist_valid _
    · exact pointDist_valid _

noncomputable def behavior (θ : World) : CausalBehavior Action Observation :=
  CausalBehavior.ofResponse (response θ) (response_valid θ)

@[simp] theorem response_root (θ : World) (a : Action) (o : Observation) :
    response θ [] a o = if a = inspect then pairDist θ.isSome o else uniformDist o := by
  simp [response]

 theorem response_panel (θ : World) (h : History) (a : Action) (o : Observation)
    (hh : h.length % 2 = 1) :
    response θ h a o = if inspected h then pointDist 0 o else pairDist (a == play1) o := by
  have hn : h ≠ [] := by intro he; subst h; simp at hh
  simp [response, hn, hh]

 theorem response_monitor (θ : World) (h : History) (a : Action) (o : Observation)
    (hh : h ≠ []) (he : h.length % 2 ≠ 1) :
    response θ h a o = pointDist (monitorLabel θ ((h.length - 2) / 2)) o := by
  simp [response, hh, he]

@[simp] theorem inspected_cons (a : Action) (o : Observation) (h : History) :
    inspected ((a,o)::h) ↔ a = inspect := by simp [inspected]

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

end IdExp.AlarmPanel
