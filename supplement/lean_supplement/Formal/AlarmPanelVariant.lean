import Formal.AlarmPanel

/-!
# Intervention variants of the alarm/panel interface

Two interventions from the 16 September follow-up, on the same countable world
class, three actions, four raw labels and monitor stream:

* `retain = true`: startup inspection keeps the same controllable colored
  panel afterwards instead of disabling it;
* `p`: every fresh color is Bernoulli(`p`) instead of fair.

`Variant.original` (panel disabled after inspection, `p = 1/2`) is literally
the original response `AlarmPanel.response`.
-/

noncomputable section

namespace IdExp.AlarmPanel

/-- An intervention: whether inspection retains the panel, and the color law. -/
structure Variant where
  retain : Bool
  p : ℝ

namespace Variant

/-- The color probability must be a probability. -/
def Valid (v : Variant) : Prop := 0 ≤ v.p ∧ v.p ≤ 1

/-- The original construction. -/
def original : Variant := ⟨false, 1/2⟩

theorem original_valid : original.Valid := by unfold Valid original; norm_num

/-- Panel retained after inspection, fair colors. -/
def retained : Variant := ⟨true, 1/2⟩

theorem retained_valid : retained.Valid := by unfold Valid retained; norm_num

/-- The original panel rule with a biased color. -/
def colored (p : ℝ) : Variant := ⟨false, p⟩

theorem colored_valid (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : (colored p).Valid := ⟨h0, h1⟩

@[simp] theorem original_retain : original.retain = false := rfl
@[simp] theorem original_p : original.p = 1/2 := rfl
@[simp] theorem retained_retain : retained.retain = true := rfl
@[simp] theorem retained_p : retained.p = 1/2 := rfl
@[simp] theorem colored_retain (p : ℝ) : (colored p).retain = false := rfl
@[simp] theorem colored_p (p : ℝ) : (colored p).p = p := rfl

end Variant

/-- Mass of the known color coordinate, the low bit of a raw label. -/
def colorMass (p : ℝ) (o : Observation) : ℝ := if o.val % 2 = 1 then p else 1 - p

/-- A specified high bit with an independent Bernoulli(`p`) color. -/
def pairDistP (p : ℝ) (b : Bool) (o : Observation) : ℝ :=
  if o.val / 2 = (if b then 1 else 0) then colorMass p o else 0

/-- A fair high bit with an independent Bernoulli(`p`) color. -/
def startupDistP (p : ℝ) (o : Observation) : ℝ := colorMass p o / 2

theorem colorMass_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (o : Observation) :
    0 ≤ colorMass p o := by
  unfold colorMass; split_ifs <;> linarith

theorem pairDistP_sum (p : ℝ) (b : Bool) : ∑ o, pairDistP p b o = 1 := by
  cases b <;> simp [pairDistP, colorMass, Fin.sum_univ_succ] <;> ring

theorem startupDistP_sum (p : ℝ) : ∑ o, startupDistP p o = 1 := by
  simp [startupDistP, colorMass, Fin.sum_univ_succ]; ring

theorem pairDistP_valid {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    IsDist (pairDistP p b) := by
  refine ⟨fun o => ?_, pairDistP_sum p b⟩
  unfold pairDistP
  split_ifs <;> first | exact colorMass_nonneg h0 h1 o | exact le_rfl

theorem startupDistP_valid {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsDist (startupDistP p) := by
  refine ⟨fun o => ?_, startupDistP_sum p⟩
  exact div_nonneg (colorMass_nonneg h0 h1 o) (by norm_num)

theorem pairDistP_half (b : Bool) : pairDistP (1/2) b = pairDist b := by
  funext o
  unfold pairDistP pairDist colorMass
  split_ifs <;> norm_num

theorem startupDistP_half : startupDistP (1/2) = uniformDist := by
  funext o
  unfold startupDistP uniformDist colorMass
  split_ifs <;> norm_num

theorem pairDistP_half_apply (b : Bool) (o : Observation) : pairDistP (1/2) b o = pairDist b o :=
  congrFun (pairDistP_half b) o

theorem pairDistP_inv_two (b : Bool) : pairDistP 2⁻¹ b = pairDist b := by
  rw [← one_div]; exact pairDistP_half b

theorem startupDistP_inv_two : startupDistP 2⁻¹ = uniformDist := by
  rw [← one_div]; exact startupDistP_half

/-- The literal response law of a variant, including off-support histories. -/
def responseV (v : Variant) (θ : World) : CausalResponse Action Observation := fun h a o =>
  if h = [] then
    if a = inspect then pairDistP v.p θ.isSome o else startupDistP v.p o
  else if h.length % 2 = 1 then
    if inspected h ∧ v.retain = false then pointDist 0 o else pairDistP v.p (a == play1) o
  else pointDist (monitorLabel θ ((h.length - 2) / 2)) o

theorem responseV_valid (v : Variant) (hv : v.Valid) (θ : World) :
    IsCausalResponse (responseV v θ) := by
  intro h a
  unfold responseV
  split
  · split
    · exact pairDistP_valid hv.1 hv.2 _
    · exact startupDistP_valid hv.1 hv.2
  · split
    · split
      · exact pointDist_valid _
      · exact pairDistP_valid hv.1 hv.2 _
    · exact pointDist_valid _

/-- The original variant is the literal original response. -/
theorem responseV_original : responseV Variant.original = response := by
  funext θ h a o
  simp [responseV, response, Variant.original, pairDistP_inv_two, startupDistP_inv_two]

@[simp] theorem responseV_root (v : Variant) (θ : World) (a : Action) (o : Observation) :
    responseV v θ [] a o =
      if a = inspect then pairDistP v.p θ.isSome o else startupDistP v.p o := by
  simp [responseV]

theorem responseV_panel (v : Variant) (θ : World) (h : History) (a : Action) (o : Observation)
    (hh : h.length % 2 = 1) :
    responseV v θ h a o =
      if inspected h ∧ v.retain = false then pointDist 0 o else pairDistP v.p (a == play1) o := by
  have hn : h ≠ [] := by intro he; subst h; simp at hh
  simp [responseV, hn, hh]

theorem responseV_monitor (v : Variant) (θ : World) (h : History) (a : Action) (o : Observation)
    (hh : h ≠ []) (he : h.length % 2 ≠ 1) :
    responseV v θ h a o = pointDist (monitorLabel θ ((h.length - 2) / 2)) o := by
  simp [responseV, hh, he]

/-- Actual finite collected experiments of a variant, with the full record. -/
noncomputable def experimentV (v : Variant) (π : CausalPolicy Action Observation) (t : ℕ) :
    FiniteExperiment World (CausalFiniteTrace Action Observation t) :=
  causalFiniteExperiment π (responseV v) t

theorem experimentV_valid (v : Variant) (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ) : IsFiniteExperiment (experimentV v π t) :=
  causalFiniteExperiment_valid π hπ (responseV v) (responseV_valid v hv) t

theorem experimentV_original (π : CausalPolicy Action Observation) (t : ℕ) :
    experimentV Variant.original π t = experiment π t := by
  simp [experimentV, experiment, responseV_original]

end IdExp.AlarmPanel
