import Formal.DeterministicDeficiency
import Formal.CausalBehaviorCapability

/-!
# The countable Delayed Signal and Immediate Query controlled behaviors

World `none` is the extra infinity world; `some k` is the finite world k.
Action false is WAIT and true is QUERY. A root QUERY immediately reports
whether the world is finite and is followed by zeros. A root WAIT is followed
by the unique pulse at step k+2 in world k; later actions have no effect.
All displayed record identities concern the actual controlled behavior and
literal action-observation history, rather than a finite world restriction.
-/

namespace IdExp

open Finset Set

abbrev WaitingQueryWorld := Option ℕ

/-- Zero-indexed WAIT observation: world k pulses at index k+1. -/
def waitingQueryBit (θ : WaitingQueryWorld) (i : ℕ) : Bool :=
  match θ with
  | none => false
  | some k => decide (i = k + 1)

/-- Deterministic output rule on every syntactic history. -/
def waitingQueryOutput (θ : WaitingQueryWorld)
    (h : CausalHistory Bool Bool) (a : Bool) : Bool :=
  if h = [] then a && θ.isSome
  else if (h.headD (false, false)).1 then false
  else waitingQueryBit θ h.length

/-- Canonical controlled behavior of the deterministic output rule. -/
noncomputable def waitingQueryBehavior (θ : WaitingQueryWorld) : CausalBehavior Bool Bool :=
  CausalBehavior.ofResponse (detResponse (waitingQueryOutput θ))
    (isCausalResponse_detResponse (waitingQueryOutput θ))

/-- The collector always supplies WAIT. -/
noncomputable def waitingQueryPolicy : CausalPolicy Bool Bool := detPolicy (fun _ => false)

theorem waitingQueryPolicy_valid : IsCausalPolicy waitingQueryPolicy :=
  isCausalPolicy_detPolicy _

/-- The complete deterministic acquired trace, including its WAIT actions. -/
def waitingQueryTrace (t : ℕ) (θ : WaitingQueryWorld) : CausalFiniteTrace Bool Bool t :=
  fun i => (false, waitingQueryBit θ i.1)

/-- The next observation along the literal WAIT history. -/
theorem waitingQueryOutput_waitTrace (t : ℕ) (θ : WaitingQueryWorld) :
    waitingQueryOutput θ (List.ofFn (waitingQueryTrace t θ)) false = waitingQueryBit θ t := by
  cases t with
  | zero => cases θ <;> simp [waitingQueryOutput, waitingQueryBit]
  | succ t => simp [waitingQueryOutput, waitingQueryTrace, List.ofFn_succ]

/-- The deterministic execution unfolds to the stated full trace at every
finite time, uniformly over the entire countable world class. -/
theorem waitingQuery_detTraceList (t : ℕ) (θ : WaitingQueryWorld) :
    detTraceList (fun _ => false) (waitingQueryOutput θ) t =
      List.ofFn (waitingQueryTrace t θ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [detTraceList_succ, ih, waitingQueryOutput_waitTrace]
    rw [List.ofFn_succ']
    simp [waitingQueryTrace, List.concat_eq_append]
    rfl

theorem waitingQuery_detTraceFin (t : ℕ) (θ : WaitingQueryWorld) :
    detTraceFin (fun _ => false) (waitingQueryOutput θ) t = waitingQueryTrace t θ := by
  apply List.ofFn_injective
  rw [ofFn_detTraceFin, waitingQuery_detTraceList]

/-- The actual acquired experiment on canonical controlled behaviors. -/
noncomputable def waitingQueryExperiment (t : ℕ) :
    FiniteExperiment WaitingQueryWorld (CausalFiniteTrace Bool Bool t) :=
  causalBehaviorFiniteExperiment waitingQueryPolicy waitingQueryBehavior t

theorem waitingQueryExperiment_eq_dirac (t : ℕ) :
    waitingQueryExperiment t = diracExp (waitingQueryTrace t) := by
  change causalBehaviorFiniteExperiment (detPolicy (fun _ => false))
    (fun θ => CausalBehavior.ofResponse (detResponse (waitingQueryOutput θ))
      (isCausalResponse_detResponse _)) t = _
  rw [causalBehaviorFiniteExperiment_ofResponse, causalFiniteExperiment_det]
  simp_rw [waitingQuery_detTraceFin]

theorem waitingQueryExperiment_valid (t : ℕ) : IsFiniteExperiment (waitingQueryExperiment t) := by
  rw [waitingQueryExperiment_eq_dirac]
  exact diracExp_valid _

/-- Undetected finite worlds have exactly the infinity world's full record. -/
theorem waitingQueryTrace_undetected (t k : ℕ) (hk : t < k + 2) :
    waitingQueryTrace t (some k) = waitingQueryTrace t none := by
  funext i
  have hne : i.1 ≠ k + 1 := by omega
  simp [waitingQueryTrace, waitingQueryBit, hne]

/-- Once the pulse has arrived, its index identifies the finite world. -/
theorem waitingQueryTrace_detected_injective (t k : ℕ) (hk : k + 2 ≤ t)
    (θ : WaitingQueryWorld) (h : waitingQueryTrace t (some k) = waitingQueryTrace t θ) :
    θ = some k := by
  have hi : k + 1 < t := by omega
  have hp := congrArg (fun w : CausalFiniteTrace Bool Bool t => (w ⟨k + 1, hi⟩).2) h
  cases θ with
  | none => simp [waitingQueryTrace, waitingQueryBit] at hp
  | some l =>
    simp [waitingQueryTrace, waitingQueryBit] at hp
    congr 1
    omega

/-- A world-independent interpretation of a record: decode a detected pulse
as its exact integer, and interpret every other record as infinity. -/
noncomputable def waitingQueryGuess (t : ℕ) (x : CausalFiniteTrace Bool Bool t) :
    WaitingQueryWorld := by
  classical
  exact if h : ∃ k, k + 2 ≤ t ∧ waitingQueryTrace t (some k) = x then some (Classical.choose h)
    else none

/-- The supplied record decoder is exact outside the undetected finite tail. -/
theorem waitingQueryGuess_exact (t : ℕ) (θ : WaitingQueryWorld)
    (hθ : θ = none ∨ ∃ k, θ = some k ∧ k + 2 ≤ t) :
    waitingQueryGuess t (waitingQueryTrace t θ) = θ := by
  unfold waitingQueryGuess
  split_ifs with h
  · obtain ⟨hk, heq⟩ := Classical.choose_spec h
    exact (waitingQueryTrace_detected_injective t (Classical.choose h) hk θ heq).symm
  · rcases hθ with rfl | ⟨k, rfl, hk⟩
    · rfl
    · exact (h ⟨k, hk, rfl⟩).elim

/-- The root QUERY target reports whether the world is finite. -/
noncomputable def waitingQueryTarget : FiniteExperiment WaitingQueryWorld Bool :=
  diracExp Option.isSome

/-- The source cannot distinguish a sufficiently delayed finite world from
infinity, but root QUERY distinguishes them perfectly. -/
theorem waitingQuery_half_le_deficiency (t : ℕ) :
    (1 / 2 : ℝ) ≤ finiteDeficiency (waitingQueryExperiment t) waitingQueryTarget := by
  rw [waitingQueryExperiment_eq_dirac]
  apply half_le_finiteDeficiency_diracExp_of_merge
  exact ⟨some t, none, waitingQueryTrace_undetected t t (by omega), by simp⟩

/-- A fair guess has error one half against every deterministic binary target. -/
theorem finiteDeficiency_dirac_binary_le_half {Θ X : Type*} [Fintype X] [Nonempty Θ]
    (e : Θ → X) (f : Θ → Bool) :
    finiteDeficiency (diracExp e) (diracExp f) ≤ (1 / 2 : ℝ) := by
  let G : X → Bool → ℝ := fun _ _ => 1 / 2
  have hG : G ∈ stochasticRules X Bool := by
    intro x _
    constructor
    · intro b; norm_num [G]
    · simp [G]
  apply finiteDeficiency_le_of_decoder _ _ G hG
  intro θ
  rw [decodeErr_diracExp e f hG θ]
  norm_num [G]

theorem waitingQuery_deficiency_eq_half (t : ℕ) :
    finiteDeficiency (waitingQueryExperiment t) waitingQueryTarget = (1 / 2 : ℝ) := by
  apply le_antisymm _ (waitingQuery_half_le_deficiency t)
  rw [waitingQueryExperiment_eq_dirac]
  exact finiteDeficiency_dirac_binary_le_half _ _

end IdExp
