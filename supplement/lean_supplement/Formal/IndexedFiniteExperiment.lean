import Formal.DeficiencyTriangle

/-!
# Heterogeneous finite experiments in one ambient type

A dependent pair retains each experiment's finite signal alphabet and validity
proof. Its deficiency is the existing matrix deficiency, so abstract process
theorems can apply without imposing a common alphabet or a finite world class.
-/

namespace IdExp

/-- An experiment with a signal alphabet chosen from an indexed family. -/
abbrev IndexedFiniteExperiment (Θ : Type*) {ι : Type*} (X : ι → Type*)
    [∀ i, Fintype (X i)] :=
  Σ i, {E : FiniteExperiment Θ (X i) // IsFiniteExperiment E}

variable {Θ ι : Type*} {X : ι → Type*} [∀ i, Fintype (X i)]

/-- Directed deficiency retains the two original signal alphabets. -/
noncomputable def indexedFiniteDeficiency (E F : IndexedFiniteExperiment Θ X) : ℝ :=
  finiteDeficiency E.2.1 F.2.1

theorem indexedFiniteDeficiency_triangle [Nonempty Θ]
    (E F G : IndexedFiniteExperiment Θ X) :
    indexedFiniteDeficiency E G ≤ indexedFiniteDeficiency E F + indexedFiniteDeficiency F G :=
  finiteDeficiency_triangle E.2.1 F.2.1 G.2.1 E.2.2 F.2.2 G.2.2

end IdExp
