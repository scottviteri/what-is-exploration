import Formal.Experiment

/-!
# Countably many atoms: the exact-label top is unreachable from a finite outcome space

The Lean check of the core of Theorem 3.1(ii) of `TheoryDocs/native_test_geometry.tex`:
a decoder from a finite outcome space `X` to distributions on the parameter space `Θ` is a
Markov kernel `G : Kernel X Θ`.  Each `G x` is a finite measure, so it has at most countably
many atoms (`countable_atoms`), and a finite union of countable sets is countable
(`countable_atoms_bind`).  For `θ` outside that countable set the garbled law
`(E θ).bind G` gives `{θ}` mass zero while `dirac θ` gives it mass one
(`bind_singleton_eq_zero_of_not_mem_atoms`, `mutuallySingular_dirac_bind`), so no
finite-outcome experiment on an uncountable class has the exact-label top
`θ ↦ dirac θ` as a garbling (`not_blackwellLE_dirac_of_uncountable`).  Equivalently, a
finite-outcome experiment that does reach the top must live on a countable class
(`countable_of_blackwellLE_dirac`).

The statements are phrased through `Experiment.lean`'s `BlackwellLE`; the top experiment is
`fun θ => Measure.dirac θ`, the same object as in `Garbling.lean`'s `FullRevelationGarbling`
(there the outcome space is the path space and the class is finite; here the outcome space is
finite and the class is arbitrary).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace IdExp

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace X]

/-- The atoms of a measure: the points whose singleton has positive mass. -/
def atoms (μ : Measure Θ) : Set Θ := {θ | μ {θ} ≠ 0}

theorem mem_atoms {μ : Measure Θ} {θ : Θ} : θ ∈ atoms μ ↔ μ {θ} ≠ 0 := Iff.rfl

/-- **(1) Countably many atoms.**  An s-finite (in particular, any finite or probability)
measure on a space with measurable singletons has countably many atoms: singletons are
pairwise disjoint measurable sets, and only countably many disjoint sets can have positive
mass. -/
theorem countable_atoms (μ : Measure Θ) [SFinite μ] : (atoms μ).Countable := by
  have h := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
    (As := fun θ : Θ => ({θ} : Set Θ)) (fun θ => measurableSet_singleton θ)
    (fun _ _ hab => disjoint_singleton.2 hab)
  exact h.mono fun θ hθ => pos_iff_ne_zero.2 hθ

/-- The same statement for a finite measure. -/
theorem countable_atoms_of_finite_measure (μ : Measure Θ) [IsFiniteMeasure μ] :
    {θ | μ {θ} ≠ 0}.Countable :=
  countable_atoms μ

/-- The mass a garbled law gives a singleton is a finite sum over the outcome space. -/
theorem bind_singleton_eq_sum [Fintype X] [MeasurableSingletonClass X]
    (μ : Measure X) (G : Kernel X Θ) (θ : Θ) :
    (μ.bind fun x => G x) {θ} = ∑ x, G x {θ} * μ {x} := by
  rw [Measure.bind_apply (measurableSet_singleton θ) (Kernel.measurable G).aemeasurable,
    lintegral_fintype]

/-- An atom of a garbled law is an atom of one of the kernel's output measures. -/
theorem atoms_bind_subset [Fintype X] [MeasurableSingletonClass X]
    (μ : Measure X) (G : Kernel X Θ) :
    atoms (μ.bind fun x => G x) ⊆ ⋃ x, atoms (G x) := by
  intro θ hθ
  rw [mem_atoms, bind_singleton_eq_sum] at hθ
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hθ
  exact mem_iUnion.2 ⟨x, left_ne_zero_of_mul hx⟩

/-- **(2) The atoms of every garbled law lie in one countable set.**  For a Markov kernel
`G` from a finite outcome space, `⋃ x, atoms (G x)` is countable and contains every atom
of every `(E θ).bind G`. -/
theorem countable_iUnion_atoms [Fintype X] (G : Kernel X Θ) [IsMarkovKernel G] :
    (⋃ x, atoms (G x)).Countable :=
  countable_iUnion fun x => countable_atoms (G x)

theorem countable_atoms_bind [Fintype X] [MeasurableSingletonClass X]
    (E : Experiment Θ X) (G : Kernel X Θ) [IsMarkovKernel G] :
    {θ | ((E θ).bind fun x => G x) {θ} ≠ 0}.Countable := by
  refine (countable_iUnion_atoms G).mono fun θ hθ => ?_
  exact atoms_bind_subset (E θ) G hθ

/-- **(4) Off the atoms, the garbled law misses the truth entirely** while the top puts
mass one there. -/
theorem bind_singleton_eq_zero_of_not_mem_atoms [Fintype X] [MeasurableSingletonClass X]
    (μ : Measure X) (G : Kernel X Θ) {θ : Θ} (hθ : θ ∉ ⋃ x, atoms (G x)) :
    (μ.bind fun x => G x) {θ} = 0 := by
  by_contra h
  exact hθ (atoms_bind_subset μ G h)

theorem dirac_singleton_eq_one (θ : Θ) : Measure.dirac θ {θ} = 1 :=
  Measure.dirac_apply_of_mem (mem_singleton θ)

/-- Off the countable atom set the garbled law and the point mass at the truth are mutually
singular (total variation one). -/
theorem mutuallySingular_dirac_bind [Fintype X] [MeasurableSingletonClass X]
    (μ : Measure X) (G : Kernel X Θ) {θ : Θ} (hθ : θ ∉ ⋃ x, atoms (G x)) :
    Measure.dirac θ ⟂ₘ (μ.bind fun x => G x) := by
  refine ⟨{θ}ᶜ, (measurableSet_singleton θ).compl, ?_, ?_⟩
  · rw [Measure.dirac_apply' _ (measurableSet_singleton θ).compl]
    simp
  · rw [compl_compl]
    exact bind_singleton_eq_zero_of_not_mem_atoms μ G hθ

/-- The exact-label top: the experiment that reveals the parameter. -/
noncomputable abbrev topExperiment (Θ : Type*) [MeasurableSpace Θ] : Experiment Θ Θ :=
  fun θ => Measure.dirac θ

/-- **A finite-outcome experiment that reaches the top has a countable class.**  If
`θ ↦ dirac θ` is a garbling of `E` through a Markov kernel `G`, every `θ` is an atom of
`(E θ).bind G`, so `Θ` is contained in the countable set of atoms. -/
theorem countable_of_blackwellLE_dirac [Fintype X] [MeasurableSingletonClass X]
    (E : Experiment Θ X) (h : BlackwellLE (topExperiment Θ) E) : Countable Θ := by
  obtain ⟨G, hG, hbind⟩ := h
  let _ : IsMarkovKernel G := hG
  have hall : (univ : Set Θ) ⊆ {θ | ((E θ).bind fun x => G x) {θ} ≠ 0} := by
    intro θ _
    show ((E θ).bind fun x => G x) {θ} ≠ 0
    rw [hbind θ, dirac_singleton_eq_one]
    exact one_ne_zero
  exact countable_univ_iff.1 ((countable_atoms_bind E G).mono hall)

/-- **(3) Theorem 3.1(ii), core.**  On an uncountable class no experiment with a finite
outcome space has the exact-label top as a garbling: there is no Markov kernel `G` with
`(E θ).bind G = dirac θ` for all `θ`. -/
theorem not_blackwellLE_dirac_of_uncountable [Fintype X] [MeasurableSingletonClass X]
    (hΘ : ¬ Countable Θ) (E : Experiment Θ X) : ¬ BlackwellLE (topExperiment Θ) E :=
  fun h => hΘ (countable_of_blackwellLE_dirac E h)

/-- The same statement unfolded, in the form of `Garbling.lean`'s `FullRevelationGarbling`. -/
theorem not_fullRevelation_of_uncountable [Fintype X] [MeasurableSingletonClass X]
    (hΘ : ¬ Countable Θ) (E : Experiment Θ X) :
    ¬ ∃ G : Kernel X Θ, IsMarkovKernel G ∧
      ∀ θ, (E θ).bind (fun x => G x) = Measure.dirac θ :=
  not_blackwellLE_dirac_of_uncountable hΘ E

end IdExp
