import Formal.DecisionDeficiencyDuality
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Lattice

/-!
# Purposes, recorded-label mixtures, and the audit as a sup of purpose losses

Ingredients for the minimax purpose certificate (`thm:minimax-purpose-certificate`)
on a finite world class.

* A *purpose* is a prior on the class together with a unit-range utility on a
  common finite decision alphabet `Y`; the purpose space is the compact set
  `simplex × cube`.  Its optimized task value is continuous.
* For a finite collector menu `E : ι → …` and finite target family `T`, the
  *loss vector* of a purpose is `L_i(P) = B(P) − V_P(E_i)` with
  `B(P) = max_T V_P(T)`; the loss set is compact.
* The *recorded-label mixture* `E_p` samples `i ∼ p` independently of the
  world and keeps both the label and the signal; its task value is
  `V_P(E_p) = Σ_i p_i V_P(E_i)`.
* The audit `max_T δ(E_p, T)` equals `sup_P Σ_i p_i L_i(P)`, by the exact
  finite-class randomization duality with decision alphabet `Y`.
-/

namespace IdExp

open Finset Set

noncomputable section

set_option linter.unusedSectionVars false

variable {Θ X Y : Type*} [Fintype Θ] [Nonempty Θ] [Fintype X] [Fintype Y] [Nonempty Y]

/-- A purpose: a prior on the class and a utility with decision alphabet `Y`. -/
abbrev Purpose (Θ Y : Type*) := (Θ → ℝ) × (Θ → Y → ℝ)

/-- The compact purpose space: the prior simplex times the unit utility cube. -/
def purposeSet (Θ Y : Type*) [Fintype Θ] [Fintype Y] : Set (Purpose Θ Y) :=
  stdSimplex ℝ Θ ×ˢ Set.pi univ (fun _ : Θ => Set.pi univ (fun _ : Y => Icc (0 : ℝ) 1))

theorem mem_purposeSet_iff {P : Purpose Θ Y} :
    P ∈ purposeSet Θ Y ↔ IsDist P.1 ∧ ∀ θ y, P.2 θ y ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Set.mem_prod.1 h
    exact ⟨h1, fun θ y => Set.mem_pi.1 (Set.mem_pi.1 h2 θ (mem_univ θ)) y (mem_univ y)⟩
  · rintro ⟨h1, h2⟩
    exact Set.mem_prod.2 ⟨h1, Set.mem_pi.2 fun θ _ => Set.mem_pi.2 fun y _ => h2 θ y⟩

theorem isCompact_purposeSet : IsCompact (purposeSet Θ Y) :=
  (isCompact_stdSimplex ℝ Θ).prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)

theorem purposeSet_nonempty : (purposeSet Θ Y).Nonempty := by
  classical
  exact ⟨(uniformPrior Θ, fun _ _ => 0),
    mem_purposeSet_iff.2 ⟨isDist_uniformPrior, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩⟩

/-- The optimized task value of an experiment for a purpose. -/
def purposeValue (E : FiniteExperiment Θ X) (P : Purpose Θ Y) : ℝ :=
  finiteBayesValue E P.1 P.2

theorem continuous_purposeValue (E : FiniteExperiment Θ X) :
    Continuous (purposeValue (Y := Y) E) := by
  unfold purposeValue finiteBayesValue
  refine continuous_finset_sum _ fun x _ => ?_
  refine Continuous.finset_sup'_apply Finset.univ_nonempty fun d _ => ?_
  unfold finiteDecisionScore
  exact continuous_finset_sum _ fun θ _ =>
    (((continuous_apply θ).comp continuous_fst).mul continuous_const).mul
      ((continuous_apply d).comp ((continuous_apply θ).comp continuous_snd))

theorem purposeValue_mem_unitInterval (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    {P : Purpose Θ Y} (hP : P ∈ purposeSet Θ Y) : purposeValue E P ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := mem_purposeSet_iff.1 hP
  exact finiteBayesValue_mem_unitInterval E hE P.1 h1 P.2 h2

theorem purposeValue_sub_le_finiteDeficiency {Z : Type*} [Fintype Z]
    (E : FiniteExperiment Θ Z) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    {P : Purpose Θ Y} (hP : P ∈ purposeSet Θ Y) :
    purposeValue F P - purposeValue E P ≤ finiteDeficiency E F := by
  obtain ⟨h1, h2⟩ := mem_purposeSet_iff.1 hP
  exact finiteBayesValue_sub_le_finiteDeficiency E F hE hF P.1 h1 P.2 h2

variable {J : Type*} [Fintype J] [Nonempty J] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `B(P) = max_T V_P(T)`, the best value obtainable from the target family. -/
def benchmark (T : J → FiniteExperiment Θ Y) (P : Purpose Θ Y) : ℝ :=
  univ.sup' univ_nonempty fun j => purposeValue (T j) P

theorem continuous_benchmark (T : J → FiniteExperiment Θ Y) : Continuous (benchmark T) :=
  Continuous.finset_sup'_apply univ_nonempty fun j _ => continuous_purposeValue (T j)

theorem purposeValue_le_benchmark (T : J → FiniteExperiment Θ Y) (P : Purpose Θ Y) (j : J) :
    purposeValue (T j) P ≤ benchmark T P :=
  Finset.le_sup' (fun j => purposeValue (T j) P) (mem_univ j)

theorem benchmark_le (T : J → FiniteExperiment Θ Y) (P : Purpose Θ Y) (c : ℝ)
    (h : ∀ j, purposeValue (T j) P ≤ c) : benchmark T P ≤ c :=
  Finset.sup'_le _ _ fun j _ => h j

theorem exists_benchmark_eq (T : J → FiniteExperiment Θ Y) (P : Purpose Θ Y) :
    ∃ j, benchmark T P = purposeValue (T j) P := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' univ_nonempty fun j => purposeValue (T j) P
  exact ⟨j, hj⟩

/-- The loss vector `L_i(P) = B(P) − V_P(E_i)` of a purpose against the menu. -/
def purposeLoss (E : ι → FiniteExperiment Θ X) (T : J → FiniteExperiment Θ Y)
    (P : Purpose Θ Y) : ι → ℝ :=
  fun i => benchmark T P - purposeValue (E i) P

theorem continuous_purposeLoss (E : ι → FiniteExperiment Θ X) (T : J → FiniteExperiment Θ Y) :
    Continuous (purposeLoss E T) :=
  continuous_pi fun i => (continuous_benchmark T).sub (continuous_purposeValue (E i))

/-- The compact loss set `{(L_i(P))_i : P a purpose}`. -/
def lossSet (E : ι → FiniteExperiment Θ X) (T : J → FiniteExperiment Θ Y) : Set (ι → ℝ) :=
  purposeLoss E T '' purposeSet Θ Y

theorem isCompact_lossSet (E : ι → FiniteExperiment Θ X) (T : J → FiniteExperiment Θ Y) :
    IsCompact (lossSet E T) :=
  isCompact_purposeSet.image (continuous_purposeLoss E T)

theorem lossSet_nonempty (E : ι → FiniteExperiment Θ X) (T : J → FiniteExperiment Θ Y) :
    (lossSet E T).Nonempty :=
  purposeSet_nonempty.image _

/-! ## Recorded-label mixtures -/

/-- Sample a collector `i ∼ p` independently of the world and retain both the
label and its signal. -/
def mixtureCollector (E : ι → FiniteExperiment Θ X) (p : ι → ℝ) : FiniteExperiment Θ (ι × X) :=
  fun θ z => p z.1 * E z.1 θ z.2

theorem mixtureCollector_valid (E : ι → FiniteExperiment Θ X) (hE : ∀ i, IsFiniteExperiment (E i))
    {p : ι → ℝ} (hp : IsDist p) : IsFiniteExperiment (mixtureCollector E p) := by
  intro θ
  constructor
  · intro z
    exact mul_nonneg (hp.1 z.1) ((hE z.1 θ).1 z.2)
  · unfold mixtureCollector
    rw [Fintype.sum_prod_type]
    show (∑ i, ∑ x, p i * E i θ x) = 1
    calc (∑ i, ∑ x, p i * E i θ x) = ∑ i, p i * ∑ x, E i θ x := by simp_rw [Finset.mul_sum]
      _ = ∑ i, p i := Finset.sum_congr rfl fun i _ => by rw [(hE i θ).2, mul_one]
      _ = 1 := hp.2

/-- **Recorded-label mixtures have linear task value.** -/
theorem purposeValue_mixtureCollector (E : ι → FiniteExperiment Θ X) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (P : Purpose Θ Y) :
    purposeValue (mixtureCollector E p) P = ∑ i, p i * purposeValue (E i) P := by
  unfold purposeValue finiteBayesValue mixtureCollector finiteDecisionScore
  rw [Fintype.sum_prod_type]
  dsimp only
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul₀_sup' (hp i)]
  congr 1
  funext d
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  ring

theorem benchmark_sub_purposeValue_mixture (E : ι → FiniteExperiment Θ X)
    (T : J → FiniteExperiment Θ Y) {p : ι → ℝ} (hp : IsDist p) (P : Purpose Θ Y) :
    benchmark T P - purposeValue (mixtureCollector E p) P = ∑ i, p i * purposeLoss E T P i := by
  rw [purposeValue_mixtureCollector E p hp.1 P]
  unfold purposeLoss
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]

/-! ## The audit against a finite target family -/

/-- `max_T δ(F, T)`. -/
def targetAudit {Z : Type*} [Fintype Z] (F : FiniteExperiment Θ Z)
    (T : J → FiniteExperiment Θ Y) : ℝ :=
  univ.sup' univ_nonempty fun j => finiteDeficiency F (T j)

theorem finiteDeficiency_le_targetAudit {Z : Type*} [Fintype Z] (F : FiniteExperiment Θ Z)
    (T : J → FiniteExperiment Θ Y) (j : J) : finiteDeficiency F (T j) ≤ targetAudit F T :=
  Finset.le_sup' (fun j => finiteDeficiency F (T j)) (mem_univ j)

theorem targetAudit_le {Z : Type*} [Fintype Z] (F : FiniteExperiment Θ Z)
    (T : J → FiniteExperiment Θ Y) (c : ℝ) (h : ∀ j, finiteDeficiency F (T j) ≤ c) :
    targetAudit F T ≤ c :=
  Finset.sup'_le _ _ fun j _ => h j

/-- The mixture's purpose losses `{Σ_i p_i L_i(P) : P a purpose}`. -/
def mixtureLossValues (E : ι → FiniteExperiment Θ X) (T : J → FiniteExperiment Θ Y)
    (p : ι → ℝ) : Set ℝ :=
  (fun P : Purpose Θ Y => ∑ i, p i * purposeLoss E T P i) '' purposeSet Θ Y

theorem mixtureLossValues_nonempty (E : ι → FiniteExperiment Θ X) (T : J → FiniteExperiment Θ Y)
    (p : ι → ℝ) : (mixtureLossValues E T p).Nonempty :=
  purposeSet_nonempty.image _

/-- Every purpose loss of the mixture is at most its audit. -/
theorem mixtureLoss_le_targetAudit (E : ι → FiniteExperiment Θ X)
    (hE : ∀ i, IsFiniteExperiment (E i)) (T : J → FiniteExperiment Θ Y)
    (hT : ∀ j, IsFiniteExperiment (T j)) {p : ι → ℝ} (hp : IsDist p)
    {P : Purpose Θ Y} (hP : P ∈ purposeSet Θ Y) :
    ∑ i, p i * purposeLoss E T P i ≤ targetAudit (mixtureCollector E p) T := by
  rw [← benchmark_sub_purposeValue_mixture E T hp P]
  obtain ⟨j, hj⟩ := exists_benchmark_eq T P
  rw [hj]
  exact (purposeValue_sub_le_finiteDeficiency _ _ (mixtureCollector_valid E hE hp) (hT j) hP).trans
    (finiteDeficiency_le_targetAudit _ T j)

theorem mixtureLossValues_bddAbove (E : ι → FiniteExperiment Θ X)
    (hE : ∀ i, IsFiniteExperiment (E i)) (T : J → FiniteExperiment Θ Y)
    (hT : ∀ j, IsFiniteExperiment (T j)) {p : ι → ℝ} (hp : IsDist p) :
    BddAbove (mixtureLossValues E T p) :=
  ⟨targetAudit (mixtureCollector E p) T, by
    rintro _ ⟨P, hP, rfl⟩
    exact mixtureLoss_le_targetAudit E hE T hT hp hP⟩

/-- **The audit of a recorded-label mixture is the supremum of its purpose
losses**: `max_T δ(E_p, T) = sup_P Σ_i p_i L_i(P)`. -/
theorem targetAudit_mixture_eq_sSup (E : ι → FiniteExperiment Θ X)
    (hE : ∀ i, IsFiniteExperiment (E i)) (T : J → FiniteExperiment Θ Y)
    (hT : ∀ j, IsFiniteExperiment (T j)) {p : ι → ℝ} (hp : IsDist p) :
    targetAudit (mixtureCollector E p) T = sSup (mixtureLossValues E T p) := by
  classical
  have hmix := mixtureCollector_valid E hE hp
  have hbdd := mixtureLossValues_bddAbove E hE T hT hp
  apply le_antisymm
  · apply targetAudit_le
    intro j
    rw [finiteDeficiency_eq_sSup_finiteBayesValueGaps _ _ hmix (hT j)]
    apply csSup_le
    · exact ⟨_, uniformPrior Θ, fun _ _ => 0, isDist_uniformPrior,
        fun _ _ => ⟨le_rfl, zero_le_one⟩, rfl⟩
    rintro _ ⟨α, u, hα, hu, rfl⟩
    have hP : ((α, u) : Purpose Θ Y) ∈ purposeSet Θ Y := mem_purposeSet_iff.2 ⟨hα, hu⟩
    have h1 : finiteBayesValue (T j) α u - finiteBayesValue (mixtureCollector E p) α u ≤
        benchmark T (α, u) - purposeValue (mixtureCollector E p) (α, u) :=
      sub_le_sub_right (purposeValue_le_benchmark T (α, u) j) _
    rw [benchmark_sub_purposeValue_mixture E T hp] at h1
    exact h1.trans (le_csSup hbdd ⟨(α, u), hP, rfl⟩)
  · apply csSup_le (mixtureLossValues_nonempty E T p)
    rintro _ ⟨P, hP, rfl⟩
    exact mixtureLoss_le_targetAudit E hE T hT hp hP

end

end IdExp
