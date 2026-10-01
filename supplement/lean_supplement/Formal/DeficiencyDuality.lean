import Formal.DeficiencyTriangle
import Formal.BlackwellConverse

/-!
# Strong duality for finite directed deficiency

**Relevance:** direct current-paper support, finite-experiment scope.

For finite experiments `E : FiniteExperiment Θ X` and `F : FiniteExperiment Θ Y`
over a general finite world class `Θ`, the directed deficiency
`finiteDeficiency E F` is the infimum over stochastic decoders `G` of the
worst-row total-variation error `max_θ TV(E ⬝ G, F)`.  A *box-constrained dual
witness* is a pair `(lam, w)` with `lam` a prior on `Θ` and payoffs
`0 ≤ w θ y ≤ lam θ`; its value is

    (∑ θ y, w θ y * F θ y) - max_σ ∑ x θ, E θ x * w θ (σ x),

the maximum running over deterministic selections `σ : X → Y`.

* `DualCertificate.lean` proves **weak duality**: every such value
  (there written as `finiteDualCertificateValue E F mu` with `mu = lam - w`, see
  `finiteDualCertificateValue_eq_boxDual` below) is at most the deficiency.
* This file proves **strong duality** for general finite `Θ`
  (`exists_boxDual_gt_of_lt_finiteDeficiency`): every level `r` strictly below
  `finiteDeficiency E F` is beaten by some box-constrained dual witness,
  uniformly over all selections `σ`.  Consequently the paper's finite dual
  certificate is tight: the supremum of admissible certificate values equals
  the deficiency (`finiteDeficiency_eq_sSup_finiteDualCertificateValue`).
* `BinaryDeficiencyIdentity.lean` is the two-world specialization
  `Θ = Bool`, where the same separation argument is pushed further to the
  closed-form identity `finiteDeficiency E F = binaryCallGap E F`.  That module
  keeps its own `tvBall` (unit-row-sum pairs); the general product of rowwise
  TV balls here is called `rowTVBall` to avoid a name clash.

**Proof.**  Below the deficiency, the compact convex menu of decoded laws
`{E ⬝ G : G stochastic}` (`finiteMatrixCapabilityMenu`) is disjoint from the
closed convex product of rowwise total-variation balls `rowTVBall F r`.
Mathlib's `geometric_hahn_banach_compact_closed` gives a continuous linear
functional strictly separating them; on `Θ → Y → ℝ` it is a coefficient matrix
`w0`.  Evaluating at one deterministic decoder (`selectionRule σ`) and at the
target with mass `r` shifted from each row's argmax coordinate to its argmin
coordinate (`shiftedTarget`) yields `r * ∑ θ, osc θ < value(w0 - rowmin)`
where `osc θ` is the row oscillation of `w0`.  The oscillation sum is positive
(otherwise the shifted target would coincide with a decoded law), and dividing
by it normalizes `lam := osc / ∑ osc` to a prior and `w := (w0 - rowmin) / ∑ osc`
into the box `0 ≤ w ≤ lam`.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset Set

section Duality

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]



/-- The closed convex product of rowwise total-variation balls around the
target rows.  (Row sums are not constrained; the set only needs to be closed,
convex, and to contain the mass-shifted targets used in the proof.) -/
def rowTVBall (F : FiniteExperiment Θ Y) (r : ℝ) : Set (Θ → Y → ℝ) :=
  {q | ∀ θ, finiteTV (q θ) (F θ) ≤ r}

theorem continuous_finiteTV_row (F : FiniteExperiment Θ Y) (θ : Θ) :
    Continuous fun q : Θ → Y → ℝ => finiteTV (q θ) (F θ) := by
  unfold finiteTV
  fun_prop

theorem isClosed_rowTVBall (F : FiniteExperiment Θ Y) (r : ℝ) : IsClosed (rowTVBall F r) := by
  unfold rowTVBall
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun θ => isClosed_le (continuous_finiteTV_row F θ) continuous_const

theorem convex_rowTVBall (F : FiniteExperiment Θ Y) (r : ℝ) : Convex ℝ (rowTVBall F r) := by
  intro q hq q' hq' a b ha hb hab θ
  have hb1 : b ≤ 1 := by linarith
  have h := finiteTV_affine_le_max (q θ) (q' θ) (F θ) (F θ) b hb hb1
  have hF : (fun y => (1 - b) * F θ y + b * F θ y) = F θ := by
    funext y; ring
  rw [hF] at h
  have hq'' : (fun y => (1 - b) * q θ y + b * q' θ y) = (a • q + b • q') θ := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show a = 1 - b by linarith]
  rw [hq''] at h
  exact h.trans (max_le (hq θ) (hq' θ))

/-- Below the deficiency, no decoded law lies in the TV-ball product. -/
theorem disjoint_menu_rowTVBall [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    {r : ℝ} (hr : r < finiteDeficiency E F) :
    Disjoint (finiteMatrixCapabilityMenu (D := Y) E) (rowTVBall F r) := by
  rw [Set.disjoint_left]
  rintro _ ⟨G, hG, rfl⟩ hq
  have hmem : r ∈ finiteDeficiencyCandidates E F := ⟨G, hG, fun θ => hq θ⟩
  have hle : finiteDeficiency E F ≤ r :=
    csInf_le (finiteDeficiencyCandidates_bddBelow E F) hmem
  exact absurd hr (not_lt.mpr hle)

/-- The deterministic decoder that maps each source signal to a chosen
target signal. -/
def selectionRule [DecidableEq Y] (σ : X → Y) : X → Y → ℝ :=
  fun x y => if y = σ x then 1 else 0

theorem selectionRule_mem_stochasticRules [DecidableEq Y] (σ : X → Y) :
    selectionRule σ ∈ stochasticRules X Y := by
  intro x _
  constructor
  · intro y
    unfold selectionRule
    split_ifs <;> norm_num
  · simp [selectionRule]

/-- Coefficient sum of a functional at a deterministic decoder's law. -/
theorem sum_finiteDecisionLaw_selectionRule [DecidableEq Y]
    (E : FiniteExperiment Θ X) (σ : X → Y) (w : Θ → Y → ℝ) :
    ∑ θ, ∑ y, finiteDecisionLaw E (selectionRule σ) θ y * w θ y =
      ∑ x, ∑ θ, E θ x * w θ (σ x) := by
  have hθ : ∀ θ, ∑ y, finiteDecisionLaw E (selectionRule σ) θ y * w θ y =
      ∑ x, E θ x * w θ (σ x) := by
    intro θ
    simp only [finiteDecisionLaw, selectionRule, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp [mul_ite, Finset.sum_ite_eq']
  simp_rw [hθ]
  exact Finset.sum_comm

/-- The target rows with mass `r` moved from one signal to another. -/
def shiftedTarget [DecidableEq Y] (F : FiniteExperiment Θ Y) (r : ℝ)
    (ymax ymin : Θ → Y) : Θ → Y → ℝ :=
  fun θ y => F θ y - (if y = ymax θ then r else 0) + (if y = ymin θ then r else 0)

theorem shiftedTarget_mem_rowTVBall [DecidableEq Y] (F : FiniteExperiment Θ Y)
    {r : ℝ} (hr : 0 ≤ r) (ymax ymin : Θ → Y) :
    shiftedTarget F r ymax ymin ∈ rowTVBall F r := by
  intro θ
  unfold finiteTV shiftedTarget
  have hpt : ∀ y,
      |F θ y - (if y = ymax θ then r else 0) + (if y = ymin θ then r else 0) - F θ y| ≤
        (if y = ymax θ then r else 0) + (if y = ymin θ then r else 0) := by
    intro y
    have h1 : 0 ≤ (if y = ymax θ then r else 0) := by split_ifs <;> linarith
    have h2 : 0 ≤ (if y = ymin θ then r else 0) := by split_ifs <;> linarith
    have heq : F θ y - (if y = ymax θ then r else 0) + (if y = ymin θ then r else 0) - F θ y =
        (if y = ymin θ then r else 0) - (if y = ymax θ then r else 0) := by ring
    rw [heq]
    calc |(if y = ymin θ then r else 0) - (if y = ymax θ then r else 0)| ≤
          |(if y = ymin θ then r else 0)| + |(if y = ymax θ then r else 0)| := abs_sub _ _
      _ = (if y = ymax θ then r else 0) + (if y = ymin θ then r else 0) := by
          rw [abs_of_nonneg h1, abs_of_nonneg h2]; ring
  calc (1 / 2 : ℝ) * ∑ y, |F θ y - (if y = ymax θ then r else 0) +
        (if y = ymin θ then r else 0) - F θ y| ≤
      (1 / 2 : ℝ) * ∑ y, ((if y = ymax θ then r else 0) + (if y = ymin θ then r else 0)) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hpt y) (by norm_num)
    _ = r := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp
        ring

theorem sum_shiftedTarget [DecidableEq Y] (F : FiniteExperiment Θ Y) (r : ℝ)
    (ymax ymin : Θ → Y) (w : Θ → Y → ℝ) :
    ∑ θ, ∑ y, shiftedTarget F r ymax ymin θ y * w θ y =
      ∑ θ, ∑ y, F θ y * w θ y - r * ∑ θ, (w θ (ymax θ) - w θ (ymin θ)) := by
  have hθ : ∀ θ, ∑ y, shiftedTarget F r ymax ymin θ y * w θ y =
      ∑ y, F θ y * w θ y - r * (w θ (ymax θ) - w θ (ymin θ)) := by
    intro θ
    unfold shiftedTarget
    have hpt : ∀ y, (F θ y - (if y = ymax θ then r else 0) +
        (if y = ymin θ then r else 0)) * w θ y =
        F θ y * w θ y - (if y = ymax θ then r * w θ y else 0) +
          (if y = ymin θ then r * w θ y else 0) := by
      intro y
      split_ifs <;> ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
    ring
  simp_rw [hθ]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Strong duality for finite directed deficiency.**  Every level strictly
below the deficiency is beaten by a box-constrained dual witness. -/
theorem exists_boxDual_gt_of_lt_finiteDeficiency [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    {r : ℝ} (hr : r < finiteDeficiency E F) :
    ∃ (lam : Θ → ℝ) (w : Θ → Y → ℝ), IsDist lam ∧ (∀ θ y, 0 ≤ w θ y) ∧
      (∀ θ y, w θ y ≤ lam θ) ∧
      ∀ σ : X → Y, r < (∑ θ, ∑ y, w θ y * F θ y) - ∑ x, ∑ θ, E θ x * w θ (σ x) := by
  classical
  have hY : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  rcases lt_or_ge r 0 with hr0 | hr0
  · refine ⟨uniformPrior Θ, fun _ _ => 0, isDist_uniformPrior, fun _ _ => le_rfl,
      fun θ _ => (isDist_uniformPrior (Θ := Θ)).1 θ, fun σ => by simpa using hr0⟩
  obtain ⟨f, u, v, hfD, huv, hfB⟩ := geometric_hahn_banach_compact_closed
    (convex_finiteMatrixCapabilityMenu E) (isCompact_finiteMatrixCapabilityMenu E)
    (convex_rowTVBall F r) (isClosed_rowTVBall F r) (disjoint_menu_rowTVBall E F hr)
  set w0 : Θ → Y → ℝ := fun θ y => f (Pi.single θ (Pi.single y 1)) with hw0
  have hf : ∀ q, f q = ∑ θ, ∑ y, q θ y * w0 θ y := fun q => strongDual_apply_eq f q
  choose ymax _ hymax using fun θ => Finset.exists_max_image Finset.univ (w0 θ) Finset.univ_nonempty
  choose ymin _ hymin using fun θ => Finset.exists_min_image Finset.univ (w0 θ) Finset.univ_nonempty
  have hi : ∀ σ : X → Y, ∑ x, ∑ θ, E θ x * w0 θ (σ x) < u := by
    intro σ
    have h := hfD _ ⟨selectionRule σ, selectionRule_mem_stochasticRules σ, rfl⟩
    rw [hf, sum_finiteDecisionLaw_selectionRule] at h
    exact h
  have hii : v < ∑ θ, ∑ y, F θ y * w0 θ y - r * ∑ θ, (w0 θ (ymax θ) - w0 θ (ymin θ)) := by
    have h := hfB _ (shiftedTarget_mem_rowTVBall F hr0 ymax ymin)
    rw [hf, sum_shiftedTarget] at h
    exact h
  set osc : Θ → ℝ := fun θ => w0 θ (ymax θ) - w0 θ (ymin θ) with hosc
  have hosc0 : ∀ θ, 0 ≤ osc θ := fun θ => sub_nonneg.mpr (hymin θ (ymax θ) (mem_univ _))
  set c := ∑ θ, osc θ with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun θ _ => hosc0 θ
  set w1 : Θ → Y → ℝ := fun θ y => w0 θ y - w0 θ (ymin θ) with hw1
  have hw10 : ∀ θ y, 0 ≤ w1 θ y := fun θ y => sub_nonneg.mpr (hymin θ y (mem_univ _))
  have hw1le : ∀ θ y, w1 θ y ≤ osc θ := fun θ y => sub_le_sub_right (hymax θ y (mem_univ _)) _
  have hkey : ∀ σ : X → Y,
      r * c < (∑ θ, ∑ y, w1 θ y * F θ y) - ∑ x, ∑ θ, E θ x * w1 θ (σ x) := by
    intro σ
    have h1 : ∑ θ, ∑ y, w1 θ y * F θ y =
        ∑ θ, ∑ y, F θ y * w0 θ y - ∑ θ, w0 θ (ymin θ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro θ _
      have : ∑ y, w1 θ y * F θ y = ∑ y, F θ y * w0 θ y - w0 θ (ymin θ) * ∑ y, F θ y := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y _
        simp only [w1]
        ring
      rw [this, (hF θ).2, mul_one]
    have h2 : ∑ x, ∑ θ, E θ x * w1 θ (σ x) =
        ∑ x, ∑ θ, E θ x * w0 θ (σ x) - ∑ θ, w0 θ (ymin θ) := by
      have : ∑ x, ∑ θ, E θ x * w1 θ (σ x) =
          ∑ x, ∑ θ, E θ x * w0 θ (σ x) - ∑ θ, (∑ x, E θ x) * w0 θ (ymin θ) := by
        rw [Finset.sum_comm (f := fun x θ => E θ x * w0 θ (σ x)),
          Finset.sum_comm (f := fun x θ => E θ x * w1 θ (σ x)), ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro θ _
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        simp only [w1]
        ring
      rw [this]
      congr 1
      apply Finset.sum_congr rfl
      intro θ _
      rw [(hE θ).2, one_mul]
    rw [h1, h2]
    have := hi σ
    linarith
  have hcpos : 0 < c := by
    rcases hc0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hosc_zero : ∀ θ, osc θ = 0 := fun θ =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun θ _ => hosc0 θ)).mp h.symm θ (mem_univ θ)
      have hw1zero : ∀ θ y, w1 θ y = 0 := fun θ y =>
        le_antisymm ((hw1le θ y).trans (hosc_zero θ).le) (hw10 θ y)
      have hk := hkey (fun _ => Classical.arbitrary Y)
      simp only [hw1zero, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, ← h] at hk
      exact lt_irrefl _ hk
  refine ⟨fun θ => osc θ / c, fun θ y => w1 θ y / c,
    ⟨fun θ => div_nonneg (hosc0 θ) hc0, by rw [← Finset.sum_div, div_self hcpos.ne']⟩,
    fun θ y => div_nonneg (hw10 θ y) hc0,
    fun θ y => div_le_div_of_nonneg_right (hw1le θ y) hc0, ?_⟩
  intro σ
  have hk := hkey σ
  have hrw : (∑ θ, ∑ y, w1 θ y / c * F θ y) - ∑ x, ∑ θ, E θ x * (w1 θ (σ x) / c) =
      ((∑ θ, ∑ y, w1 θ y * F θ y) - ∑ x, ∑ θ, E θ x * w1 θ (σ x)) / c := by
    rw [sub_div, Finset.sum_div, Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro θ _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      ring
    · apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro θ _
      ring
  rw [hrw, lt_div_iff₀ hcpos]
  exact hk

/-! ### Tightness of the paper's finite dual certificate

`finiteDualCertificateValue E F mu` (in `DualCertificate.lean`) is the paper's
displayed certificate `∑ x, min_y ∑ θ, mu θ y * E θ x - ∑ θ y, mu θ y * F θ y`
for weights `0 ≤ mu ≤ lambda`.  Under the substitution `mu = lam - w` it is
exactly the box-dual value of `(lam, w)` at the maximizing selection, so strong
duality makes the certificate tight. -/

/-- The paper's certificate value at `mu θ y = lam θ - w θ y` equals the
box-dual value of `(lam, w)` at any selection `σ` attaining the rowwise
minimum of `∑ θ, mu θ y * E θ x`. -/
theorem finiteDualCertificateValue_eq_boxDual [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (lam : Θ → ℝ) (hlam : IsDist lam) (w : Θ → Y → ℝ) (σ : X → Y)
    (hσ : ∀ x, Finset.univ.inf' Finset.univ_nonempty
      (fun y => ∑ θ, (lam θ - w θ y) * E θ x) = ∑ θ, (lam θ - w θ (σ x)) * E θ x) :
    finiteDualCertificateValue E F (fun θ y => lam θ - w θ y) =
      (∑ θ, ∑ y, w θ y * F θ y) - ∑ x, ∑ θ, E θ x * w θ (σ x) := by
  unfold finiteDualCertificateValue
  simp_rw [hσ]
  have h1 : ∑ x, ∑ θ, (lam θ - w θ (σ x)) * E θ x =
      1 - ∑ x, ∑ θ, E θ x * w θ (σ x) := by
    have : ∑ x, ∑ θ, (lam θ - w θ (σ x)) * E θ x =
        ∑ x, ∑ θ, lam θ * E θ x - ∑ x, ∑ θ, E θ x * w θ (σ x) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro θ _
      ring
    rw [this]
    congr 1
    rw [Finset.sum_comm]
    calc ∑ θ, ∑ x, lam θ * E θ x = ∑ θ, lam θ * ∑ x, E θ x := by
          apply Finset.sum_congr rfl
          intro θ _
          rw [Finset.mul_sum]
      _ = 1 := by
          rw [show (∑ θ, lam θ * ∑ x, E θ x) = ∑ θ, lam θ from
            Finset.sum_congr rfl fun θ _ => by rw [(hE θ).2, mul_one]]
          exact hlam.2
  have h2 : ∑ θ, ∑ y, (lam θ - w θ y) * F θ y =
      1 - ∑ θ, ∑ y, w θ y * F θ y := by
    have : ∑ θ, ∑ y, (lam θ - w θ y) * F θ y =
        ∑ θ, lam θ * ∑ y, F θ y - ∑ θ, ∑ y, w θ y * F θ y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro θ _
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [this]
    congr 1
    rw [show (∑ θ, lam θ * ∑ y, F θ y) = ∑ θ, lam θ from
      Finset.sum_congr rfl fun θ _ => by rw [(hF θ).2, mul_one]]
    exact hlam.2
  rw [h1, h2]
  ring

/-- **Tightness of the finite dual certificate.**  Every level strictly below
the deficiency is beaten by an admissible certificate of `DualCertificate.lean`. -/
theorem exists_finiteDualCertificateValue_gt_of_lt_finiteDeficiency
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    {r : ℝ} (hr : r < finiteDeficiency E F) :
    ∃ (lam : Θ → ℝ) (mu : Θ → Y → ℝ), IsDist lam ∧ (∀ θ y, 0 ≤ mu θ y) ∧
      (∀ θ y, mu θ y ≤ lam θ) ∧ r < finiteDualCertificateValue E F mu := by
  classical
  obtain ⟨lam, w, hlam, hw0, hwle, hval⟩ :=
    exists_boxDual_gt_of_lt_finiteDeficiency E F hE hF hr
  choose σ _ hσ using fun x =>
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
      (fun y => ∑ θ, (lam θ - w θ y) * E θ x)
  refine ⟨lam, fun θ y => lam θ - w θ y, hlam,
    fun θ y => sub_nonneg.mpr (hwle θ y),
    fun θ y => by linarith [hw0 θ y], ?_⟩
  rw [finiteDualCertificateValue_eq_boxDual E F hE hF lam hlam w σ hσ]
  exact hval σ

/-- The set of admissible values of the paper's finite dual certificate. -/
def finiteDualCertificateValues [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) : Set ℝ :=
  {c | ∃ (lam : Θ → ℝ) (mu : Θ → Y → ℝ), IsDist lam ∧ (∀ θ y, 0 ≤ mu θ y) ∧
    (∀ θ y, mu θ y ≤ lam θ) ∧ c = finiteDualCertificateValue E F mu}

/-- **Strong duality in supremum form.**  Finite directed deficiency equals the
supremum of admissible finite dual certificate values. -/
theorem finiteDeficiency_eq_sSup_finiteDualCertificateValue
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F = sSup (finiteDualCertificateValues E F) := by
  classical
  have hbdd : BddAbove (finiteDualCertificateValues E F) := by
    refine ⟨finiteDeficiency E F, ?_⟩
    rintro _ ⟨lam, mu, hlam, hmu0, hmule, rfl⟩
    exact finiteDualCertificateValue_le_finiteDeficiency E F hE hF lam hlam mu hmu0 hmule
  have hne : (finiteDualCertificateValues E F).Nonempty :=
    ⟨_, uniformPrior Θ, fun _ _ => 0, isDist_uniformPrior, fun _ _ => le_rfl,
      fun θ _ => (isDist_uniformPrior (Θ := Θ)).1 θ, rfl⟩
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨lam, mu, hlam, hmu0, hmule, hval⟩ :=
      exists_finiteDualCertificateValue_gt_of_lt_finiteDeficiency E F hE hF hlt
    have : finiteDualCertificateValue E F mu ≤ sSup (finiteDualCertificateValues E F) :=
      le_csSup hbdd ⟨lam, mu, hlam, hmu0, hmule, rfl⟩
    linarith
  · apply csSup_le hne
    rintro _ ⟨lam, mu, hlam, hmu0, hmule, rfl⟩
    exact finiteDualCertificateValue_le_finiteDeficiency E F hE hF lam hlam mu hmu0 hmule

end Duality


end IdExp
