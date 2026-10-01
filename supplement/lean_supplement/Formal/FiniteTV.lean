import Formal.FiniteBlackwell

/-!
# Finite total variation and approximate simulation

**Relevance:** direct current-paper support.  These lemmas supply the quantitative facts used by
the readiness, localization-obstruction, and unrestricted-class arguments: total variation obeys
the triangle inequality, contracts under stochastic post-processing, controls every `[0,1]`-valued
decision payoff with the sharp constant one, and yields the pairwise lower bound on decoder error.
-/

namespace IdExp

open Finset Set

variable {X Y Θ : Type*} [Fintype X] [Fintype Y]

/-- Total variation between two real vectors on a finite signal space. -/
noncomputable def finiteTV (p q : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |p x - q x|

theorem finiteTV_nonneg (p q : X → ℝ) : 0 ≤ finiteTV p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => abs_nonneg _)

theorem finiteTV_eq_zero_iff {X : Type*} [Fintype X] (p q : X → ℝ) :
    finiteTV p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hs : ∑ x, |p x - q x| = 0 := by
      unfold finiteTV at h
      linarith
    funext x
    have hx : |p x - q x| ≤ 0 := by
      rw [← hs]
      exact Finset.single_le_sum (fun y _ => abs_nonneg (p y - q y)) (mem_univ x)
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hx)
  · rintro rfl
    simp [finiteTV]

/-- Finite total variation is jointly continuous in both vectors. -/
theorem continuous_finiteTV {X : Type*} [Fintype X] :
    Continuous (fun p : (X → ℝ) × (X → ℝ) => finiteTV p.1 p.2) := by
  unfold finiteTV
  refine continuous_const.mul (continuous_finsetSum _ fun x _ => ?_)
  exact ((continuous_apply x).comp continuous_fst |>.sub
    ((continuous_apply x).comp continuous_snd)).abs

theorem finiteTV_symm (p q : X → ℝ) : finiteTV p q = finiteTV q p := by
  unfold finiteTV
  congr 2 with x
  rw [abs_sub_comm]

theorem finiteTV_triangle (p q r : X → ℝ) :
    finiteTV p r ≤ finiteTV p q + finiteTV q r := by
  unfold finiteTV
  rw [← mul_add, ← Finset.sum_add_distrib]
  gcongr with x
  exact abs_sub_le (p x) (q x) (r x)

/-- Total variation between two finite probability vectors is at most one. -/
theorem finiteTV_le_one_of_isDist (p q : X → ℝ)
    (hp : IsDist p) (hq : IsDist q) : finiteTV p q ≤ 1 := by
  unfold finiteTV
  calc
    (1 / 2 : ℝ) * ∑ x, |p x - q x| ≤
        (1 / 2 : ℝ) * ∑ x, (p x + q x) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by norm_num)
      exact abs_sub_le_iff.2 ⟨by linarith [hq.1 x], by linarith [hp.1 x]⟩
    _ = 1 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num


/-- Data processing for arbitrary finite vectors: applying the same stochastic
post-processing rule to both cannot increase total variation.  Probability-row
normalization of the input vectors is not needed. -/
theorem finiteTV_postprocess_le (p q : X → ℝ)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    finiteTV (fun y => ∑ x, p x * G x y)
        (fun y => ∑ x, q x * G x y) ≤ finiteTV p q := by
  unfold finiteTV
  have hdiff : ∀ y, (∑ x, p x * G x y) - (∑ x, q x * G x y) =
      ∑ x, (p x - q x) * G x y := by
    intro y
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hdiff]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc
    ∑ y, |∑ x, (p x - q x) * G x y| ≤
        ∑ y, ∑ x, |(p x - q x) * G x y| :=
      Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, ∑ x, |p x - q x| * G x y := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg ((hG x (Set.mem_univ x)).1 y)]
    _ = ∑ x, |p x - q x| * ∑ y, G x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = ∑ x, |p x - q x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [(hG x (Set.mem_univ x)).2, mul_one]

/-- Data processing: a stochastic matrix cannot increase total variation. -/
theorem finiteTV_decisionLaw_le (E : FiniteExperiment Θ X)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (θ θ' : Θ) :
    finiteTV (finiteDecisionLaw E G θ) (finiteDecisionLaw E G θ') ≤
      finiteTV (E θ) (E θ') := by
  unfold finiteTV finiteDecisionLaw
  have hdiff : ∀ y, (∑ x, E θ x * G x y) - (∑ x, E θ' x * G x y) =
      ∑ x, (E θ x - E θ' x) * G x y := by
    intro y
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hdiff]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc
    ∑ y, |∑ x, (E θ x - E θ' x) * G x y|
        ≤ ∑ y, ∑ x, |(E θ x - E θ' x) * G x y| :=
      Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, ∑ x, |E θ x - E θ' x| * G x y := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg ((hG x (Set.mem_univ x)).1 y)]
    _ = ∑ x, |E θ x - E θ' x| * ∑ y, G x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = ∑ x, |E θ x - E θ' x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [(hG x (Set.mem_univ x)).2, mul_one]

/-- If a single decoder approximates two target rows within `c`, its error is at least half the
target pair's separation advantage over the source pair.  This is the quantitative engine of the
paper's unrestricted-class obstruction. -/
theorem finiteTV_pairwise_decoder_lower (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (G : X → Y → ℝ)
    (hG : G ∈ stochasticRules X Y) (θ θ' : Θ) (c : ℝ)
    (hθ : finiteTV (finiteDecisionLaw E G θ) (F θ) ≤ c)
    (hθ' : finiteTV (finiteDecisionLaw E G θ') (F θ') ≤ c) :
    (finiteTV (F θ) (F θ') - finiteTV (E θ) (E θ')) / 2 ≤ c := by
  have hmiddle := finiteTV_decisionLaw_le E G hG θ θ'
  have hfirst := finiteTV_triangle (F θ) (finiteDecisionLaw E G θ) (F θ')
  have hsecond := finiteTV_triangle (finiteDecisionLaw E G θ)
    (finiteDecisionLaw E G θ') (F θ')
  rw [finiteTV_symm (F θ) (finiteDecisionLaw E G θ)] at hfirst
  nlinarith

theorem sum_posPart_eq_finiteTV (p q : X → ℝ)
    (hsum : ∑ x, p x = ∑ x, q x) :
    ∑ x, max (p x - q x) 0 = finiteTV p q := by
  have hzero : ∑ x, (p x - q x) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hpoint : ∀ x, |p x - q x| = 2 * max (p x - q x) 0 - (p x - q x) := by
    intro x
    by_cases h : 0 ≤ p x - q x
    · rw [abs_of_nonneg h, max_eq_left h]
      ring
    · have hn : p x - q x ≤ 0 := le_of_not_ge h
      rw [abs_of_nonpos hn, max_eq_right hn]
      ring
  unfold finiteTV
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, sub_zero]
  ring

/-- A single event has the sharp TV bound for equal-mass real vectors. -/
theorem finiteTV_coord_sub_le (p q : X → ℝ)
    (hsum : ∑ x, p x = ∑ x, q x) (x : X) :
    p x - q x ≤ finiteTV p q := by
  calc
    p x - q x ≤ max (p x - q x) 0 := le_max_left _ _
    _ ≤ ∑ y, max (p y - q y) 0 :=
      Finset.single_le_sum (fun y _ => le_max_right (p y - q y) 0) (Finset.mem_univ x)
    _ = finiteTV p q := sum_posPart_eq_finiteTV p q hsum

/-- Both signs of the singleton-event bound, without positivity assumptions. -/
theorem finiteTV_coord_abs_le (p q : X → ℝ)
    (hsum : ∑ x, p x = ∑ x, q x) (x : X) :
    |p x - q x| ≤ finiteTV p q := by
  apply abs_sub_le_iff.2
  constructor
  · exact finiteTV_coord_sub_le p q hsum x
  · simpa only [finiteTV_symm] using finiteTV_coord_sub_le q p hsum.symm x

/-- Sharp bounded-payoff consequence of total variation. -/
theorem expectation_sub_le_finiteTV (p q u : X → ℝ)
    (hsum : ∑ x, p x = ∑ x, q x)
    (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1) :
    (∑ x, p x * u x) - ∑ x, q x * u x ≤ finiteTV p q := by
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ x, p x * u x - q x * u x ≤ max (p x - q x) 0 := by
    intro x
    rw [← sub_mul]
    by_cases h : 0 ≤ p x - q x
    · rw [max_eq_left h]
      exact mul_le_of_le_one_right h (hu1 x)
    · have hn : p x - q x ≤ 0 := le_of_not_ge h
      rw [max_eq_right hn]
      exact mul_nonpos_of_nonpos_of_nonneg hn (hu0 x)
  calc
    ∑ x, (p x * u x - q x * u x) ≤ ∑ x, max (p x - q x) 0 :=
      Finset.sum_le_sum fun x _ => hterm x
    _ = finiteTV p q := sum_posPart_eq_finiteTV p q hsum

/-- Total variation at a common affine interpolation of two pairs of rows is
bounded by the worse endpoint distance.  This is the machine-checked
norm-convexity core of the paper's effective-binary frontier reduction. -/
theorem finiteTV_affine_le_max (p₀ p₁ q₀ q₁ : X → ℝ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    finiteTV
        (fun x => (1 - lam) * p₀ x + lam * p₁ x)
        (fun x => (1 - lam) * q₀ x + lam * q₁ x)
      ≤ max (finiteTV p₀ q₀) (finiteTV p₁ q₁) := by
  have hcomp : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  have hweighted :
      finiteTV
          (fun x => (1 - lam) * p₀ x + lam * p₁ x)
          (fun x => (1 - lam) * q₀ x + lam * q₁ x)
        ≤ (1 - lam) * finiteTV p₀ q₀ + lam * finiteTV p₁ q₁ := by
    unfold finiteTV
    calc
      (1 / 2 : ℝ) *
          ∑ x, |((1 - lam) * p₀ x + lam * p₁ x) -
            ((1 - lam) * q₀ x + lam * q₁ x)| ≤
          (1 / 2 : ℝ) *
            ∑ x, ((1 - lam) * |p₀ x - q₀ x| + lam * |p₁ x - q₁ x|) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by norm_num)
        calc
          |((1 - lam) * p₀ x + lam * p₁ x) -
              ((1 - lam) * q₀ x + lam * q₁ x)| =
              |(1 - lam) * (p₀ x - q₀ x) + lam * (p₁ x - q₁ x)| := by
                congr 1
                ring
          _ ≤ |(1 - lam) * (p₀ x - q₀ x)| +
                |lam * (p₁ x - q₁ x)| := abs_add_le _ _
          _ = (1 - lam) * |p₀ x - q₀ x| +
                lam * |p₁ x - q₁ x| := by
                rw [abs_mul, abs_of_nonneg hcomp, abs_mul, abs_of_nonneg hlam0]
      _ = (1 - lam) * ((1 / 2 : ℝ) * ∑ x, |p₀ x - q₀ x|) +
            lam * ((1 / 2 : ℝ) * ∑ x, |p₁ x - q₁ x|) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
  calc
    finiteTV
        (fun x => (1 - lam) * p₀ x + lam * p₁ x)
        (fun x => (1 - lam) * q₀ x + lam * q₁ x)
      ≤ (1 - lam) * finiteTV p₀ q₀ + lam * finiteTV p₁ q₁ := hweighted
    _ ≤ (1 - lam) * max (finiteTV p₀ q₀) (finiteTV p₁ q₁) +
          lam * max (finiteTV p₀ q₀) (finiteTV p₁ q₁) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hcomp)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hlam0)
    _ = max (finiteTV p₀ q₀) (finiteTV p₁ q₁) := by ring

/-- Distinct point masses have full total-variation separation, on any
finite alphabet (also useful for observation words). -/
theorem finiteTV_pointMass_eq_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (y0 y1 : Y) (hne : y0 ≠ y1) :
    finiteTV (fun y => if y = y0 then 1 else 0)
      (fun y => if y = y1 then 1 else 0) = 1 := by
  have hpoint : ∀ y : Y,
      |(if y = y0 then (1 : ℝ) else 0) - (if y = y1 then 1 else 0)| =
        (if y = y0 then 1 else 0) + (if y = y1 then 1 else 0) := by
    intro y
    by_cases h0 : y = y0 <;> by_cases h1 : y = y1 <;>
      simp_all
  norm_num [finiteTV, hpoint, Finset.sum_add_distrib]

end IdExp
