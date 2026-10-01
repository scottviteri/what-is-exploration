import Formal.RecordedMixtureScores

/-!
# Squared posterior movement as a bounded forecasting task

The paper's "posterior rewards express particular decision preferences"
paragraph.  On a finite world class, report a probability vector `q` and
receive the bounded utility `u(θ, q) = (1 + 2 q_θ − ‖q‖²)/2 ∈ [0, 1]`.  At
posterior `p` the expected utility is `(1 + ‖p‖² − ‖p − q‖²)/2`, uniquely
maximized by reporting `q = p`.  With the finite decision set consisting of
the prior and the possible posteriors of an experiment, its optimized Bayes
value is `(1 + Σ_x m_x ‖π_x‖²)/2`, so the squared-posterior objective equals
twice the improvement over the no-data value: it lies literally inside the
bounded decision envelope, and every decision-envelope theorem applies to it.
-/

namespace IdExp

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

/-- The quadratic scoring rule: report `q`, receive `(1 + 2 q_θ − ‖q‖²)/2`. -/
def quadraticReport (q : Θ → ℝ) (θ : Θ) : ℝ :=
  (1 + 2 * q θ - posteriorQuadraticPotential q) / 2

theorem posteriorQuadraticPotential_le_one {q : Θ → ℝ} (hq : IsDist q) :
    posteriorQuadraticPotential q ≤ 1 := by
  unfold posteriorQuadraticPotential
  calc ∑ θ, (q θ)^2 ≤ ∑ θ, q θ := by
        apply Finset.sum_le_sum
        intro θ _
        have h0 := hq.1 θ
        have h1 : q θ ≤ 1 := by
          have := Finset.single_le_sum (fun c _ => hq.1 c) (Finset.mem_univ θ)
          linarith [hq.2]
        nlinarith
    _ = 1 := hq.2

/-- The report utility is unit-range on the simplex. -/
theorem quadraticReport_mem_unitInterval {q : Θ → ℝ} (hq : IsDist q) (θ : Θ) :
    quadraticReport q θ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold quadraticReport
  have hle := posteriorQuadraticPotential_le_one hq
  have h0 := hq.1 θ
  have hsq : (q θ)^2 ≤ posteriorQuadraticPotential q :=
    Finset.single_le_sum (fun c _ => sq_nonneg (q c)) (Finset.mem_univ θ)
  constructor
  · linarith
  · nlinarith

/-- Expected report utility under a probability vector `p`:
`(1 + ‖p‖² − ‖p − q‖²)/2`. -/
theorem expected_quadraticReport {p : Θ → ℝ} (hp : IsDist p) (q : Θ → ℝ) :
    ∑ θ, p θ * quadraticReport q θ =
      (1 + posteriorQuadraticPotential p - posteriorQuadraticPotential (p - q)) / 2 := by
  unfold quadraticReport posteriorQuadraticPotential
  have h1 : ∑ θ, p θ * ((1 + 2 * q θ - ∑ c, (q c)^2) / 2) =
      (∑ θ, p θ) / 2 + ∑ θ, p θ * q θ - (∑ θ, p θ) * (∑ c, (q c)^2) / 2 := by
    simp only [Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [h1, hp.2]
  simp only [Pi.sub_apply]
  have h2 : ∑ θ, (p θ - q θ)^2 = ∑ θ, (p θ)^2 - 2 * ∑ θ, p θ * q θ + ∑ θ, (q θ)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [h2]
  ring

/-- The report decisions: the prior, or the posterior at a signal. -/
def reportVector (α : Θ → ℝ) (E : FiniteExperiment Θ X) : Option X → Θ → ℝ
  | none => α
  | some x => finiteBayesPosterior α E x

/-- The report utility as a decision problem with decisions `Option X`. -/
def reportUtility (α : Θ → ℝ) (E : FiniteExperiment Θ X) (θ : Θ) (d : Option X) : ℝ :=
  quadraticReport (reportVector α E d) θ

theorem reportUtility_mem_unitInterval (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (θ : Θ) (d : Option X) :
    reportUtility α E θ d ∈ Set.Icc (0 : ℝ) 1 := by
  unfold reportUtility
  cases d with
  | none => exact quadraticReport_mem_unitInterval hα θ
  | some x =>
    by_cases hx : finiteBayesMass α E x = 0
    · have hz : finiteBayesPosterior α E x = fun _ => 0 := by
        funext θ'
        unfold finiteBayesPosterior
        have : (∑ c, α c * E c x) = 0 := hx
        rw [this, div_zero]
      show quadraticReport (finiteBayesPosterior α E x) θ ∈ Set.Icc (0 : ℝ) 1
      rw [hz]
      unfold quadraticReport posteriorQuadraticPotential
      norm_num
    · exact quadraticReport_mem_unitInterval
        (finiteBayesPosterior_mem_simplex α E hα.1 (fun θ x => (hE θ).1 x) x hx) θ

/-- The score at signal `x` of reporting `q` is the mass times the expected
report utility under the posterior. -/
theorem finiteDecisionScore_reportUtility (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (x : X) (d : Option X) :
    finiteDecisionScore E α (reportUtility α E) x d =
      finiteBayesMass α E x *
        ∑ θ, finiteBayesPosterior α E x θ * quadraticReport (reportVector α E d) θ := by
  unfold finiteDecisionScore reportUtility
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  have h := finiteBayesPosterior_mul_mass α E hα.1 (fun θ x => (hE θ).1 x) x θ
  have hm : finiteBayesMass α E x = ∑ c, α c * E c x := rfl
  rw [hm, ← h]
  ring

/-- **The optimized report value is `(1 + Σ_x m_x‖π_x‖²)/2`.** -/
theorem finiteBayesValue_reportUtility (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    finiteBayesValue E α (reportUtility α E) =
      (1 + finiteBayesPotential posteriorQuadraticPotential α E) / 2 := by
  unfold finiteBayesValue
  have hterm : ∀ x, Finset.univ.sup' Finset.univ_nonempty
      (finiteDecisionScore E α (reportUtility α E) x) =
      finiteBayesMass α E x * (1 + posteriorQuadraticPotential (finiteBayesPosterior α E x)) / 2 := by
    intro x
    by_cases hx : finiteBayesMass α E x = 0
    · rw [hx, zero_mul, zero_div]
      apply le_antisymm
      · apply Finset.sup'_le
        intro d _
        rw [finiteDecisionScore_reportUtility α hα E hE, hx, zero_mul]
      · refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (some x)))
        rw [finiteDecisionScore_reportUtility α hα E hE, hx, zero_mul]
    · have hpost := finiteBayesPosterior_mem_simplex α E hα.1 (fun θ x => (hE θ).1 x) x hx
      have hm0 := finiteBayesMass_nonneg α E hα.1 (fun θ x => (hE θ).1 x) x
      apply le_antisymm
      · apply Finset.sup'_le
        intro d _
        rw [finiteDecisionScore_reportUtility α hα E hE, expected_quadraticReport hpost]
        have hq : 0 ≤ posteriorQuadraticPotential (finiteBayesPosterior α E x - reportVector α E d) :=
          Finset.sum_nonneg fun θ _ => sq_nonneg _
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hm0
        linarith
      · refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (some x)))
        rw [finiteDecisionScore_reportUtility α hα E hE, expected_quadraticReport hpost]
        simp only [reportVector, sub_self]
        have : posteriorQuadraticPotential (0 : Θ → ℝ) = 0 := by
          simp [posteriorQuadraticPotential]
        rw [this, sub_zero, mul_div_assoc]
  simp_rw [hterm]
  unfold finiteBayesPotential
  have hmass : ∑ x, finiteBayesMass α E x = 1 := (finiteBayesMass_isDist α hα E hE).2
  calc ∑ x, finiteBayesMass α E x *
        (1 + posteriorQuadraticPotential (finiteBayesPosterior α E x)) / 2
      = (∑ x, finiteBayesMass α E x +
          ∑ x, finiteBayesMass α E x * posteriorQuadraticPotential (finiteBayesPosterior α E x)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = _ := by rw [hmass]

/-- The no-data experiment: one signal, always observed. -/
def trivialExperiment (Θ : Type*) : FiniteExperiment Θ Unit := fun _ _ => 1

theorem trivialExperiment_valid : IsFiniteExperiment (trivialExperiment Θ) := fun _ =>
  ⟨fun _ => zero_le_one, by simp [trivialExperiment]⟩

theorem finiteBayesPotential_trivialExperiment (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (hα : IsDist α) :
    finiteBayesPotential Φ α (trivialExperiment Θ) = Φ α := by
  unfold finiteBayesPotential finiteBayesMass finiteBayesPosterior trivialExperiment
  simp [hα.2]

/-- **Squared posterior movement is twice the improvement in the quadratic
forecasting task over the no-data value.** -/
theorem quadraticPosteriorScore_eq_twice_improvement (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    quadraticPosteriorScore α E =
      2 * (finiteBayesValue E α (reportUtility α E) -
        finiteBayesValue (trivialExperiment Θ) α (reportUtility α (trivialExperiment Θ))) := by
  rw [finiteBayesValue_reportUtility α hα E hE,
    finiteBayesValue_reportUtility α hα (trivialExperiment Θ) trivialExperiment_valid,
    finiteBayesPotential_trivialExperiment _ α hα]
  unfold quadraticPosteriorScore
  ring

end

end IdExp
