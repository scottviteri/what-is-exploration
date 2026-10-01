import Formal.CountEntropyProcess

/-!
# A literal tabular pseudo-count objective with a dominated process optimum

The density model is the categorical posterior predictive distribution with
one initial count for each of four labels. Updating increments the observed
label. The Bellemare pseudo-count expression is evaluated on that actual
before/after model. A bonus 1/sqrt(pseudo-count) is summed for two observations.
Every randomized history-policy optimum selects the permanently independent
noise branch and is strictly finitarily dominated by READ.
-/
namespace IdExp.FirstVisitCount
open Finset
noncomputable section

def countDensity (xs : List Observation) (o : Observation) : ℝ :=
  ((xs.count o : ℝ) + 1) / (xs.length + 4)

theorem count_sum (xs : List Observation) :
    (∑ o : Observation, (xs.count o : ℝ)) = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    simp only [Nat.cast_ite, Nat.cast_one]
    simp only [Finset.sum_add_distrib, ih]
    simp

theorem countDensity_valid (xs : List Observation) : IsDist (countDensity xs) := by
  constructor
  · intro o
    unfold countDensity
    positivity
  · simp only [countDensity, ← Finset.sum_div, Finset.sum_add_distrib, count_sum]
    norm_num
    have h : (xs.length : ℝ) + 4 ≠ 0 := by positivity
    exact h

def updatedCountDensity (xs : List Observation) (o : Observation) : ℝ :=
  countDensity (xs ++ [o]) o

def modelPseudoCount (xs : List Observation) (o : Observation) : ℝ :=
  countDensity xs o * (1 - updatedCountDensity xs o) /
    (updatedCountDensity xs o - countDensity xs o)

theorem modelPseudoCount_empty (o : Observation) : modelPseudoCount [] o = 1 := by
  norm_num [modelPseudoCount, countDensity, updatedCountDensity]

theorem modelPseudoCount_single (o o' : Observation) :
    modelPseudoCount [o] o' = if o = o' then 2 else 1 := by
  by_cases h : o = o'
  · subst o'
    norm_num [modelPseudoCount, countDensity, updatedCountDensity]
  · have h' : o' ≠ o := Ne.symm h
    norm_num [modelPseudoCount, countDensity, updatedCountDensity, h, h']

def pseudoCountReward (w : CausalFiniteTrace Action Observation 2) : ℝ :=
  1 / Real.sqrt (modelPseudoCount [] (w 0).2) +
    1 / Real.sqrt (modelPseudoCount [(w 0).2] (w 1).2)

theorem pseudoCountReward_eq (w : CausalFiniteTrace Action Observation 2) :
    pseudoCountReward w = 2 / Real.sqrt 2 + (1 - 1 / Real.sqrt 2) * countReward w := by
  unfold pseudoCountReward
  rw [modelPseudoCount_empty, modelPseudoCount_single]
  by_cases h : (w 0).2 = (w 1).2 <;>
    simp only [countReward, h, if_true, if_false, Real.sqrt_one, div_one] <;> ring

def expectedPseudoCount (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑ θ, prior θ * ∑ w, causalFiniteExperiment π.1 response 2 θ w * pseudoCountReward w

theorem expectedPseudoCount_eq (π : ValidCausalPolicy Action Observation) :
    expectedPseudoCount π = 2 / Real.sqrt 2 + (1 - 1 / Real.sqrt 2) * expectedCount π := by
  have hrow (θ : World) :
      (∑ w, causalFiniteExperiment π.1 response 2 θ w * pseudoCountReward w) =
      2 / Real.sqrt 2 + (1 - 1 / Real.sqrt 2) *
        ∑ w, causalFiniteExperiment π.1 response 2 θ w * countReward w := by
    simp only [pseudoCountReward_eq, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, (causalFiniteExperiment_valid π.1 π.2 response response_valid 2 θ).2]
    simp only [one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  unfold expectedPseudoCount expectedCount
  simp only [hrow, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, KnownNoise.prior_valid.2]
  simp only [one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  ring

theorem pseudoCount_maximizers (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      expectedPseudoCount ρ ≤ expectedPseudoCount π) ↔ π.1 [] 0 = 0 := by
  have hs : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hc : 0 < 1 - 1 / Real.sqrt 2 := by
    have hi : 1 / Real.sqrt 2 < 1 := (div_lt_one (by positivity)).mpr hs
    linarith
  rw [← count_maximizers π]
  simp only [expectedPseudoCount_eq, add_le_add_iff_left, mul_le_mul_iff_right₀ hc]

theorem every_pseudoCount_optimum_strictly_finitarily_dominated
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation,
      expectedPseudoCount ρ ≤ expectedPseudoCount π) :
    CausalFinitaryDominates response (purePolicy 0) π ∧
      ¬ CausalFinitaryDominates response π (purePolicy 0) :=
  noise_root_strictly_dominated π ((pseudoCount_maximizers π).mp hopt)

theorem pseudoCount_dominated_maximizer :
    (∀ ρ : ValidCausalPolicy Action Observation,
      expectedPseudoCount ρ ≤ expectedPseudoCount (purePolicy 1)) ∧
    CausalFinitaryDominates response (purePolicy 0) (purePolicy 1) ∧
      ¬ CausalFinitaryDominates response (purePolicy 1) (purePolicy 0) := by
  have h : (purePolicy 1).1 [] 0 = 0 := by simp [purePolicy, KnownNoise.purePolicy, detPolicy]
  exact ⟨(pseudoCount_maximizers _).mpr h, noise_root_strictly_dominated _ h⟩

end
end IdExp.FirstVisitCount
