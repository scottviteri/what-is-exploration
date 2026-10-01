import Formal.FiniteBayesInformation
import Formal.QuadraticPosterior
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Two strict posterior scores can rank incomparable measurements differently

The paper's crossing-partition example: on worlds `00, 01, 10, 11` with prior
`(3/10, 1/2, 1/10, 1/10)`, measurement `A` reveals whether the world is `00`
and measurement `B` reveals the second bit.  These deterministic partitions
are Blackwell-incomparable.  Information gain prefers `B`, since
`h₂(3/10) < h₂(2/5)`; expected squared posterior movement prefers `A`,
since `57/175 > 97/300`.  Both objectives are strictly Blackwell-monotone
posterior potentials; they differ on this incomparable pair.

The information values use a reusable identity: the finite Bayesian
information of a deterministic partition is the entropy of the partition's
prior law.  The same identity gives the two-bit prior-reversal example: with
independent bits of parameters `p, q`, reading the first bit has information
`h₂ p` and reading the second `h₂ q`, so swapping `(p, q) = (1/2, 1/10)`
reverses the preference.

Prior regions are recorded abstractly: for scores continuous in the prior,
the strict-preference region is open and the tie region is closed.
-/

namespace IdExp

open Finset Set Real

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Information of a deterministic partition -/

section Deterministic

variable {Θ S : Type*} [Fintype Θ] [Fintype S] [DecidableEq S]

/-- The deterministic experiment reporting `f θ`. -/
def deterministicExperiment (f : Θ → S) : FiniteExperiment Θ S :=
  fun θ s => if f θ = s then 1 else 0

/-- The prior law of the reported value. -/
def pushforwardDist (α : Θ → ℝ) (f : Θ → S) : S → ℝ :=
  fun s => ∑ θ, if f θ = s then α θ else 0

theorem finiteBayesMass_deterministic (α : Θ → ℝ) (f : Θ → S) (s : S) :
    finiteBayesMass α (deterministicExperiment f) s = pushforwardDist α f s := by
  simp [finiteBayesMass, deterministicExperiment, pushforwardDist, mul_ite]

theorem finiteBayesPosterior_deterministic (α : Θ → ℝ) (f : Θ → S) (s : S) (θ : Θ) :
    finiteBayesPosterior α (deterministicExperiment f) s θ =
      (if f θ = s then α θ else 0) / pushforwardDist α f s := by
  rw [finiteBayesPosterior, ← finiteBayesMass, finiteBayesMass_deterministic]
  simp [deterministicExperiment, mul_ite]

theorem pushforwardDist_nonneg (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ) (f : Θ → S) (s : S) :
    0 ≤ pushforwardDist α f s :=
  Finset.sum_nonneg fun θ _ => by split_ifs <;> simp [hα θ]

/-- Mass times posterior entropy of one deterministic signal, in closed form. -/
theorem mass_mul_ent_posterior_deterministic (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ)
    (f : Θ → S) (s : S) :
    pushforwardDist α f s * ent (finiteBayesPosterior α (deterministicExperiment f) s) =
      (∑ θ, if f θ = s then negMulLog (α θ) else 0) - negMulLog (pushforwardDist α f s) := by
  classical
  set m := pushforwardDist α f s with hm
  have hpost : ∀ θ, finiteBayesPosterior α (deterministicExperiment f) s θ =
      (if f θ = s then α θ else 0) / m :=
    fun θ => finiteBayesPosterior_deterministic α f s θ
  rcases eq_or_lt_of_le (pushforwardDist_nonneg α hα f s) with h0 | hpos
  · -- zero mass: every world in the fiber has prior zero
    have hm0 : m = 0 := by rw [hm]; exact h0.symm
    have hzero : ∀ θ, f θ = s → α θ = 0 := by
      intro θ hθ
      have hsum : (∑ θ, if f θ = s then α θ else 0) = 0 := by
        change pushforwardDist α f s = 0
        exact h0.symm
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun θ _ => by split_ifs <;> simp [hα θ])).1 hsum θ (Finset.mem_univ θ)
      simpa [hθ] using this
    rw [hm0, zero_mul]
    have : (∑ θ, if f θ = s then negMulLog (α θ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro θ _
      split_ifs with hθ
      · rw [hzero θ hθ, negMulLog_zero]
      · rfl
    rw [this, negMulLog_zero, sub_zero]
  · -- positive mass
    have hmne : m ≠ 0 := hpos.ne'
    unfold ent
    rw [Finset.mul_sum]
    have key : ∀ a : ℝ, m * negMulLog (a / m) = negMulLog a + a * Real.log m := by
      intro a
      by_cases ha : a = 0
      · simp [ha]
      · simp only [negMulLog]
        rw [Real.log_div ha hmne]
        field_simp
        ring
    have hterm : ∀ θ, m * negMulLog (finiteBayesPosterior α (deterministicExperiment f) s θ) =
        (if f θ = s then negMulLog (α θ) + α θ * Real.log m else 0) := by
      intro θ
      rw [hpost θ]
      split_ifs with hθ
      · exact key (α θ)
      · simp
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    have hfiber : (∑ θ ∈ Finset.univ.filter (fun θ => f θ = s), α θ) = m := by
      rw [hm, pushforwardDist, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfiber' : (∑ θ ∈ Finset.univ.filter (fun θ => f θ = s), negMulLog (α θ)) =
        ∑ θ, if f θ = s then negMulLog (α θ) else 0 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [hfiber, hfiber', negMulLog]
    ring

/-- **Information of a deterministic partition is the entropy of its law.** -/
theorem finiteBayesInformation_deterministic (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ) (f : Θ → S) :
    finiteBayesInformation α (deterministicExperiment f) = ent (pushforwardDist α f) := by
  classical
  unfold finiteBayesInformation finiteBayesPotential
  simp_rw [finiteBayesMass_deterministic, mass_mul_ent_posterior_deterministic α hα f]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have hcollapse : (∑ θ, ∑ s, if f θ = s then negMulLog (α θ) else 0) = ent α := by
    unfold ent
    apply Finset.sum_congr rfl
    intro θ _
    rw [Finset.sum_ite_eq]
    simp
  rw [hcollapse]
  unfold ent
  ring

end Deterministic

/-! ## The squared-posterior-movement score -/

section Quadratic

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

/-- Expected squared posterior movement: the quadratic posterior potential
after the signal, minus the potential at the prior. -/
def quadraticPosteriorScore (α : Θ → ℝ) (E : FiniteExperiment Θ X) : ℝ :=
  finiteBayesPotential posteriorQuadraticPotential α E - posteriorQuadraticPotential α

end Quadratic

/-! ## The crossing-partition example -/

section Example

/-- Prior `(3/10, 1/2, 1/10, 1/10)` on the worlds `00, 01, 10, 11`. -/
def crossingPrior : Fin 4 → ℝ := ![3/10, 1/2, 1/10, 1/10]

theorem crossingPrior_isDist : IsDist crossingPrior := by
  refine ⟨fun θ => ?_, ?_⟩
  · fin_cases θ <;> norm_num [crossingPrior]
  · simp [crossingPrior, Fin.sum_univ_succ]; norm_num

/-- Measurement `A`: is the world `00`? -/
def crossingA : Fin 4 → Fin 2 := ![0, 1, 1, 1]

/-- Measurement `B`: the second bit. -/
def crossingB : Fin 4 → Fin 2 := ![0, 1, 0, 1]

theorem pushforward_crossingA :
    pushforwardDist crossingPrior crossingA = ![3/10, 7/10] := by
  funext s
  fin_cases s <;> simp [pushforwardDist, crossingPrior, crossingA, Fin.sum_univ_succ] <;> norm_num

theorem pushforward_crossingB :
    pushforwardDist crossingPrior crossingB = ![2/5, 3/5] := by
  funext s
  fin_cases s <;> simp [pushforwardDist, crossingPrior, crossingB, Fin.sum_univ_succ] <;> norm_num

/-- Information gain of `A` is the binary entropy at `3/10`. -/
theorem information_crossingA :
    finiteBayesInformation crossingPrior (deterministicExperiment crossingA) =
      binEntropy (3/10) := by
  rw [finiteBayesInformation_deterministic _ crossingPrior_isDist.1, pushforward_crossingA,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [ent, Fin.sum_univ_succ]; norm_num

/-- Information gain of `B` is the binary entropy at `2/5`. -/
theorem information_crossingB :
    finiteBayesInformation crossingPrior (deterministicExperiment crossingB) =
      binEntropy (2/5) := by
  rw [finiteBayesInformation_deterministic _ crossingPrior_isDist.1, pushforward_crossingB,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [ent, Fin.sum_univ_succ]; norm_num

/-- **Information gain prefers `B`.** -/
theorem information_prefers_crossingB :
    finiteBayesInformation crossingPrior (deterministicExperiment crossingA) <
      finiteBayesInformation crossingPrior (deterministicExperiment crossingB) := by
  rw [information_crossingA, information_crossingB]
  exact binEntropy_strictMonoOn (by norm_num) (by norm_num) (by norm_num)

/-- Squared posterior movement of `A` is `57/175`. -/
theorem quadratic_crossingA :
    quadraticPosteriorScore crossingPrior (deterministicExperiment crossingA) = 57/175 := by
  simp [quadraticPosteriorScore, finiteBayesPotential, posteriorQuadraticPotential,
    finiteBayesPosterior, finiteBayesMass, deterministicExperiment, crossingPrior, crossingA,
    Fin.sum_univ_succ]
  norm_num

/-- Squared posterior movement of `B` is `97/300`. -/
theorem quadratic_crossingB :
    quadraticPosteriorScore crossingPrior (deterministicExperiment crossingB) = 97/300 := by
  simp [quadraticPosteriorScore, finiteBayesPotential, posteriorQuadraticPotential,
    finiteBayesPosterior, finiteBayesMass, deterministicExperiment, crossingPrior, crossingB,
    Fin.sum_univ_succ]
  norm_num

/-- **Squared posterior movement prefers `A`.** -/
theorem quadratic_prefers_crossingA :
    quadraticPosteriorScore crossingPrior (deterministicExperiment crossingB) <
      quadraticPosteriorScore crossingPrior (deterministicExperiment crossingA) := by
  rw [quadratic_crossingA, quadratic_crossingB]
  norm_num

/-- The two strict posterior scores disagree on the incomparable pair. -/
theorem crossing_scores_disagree :
    finiteBayesInformation crossingPrior (deterministicExperiment crossingA) <
        finiteBayesInformation crossingPrior (deterministicExperiment crossingB) ∧
      quadraticPosteriorScore crossingPrior (deterministicExperiment crossingB) <
        quadraticPosteriorScore crossingPrior (deterministicExperiment crossingA) :=
  ⟨information_prefers_crossingB, quadratic_prefers_crossingA⟩

end Example

/-! ## Prior reversal for two independent bits -/

section TwoBits

/-- Independent bits `U ~ Ber p`, `V ~ Ber q` on the worlds `Fin 2 × Fin 2`. -/
def productBitPrior (p q : ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun w => (if w.1 = 1 then p else 1 - p) * (if w.2 = 1 then q else 1 - q)

/-- Reading the first bit. -/
def readFirstBit : Fin 2 × Fin 2 → Fin 2 := Prod.fst

/-- Reading the second bit. -/
def readSecondBit : Fin 2 × Fin 2 → Fin 2 := Prod.snd

theorem productBitPrior_nonneg {p q : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (w : Fin 2 × Fin 2) : 0 ≤ productBitPrior p q w := by
  unfold productBitPrior
  apply mul_nonneg <;> split_ifs <;> linarith [hp.1, hp.2, hq.1, hq.2]

theorem pushforward_readFirstBit (p q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    pushforwardDist (productBitPrior p q) readFirstBit = ![1 - p, p] := by
  funext s
  fin_cases s <;>
    simp [pushforwardDist, productBitPrior, readFirstBit, Fintype.sum_prod_type,
      Fin.sum_univ_two] <;> ring

theorem pushforward_readSecondBit (p q : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    pushforwardDist (productBitPrior p q) readSecondBit = ![1 - q, q] := by
  funext s
  fin_cases s <;>
    simp [pushforwardDist, productBitPrior, readSecondBit, Fintype.sum_prod_type,
      Fin.sum_univ_two] <;> ring

/-- Information from reading the first bit is `h₂ p`. -/
theorem information_readFirstBit {p q : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) :
    finiteBayesInformation (productBitPrior p q) (deterministicExperiment readFirstBit) =
      binEntropy p := by
  rw [finiteBayesInformation_deterministic _ (productBitPrior_nonneg hp hq),
    pushforward_readFirstBit p q hq, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [ent, Fin.sum_univ_two, add_comm]

/-- Information from reading the second bit is `h₂ q`. -/
theorem information_readSecondBit {p q : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hq : q ∈ Set.Icc (0:ℝ) 1) :
    finiteBayesInformation (productBitPrior p q) (deterministicExperiment readSecondBit) =
      binEntropy q := by
  rw [finiteBayesInformation_deterministic _ (productBitPrior_nonneg hp hq),
    pushforward_readSecondBit p q hp, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [ent, Fin.sum_univ_two, add_comm]

/-- **Prior reversal.**  At `(p, q) = (1/2, 1/10)` information gain prefers
the first bit; at `(1/10, 1/2)` it prefers the second. -/
theorem information_prior_reversal :
    finiteBayesInformation (productBitPrior (1/2) (1/10))
        (deterministicExperiment readSecondBit) <
      finiteBayesInformation (productBitPrior (1/2) (1/10))
        (deterministicExperiment readFirstBit) ∧
    finiteBayesInformation (productBitPrior (1/10) (1/2))
        (deterministicExperiment readFirstBit) <
      finiteBayesInformation (productBitPrior (1/10) (1/2))
        (deterministicExperiment readSecondBit) := by
  have h1 : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have h2 : (1/10 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have hlt : binEntropy (1/10) < binEntropy (1/2) :=
    binEntropy_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  constructor
  · rw [information_readSecondBit h1 h2, information_readFirstBit h1 h2]; exact hlt
  · rw [information_readFirstBit h2 h1, information_readSecondBit h2 h1]; exact hlt

end TwoBits

/-! ## Prior regions -/

section Regions

variable {Ω : Type*} [TopologicalSpace Ω]

/-- For scores continuous in the prior, the strict-preference region is open. -/
theorem strictPreferenceRegion_isOpen (JE JF : Ω → ℝ) (hE : Continuous JE)
    (hF : Continuous JF) : IsOpen {α | JF α < JE α} :=
  isOpen_lt hF hE

/-- For scores continuous in the prior, the tie region is closed. -/
theorem tieRegion_isClosed (JE JF : Ω → ℝ) (hE : Continuous JE) (hF : Continuous JF) :
    IsClosed {α | JE α = JF α} :=
  isClosed_eq hE hF

end Regions

end

end IdExp
