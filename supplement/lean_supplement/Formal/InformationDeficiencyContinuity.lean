import Formal.EntropyTVModulus
import Formal.FiniteBayesInformation
import Formal.PosteriorGarblingStrict
import Formal.EntropyGeometry
import Formal.DeficiencyTriangle
import Formal.ScoreProcessMonotonicity

/-!
# Information gain is deficiency-continuous, hence process-monotone

For a finite world class with prior `α`, the finite Bayesian information of
an experiment has the symmetric form `I_α(E) = H(m_E) − Σ_θ α_θ H(E_θ)`,
with `m_E` the signal marginal.  Neither term divides by a signal mass, so
the explicit entropy modulus applies rowwise: a uniform row-TV bound `r`
between two experiments on a `k`-letter alphabet gives
`|I_α(E) − I_α(F)| ≤ 2 · cappedEntropyModulus k r`.

Combined with data processing under arbitrary stochastic garbling (a convex
posterior potential cannot increase under garbling), this makes information
gain *deficiency-continuous*:

`I_α(F) ≤ I_α(E) + 2 · cappedEntropyModulus |Y| (δ(E, F))`.

Through `ScoreProcessMonotonicity`, complete information — the supremum of
prefix informations — is therefore monotone in causal finitary dominance on
finite world classes.  This is the information-gain instance of the
hierarchy: the finite-prefix process order is respected by the prior-free
audit, by every bounded decision value, and by information gain, each with
an explicit modulus.  No coupling or Fano inequality is used; the modulus is
not claimed to be sharp.
-/

namespace IdExp

open Finset Real

noncomputable section

set_option linter.unusedSectionVars false

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]

/-! ## The symmetric form of finite information -/

/-- `m · negMulLog (a / m) = negMulLog a + a · log m` for `m ≠ 0`. -/
theorem mul_negMulLog_div (a m : ℝ) (hm : m ≠ 0) :
    m * negMulLog (a / m) = negMulLog a + a * Real.log m := by
  by_cases ha : a = 0
  · simp [ha]
  · simp only [negMulLog]
    rw [Real.log_div ha hm]
    field_simp
    ring

/-- Mass times posterior entropy at one signal, in closed form. -/
theorem finiteBayesMass_mul_ent_posterior (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ)
    (E : FiniteExperiment Θ X) (hE : ∀ θ x, 0 ≤ E θ x) (x : X) :
    finiteBayesMass α E x * ent (finiteBayesPosterior α E x) =
      (∑ θ, negMulLog (α θ * E θ x)) - negMulLog (finiteBayesMass α E x) := by
  classical
  set m := finiteBayesMass α E x with hm
  have hpost : ∀ θ, finiteBayesPosterior α E x θ = α θ * E θ x / m := fun θ => rfl
  rcases eq_or_lt_of_le (finiteBayesMass_nonneg α E hα hE x) with h0 | hpos
  · have hm0 : m = 0 := h0.symm
    have hzero : ∀ θ, α θ * E θ x = 0 := by
      intro θ
      have hsum : (∑ θ, α θ * E θ x) = 0 := by
        change finiteBayesMass α E x = 0
        exact h0.symm
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun θ _ => mul_nonneg (hα θ) (hE θ x))).1 hsum θ (Finset.mem_univ θ)
    rw [hm0, zero_mul, negMulLog_zero, sub_zero]
    symm
    apply Finset.sum_eq_zero
    intro θ _
    rw [hzero θ, negMulLog_zero]
  · have hmne : m ≠ 0 := hpos.ne'
    unfold ent
    rw [Finset.mul_sum]
    have hterm : ∀ θ, m * negMulLog (finiteBayesPosterior α E x θ) =
        negMulLog (α θ * E θ x) + α θ * E θ x * Real.log m := by
      intro θ
      rw [hpost θ]
      exact mul_negMulLog_div _ _ hmne
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have hsum : (∑ θ, α θ * E θ x) = m := rfl
    rw [hsum, negMulLog]
    ring

/-- **Symmetric form of finite information.**  For a distribution prior and
a valid experiment, `I_α(E) = H(m_E) − Σ_θ α_θ H(E_θ)`. -/
theorem finiteBayesInformation_eq_ent_mass_sub (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    finiteBayesInformation α E = ent (finiteBayesMass α E) - ∑ θ, α θ * ent (E θ) := by
  classical
  have hE0 : ∀ θ x, 0 ≤ E θ x := fun θ x => (hE θ).1 x
  unfold finiteBayesInformation finiteBayesPotential
  simp_rw [finiteBayesMass_mul_ent_posterior α hα.1 E hE0]
  rw [Finset.sum_sub_distrib]
  have hjoint : (∑ x, ∑ θ, negMulLog (α θ * E θ x)) = ent α + ∑ θ, α θ * ent (E θ) := by
    rw [Finset.sum_comm]
    unfold ent
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro θ _
    simp_rw [negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, (hE θ).2, one_mul]
  rw [hjoint]
  unfold ent
  ring

/-! ## Rowwise continuity of information -/

/-- Total variation of prior mixtures is at most the prior average of the
rowwise total variations. -/
theorem finiteTV_priorMixture_le (α : Θ → ℝ) (hα : IsDist α) (p q : Θ → X → ℝ)
    (r : ℝ) (hrow : ∀ θ, finiteTV (p θ) (q θ) ≤ r) :
    finiteTV (fun x => ∑ θ, α θ * p θ x) (fun x => ∑ θ, α θ * q θ x) ≤ r := by
  classical
  unfold finiteTV
  have h1 : ∀ x, |(∑ θ, α θ * p θ x) - ∑ θ, α θ * q θ x| ≤ ∑ θ, α θ * |p θ x - q θ x| := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun θ _ => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg (hα.1 θ)]
  calc (1 / 2) * ∑ x, |(∑ θ, α θ * p θ x) - ∑ θ, α θ * q θ x|
      ≤ (1 / 2) * ∑ x, ∑ θ, α θ * |p θ x - q θ x| := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h1 x) (by norm_num)
    _ = ∑ θ, α θ * finiteTV (p θ) (q θ) := by
        unfold finiteTV
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro θ _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ ≤ ∑ θ, α θ * r := Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (hrow θ) (hα.1 θ)
    _ = r := by rw [← Finset.sum_mul, hα.2, one_mul]

theorem finiteBayesMass_isDist (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) : IsDist (finiteBayesMass α E) := by
  refine ⟨finiteBayesMass_nonneg α E hα.1 (fun θ x => (hE θ).1 x), ?_⟩
  unfold finiteBayesMass
  rw [Finset.sum_comm]
  calc (∑ θ, ∑ x, α θ * E θ x) = ∑ θ, α θ * ∑ x, E θ x := by
        apply Finset.sum_congr rfl
        intro θ _
        rw [Finset.mul_sum]
    _ = ∑ θ, α θ := by
        apply Finset.sum_congr rfl
        intro θ _
        rw [(hE θ).2, mul_one]
    _ = 1 := hα.2

/-- **Information is rowwise TV-continuous with twice the capped entropy
modulus.** -/
theorem abs_finiteBayesInformation_sub_le (α : Θ → ℝ) (hα : IsDist α)
    (E F : FiniteExperiment Θ Y) (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (r : ℝ) (hr0 : 0 ≤ r) (hrow : ∀ θ, finiteTV (E θ) (F θ) ≤ r) :
    |finiteBayesInformation α E - finiteBayesInformation α F| ≤
      2 * cappedEntropyModulus (Fintype.card Y) r := by
  rw [finiteBayesInformation_eq_ent_mass_sub α hα E hE,
    finiteBayesInformation_eq_ent_mass_sub α hα F hF]
  have hmass : |ent (finiteBayesMass α E) - ent (finiteBayesMass α F)| ≤
      cappedEntropyModulus (Fintype.card Y) r := by
    apply abs_ent_sub_le_cappedEntropyModulus _ _ (finiteBayesMass_isDist α hα E hE)
      (finiteBayesMass_isDist α hα F hF) r hr0
    exact finiteTV_priorMixture_le α hα E F r hrow
  have hrows : |(∑ θ, α θ * ent (E θ)) - ∑ θ, α θ * ent (F θ)| ≤
      cappedEntropyModulus (Fintype.card Y) r := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc (∑ θ, |α θ * ent (E θ) - α θ * ent (F θ)|)
        = ∑ θ, α θ * |ent (E θ) - ent (F θ)| := by
          apply Finset.sum_congr rfl
          intro θ _
          rw [← mul_sub, abs_mul, abs_of_nonneg (hα.1 θ)]
      _ ≤ ∑ θ, α θ * cappedEntropyModulus (Fintype.card Y) r := by
          apply Finset.sum_le_sum
          intro θ _
          apply mul_le_mul_of_nonneg_left _ (hα.1 θ)
          exact abs_ent_sub_le_cappedEntropyModulus _ _ (hE θ) (hF θ) r hr0 (hrow θ)
      _ = cappedEntropyModulus (Fintype.card Y) r := by rw [← Finset.sum_mul, hα.2, one_mul]
  calc |ent (finiteBayesMass α E) - ∑ θ, α θ * ent (E θ) -
        (ent (finiteBayesMass α F) - ∑ θ, α θ * ent (F θ))|
      = |(ent (finiteBayesMass α E) - ent (finiteBayesMass α F)) -
          ((∑ θ, α θ * ent (E θ)) - ∑ θ, α θ * ent (F θ))| := by congr 1; ring
    _ ≤ |ent (finiteBayesMass α E) - ent (finiteBayesMass α F)| +
          |(∑ θ, α θ * ent (E θ)) - ∑ θ, α θ * ent (F θ)| := abs_sub _ _
    _ ≤ 2 * cappedEntropyModulus (Fintype.card Y) r := by linarith

/-! ## Data processing under stochastic garbling -/

/-- The finite-prior posterior system of a valid experiment, using the prior
itself at null signals. -/
def finitePriorPosteriorSystem (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) :
    SignalPosteriorSystem (fun θ x => α θ * E θ x) where
  mass := finiteBayesMass α E
  mass_dist := finiteBayesMass_isDist α hα E hE
  density := fun x => if finiteBayesMass α E x = 0 then α else finiteBayesPosterior α E x
  factor := by
    intro x θ
    by_cases hx : finiteBayesMass α E x = 0
    · have hzero : α θ * E θ x = 0 := by
        have hsum : (∑ θ, α θ * E θ x) = 0 := hx
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun θ _ => mul_nonneg (hα.1 θ) ((hE θ).1 x))).1 hsum θ (Finset.mem_univ θ)
      simp [hx, hzero]
    · simp only [if_neg hx]
      rw [mul_comm]
      exact finiteBayesPosterior_mul_mass α E hα.1 (fun θ x => (hE θ).1 x) x θ

theorem finitePriorPosteriorSystem_potential (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (Φ : (Θ → ℝ) → ℝ) :
    (finitePriorPosteriorSystem α hα E hE).potential Φ = finiteBayesPotential Φ α E := by
  unfold SignalPosteriorSystem.potential finiteBayesPotential
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : finiteBayesMass α E x = 0
  · simp [finitePriorPosteriorSystem, hx]
  · simp [finitePriorPosteriorSystem, hx]

theorem finitePriorPosteriorSystem_density_mem (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (x : X) :
    (finitePriorPosteriorSystem α hα E hE).density x ∈ stdSimplex ℝ Θ := by
  by_cases hx : finiteBayesMass α E x = 0
  · simp only [finitePriorPosteriorSystem, if_pos hx]
    exact ⟨hα.1, hα.2⟩
  · simp only [finitePriorPosteriorSystem, if_neg hx]
    exact finiteBayesPosterior_mem_simplex α E hα.1 (fun θ x => (hE θ).1 x) x hx

/-- **Data processing for posterior potentials.**  A convex potential of the
posterior cannot increase under any stochastic garbling of the signal. -/
theorem finiteBayesPotential_garble_le (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (Φ : (Θ → ℝ) → ℝ) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ) :
    finiteBayesPotential Φ α (finiteDecisionLaw E G) ≤ finiteBayesPotential Φ α E := by
  classical
  have hEG : IsFiniteExperiment (finiteDecisionLaw E G) := finiteDecisionLaw_valid E hE G hG
  let P := finitePriorPosteriorSystem α hα E hE
  let Q := finitePriorPosteriorSystem α hα (finiteDecisionLaw E G) hEG
  have hGF : finiteDecisionLaw (fun θ x => α θ * E θ x) G =
      (fun θ y => α θ * finiteDecisionLaw E G θ y) := by
    funext θ y
    simp only [finiteDecisionLaw]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hmass : ∀ y, ∑ x, P.mass x * G x y = Q.mass y := by
    intro y
    simp only [P, Q, finitePriorPosteriorSystem, finiteBayesMass, finiteDecisionLaw]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro θ _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h := signalPosterior_potential_mono P Q G hG hGF hmass Φ (stdSimplex ℝ Θ) hΦ
    (finitePriorPosteriorSystem_density_mem α hα E hE)
  rwa [finitePriorPosteriorSystem_potential, finitePriorPosteriorSystem_potential] at h

/-- **Data processing for information.**  Stochastic garbling cannot
increase finite Bayesian information. -/
theorem finiteBayesInformation_garble_le (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    finiteBayesInformation α (finiteDecisionLaw E G) ≤ finiteBayesInformation α E := by
  have h := finiteBayesPotential_garble_le α hα E hE G hG (fun p => -ent p)
    strictConvexOn_neg_ent_simplex.convexOn
  simp only [finiteBayesPotential, mul_neg, Finset.sum_neg_distrib] at h
  unfold finiteBayesInformation finiteBayesPotential
  linarith

/-! ## Deficiency continuity of information -/

/-- **Information gain is deficiency-continuous.**  For valid experiments on
a finite world class with a distribution prior,
`I_α(F) ≤ I_α(E) + 2 · cappedEntropyModulus |Y| (δ(E,F))`. -/
theorem finiteBayesInformation_le_add_modulus [Nonempty Θ] (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteBayesInformation α F ≤ finiteBayesInformation α E +
      2 * cappedEntropyModulus (Fintype.card Y) (finiteDeficiency E F) := by
  have hY : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  have hδ0 : 0 ≤ finiteDeficiency E F := finiteDeficiency_nonneg_of_valid E F hE hF
  -- the bound holds at every radius δ + η, then let η → 0 by continuity of the modulus
  have hstep : ∀ η : ℝ, 0 < η → finiteBayesInformation α F ≤ finiteBayesInformation α E +
      2 * cappedEntropyModulus (Fintype.card Y) (finiteDeficiency E F + η) := by
    intro η hη
    obtain ⟨G, hG, herr⟩ := exists_decoder_le_finiteDeficiency_add E F hE hF hη
    have hEG : IsFiniteExperiment (finiteDecisionLaw E G) := finiteDecisionLaw_valid E hE G hG
    have hrow : ∀ θ, finiteTV (finiteDecisionLaw E G θ) (F θ) ≤ finiteDeficiency E F + η :=
      fun θ => herr θ
    have h1 := abs_finiteBayesInformation_sub_le α hα (finiteDecisionLaw E G) F hEG hF
      (finiteDeficiency E F + η) (by linarith) hrow
    have h2 := finiteBayesInformation_garble_le α hα E hE G hG
    have h3 := (abs_le.mp h1).1
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hcont := (continuous_cappedEntropyModulus (Fintype.card Y)).continuousAt
    (x := finiteDeficiency E F)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη, h⟩ := hcont (ε / 2) (by positivity)
  have hclose := h (x := finiteDeficiency E F + η / 2)
    (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]; linarith)
  rw [Real.dist_eq] at hclose
  have hmod := (abs_lt.mp hclose).2
  have := hstep (η / 2) (by positivity)
  linarith

/-! ## Complete information respects the finitary process order -/

section Causal

universe u

variable {A O Θ' : Type u} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [Fintype Θ'] [Nonempty Θ']

/-- Information gain is deficiency-continuous on the packaged causal chain,
with the target-alphabet modulus. -/
theorem information_deficiencyContinuousAt (α : Θ' → ℝ) (hα : IsDist α)
    (F : ValidCausalPrefix A O Θ') :
    DeficiencyContinuousAt validCausalPrefixDeficiency
      (fun x : ValidCausalPrefix A O Θ' => finiteBayesInformation α x.2.1)
      (fun r => 2 * cappedEntropyModulus (Fintype.card (CausalFiniteTrace A O F.1)) r) F := by
  intro E
  exact finiteBayesInformation_le_add_modulus α hα E.2.1 F.2.1 E.2.2 F.2.2

theorem information_modulus_vanishing (k : ℕ) :
    VanishingModulus (fun r => 2 * cappedEntropyModulus k r) := by
  intro ε hε
  obtain ⟨η, hη, h⟩ := cappedEntropyModulus_vanishing k (ε / 2) (by positivity)
  exact ⟨η, hη, fun r hr0 hr => by linarith [h r hr0 hr]⟩

/-- Information never exceeds the prior entropy. -/
theorem finiteBayesInformation_le_ent (α : Θ' → ℝ) (hα : IsDist α)
    {X' : Type*} [Fintype X'] (E : FiniteExperiment Θ' X') (hE : IsFiniteExperiment E) :
    finiteBayesInformation α E ≤ ent α := by
  unfold finiteBayesInformation
  have : 0 ≤ finiteBayesPotential ent α E := by
    unfold finiteBayesPotential
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (finiteBayesMass_nonneg α E hα.1 (fun θ x => (hE θ).1 x) x)
    exact Finset.sum_nonneg fun c _ => Real.negMulLog_nonneg
      (finiteBayesPosterior_nonneg α E hα.1 (fun θ x => (hE θ).1 x) x c)
      (finiteBayesPosterior_le_one α E hα.1 (fun θ x => (hE θ).1 x) x c)
  linarith

/-- The complete (terminal) information of a policy's prefix chain. -/
def causalCompleteInformation (Qs : Θ' → CausalResponse A O) (α : Θ' → ℝ)
    (pol : ValidCausalPolicy A O) : ℝ :=
  sSup (Set.range fun t => finiteBayesInformation α (causalFiniteExperiment pol.1 Qs t))

set_option maxHeartbeats 400000 in
/-- Along a finitarily dominating policy, information eventually exceeds
every fixed rival prefix's information minus any tolerance. -/
theorem causalFinitaryDominates_information_eventually_ge
    (Qs : Θ' → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (α : Θ' → ℝ) (hα : IsDist α)
    {pol rho : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs pol rho) (n : ℕ) :
    ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
      finiteBayesInformation α (causalFiniteExperiment rho.1 Qs n) ≤
        finiteBayesInformation α (causalFiniteExperiment pol.1 Qs t) + ε := by
  intro ε hε
  have hcont := information_deficiencyContinuousAt α hα (validCausalPrefixChain Qs hQ rho n)
  obtain ⟨T, hT⟩ := finitaryDominates_score_eventually_le
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg
    (fun x : ValidCausalPrefix A O Θ' => finiteBayesInformation α x.2.1) _
    (information_modulus_vanishing _)
    ((causalFinitaryDominates_iff_packaged Qs hQ pol rho).1 hdom) n hcont ε hε
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  change finiteBayesInformation α (causalFiniteExperiment rho.1 Qs n) ≤
    finiteBayesInformation α (causalFiniteExperiment pol.1 Qs t) + ε at h
  exact h

set_option maxHeartbeats 400000 in
/-- **Complete information is monotone in the finitary process order.**
On a finite world class with a distribution prior, a finitarily dominating
policy has at least the complete information of the dominated one. -/
theorem causalCompleteInformation_mono_of_finitaryDominates
    (Qs : Θ' → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (α : Θ' → ℝ) (hα : IsDist α)
    {pol rho : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs pol rho) :
    causalCompleteInformation Qs α rho ≤ causalCompleteInformation Qs α pol := by
  have hbdd : BddAbove (Set.range fun t =>
      finiteBayesInformation α (causalFiniteExperiment pol.1 Qs t)) := by
    refine ⟨ent α, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact finiteBayesInformation_le_ent α hα _ (causalFiniteExperiment_valid pol.1 pol.2 Qs hQ t)
  unfold causalCompleteInformation
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  have hcont := information_deficiencyContinuousAt α hα (validCausalPrefixChain Qs hQ rho n)
  have h := score_le_processScoreSup_of_finitaryDominates
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg
    (fun x : ValidCausalPrefix A O Θ' => finiteBayesInformation α x.2.1) _
    (information_modulus_vanishing _)
    ((causalFinitaryDominates_iff_packaged Qs hQ pol rho).1 hdom) hbdd n hcont
  change finiteBayesInformation α (causalFiniteExperiment rho.1 Qs n) ≤
    sSup (Set.range fun t => finiteBayesInformation α (causalFiniteExperiment pol.1 Qs t)) at h
  exact h

/-- Mutually dominant policies have equal complete information. -/
theorem causalCompleteInformation_eq_of_mutual
    (Qs : Θ' → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (α : Θ' → ℝ) (hα : IsDist α)
    {pol rho : ValidCausalPolicy A O} (hpr : CausalFinitaryDominates Qs pol rho)
    (hrp : CausalFinitaryDominates Qs rho pol) :
    causalCompleteInformation Qs α rho = causalCompleteInformation Qs α pol :=
  le_antisymm (causalCompleteInformation_mono_of_finitaryDominates Qs hQ α hα hpr)
    (causalCompleteInformation_mono_of_finitaryDominates Qs hQ α hα hrp)

end Causal

end

end IdExp
