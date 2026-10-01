import Formal.InformationDeficiencyContinuity
import Formal.ApproximateAdmissibilityAssembly
import Formal.FinitePinsker
import Formal.FiniteDecoderAttainment

/-!
# The reverse-decoder Pinsker bound and the finite-class quantitative theorem

The analytic core of the quantitative admissibility theorem
(`thm:approximate-information-admissibility`): for a finite world class with
prior `α`, an experiment `F`, and a stochastic garbling `G`, the Bayes reverse
channel `R` satisfies

`∑_θ α_θ · TV(F_θ, (FG)_θ R)² ≤ (I_α(F) − I_α(FG)) / 2`.

The proof is the one in the paper, in finite sums.  In each world the joint
law of (signal, garbled signal) under the forward chain `θ → S → T` and under
the reverse chain `θ → T → S` have KL divergence whose prior average is exactly
the information gap (a termwise log identity), total variation contracts under
marginalization to the signal, and the repository's sharp finite Pinsker
inequality converts KL to squared TV.  Absolute continuity of the reverse
joint law holds in every world of positive prior mass.

Combined with the uniformization over a prior floor `α_θ ≥ a` and the
assembly lemma `finiteDeficiency_le_of_simulator_and_reverse`, this yields
the finite-class quantitative admissibility bound

`δ(E, F) ≤ ρ + √((η + 2·cappedEntropyModulus |X| ρ) / (2a))`

whenever `δ(F, E) ≤ ρ` and `I_α(F) ≤ I_α(E) + η`, with the repository's
entropy TV-modulus in place of the paper's Fano term `b_k(ρ)`.
-/

namespace IdExp

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Marginal contraction of total variation -/

section Marginal

variable {S T : Type*} [Fintype S] [Fintype T]

/-- Total variation cannot increase under marginalization. -/
theorem finiteTV_marginal_fst_le (P Q : S × T → ℝ) :
    finiteTV (fun s => ∑ t, P (s, t)) (fun s => ∑ t, Q (s, t)) ≤ finiteTV P Q := by
  unfold finiteTV
  rw [Fintype.sum_prod_type]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => ?_) (by norm_num)
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

end Marginal

/-! ## Joint laws, the Bayes reverse channel, and the KL identity -/

section Core

variable {Θ S T : Type*} [Fintype Θ] [Fintype S] [Fintype T]

/-- Bayes mass of a garbled experiment is the garbled Bayes mass. -/
theorem finiteBayesMass_decisionLaw (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ)
    (t : T) :
    finiteBayesMass α (finiteDecisionLaw F G) t = ∑ s, finiteBayesMass α F s * G s t := by
  simp only [finiteBayesMass, finiteDecisionLaw]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The forward joint law of (signal, garbled signal) in world `θ`. -/
def jointForward (F : FiniteExperiment Θ S) (G : S → T → ℝ) (θ : Θ) : S × T → ℝ :=
  fun z => F θ z.1 * G z.1 z.2

/-- The joint law of the same pair obtained by drawing the garbled signal and
reconstructing the signal through a reverse channel. -/
def jointReverse (F : FiniteExperiment Θ S) (G : S → T → ℝ) (R : T → S → ℝ) (θ : Θ) :
    S × T → ℝ :=
  fun z => finiteDecisionLaw F G θ z.2 * R z.2 z.1

theorem jointForward_marginal (F : FiniteExperiment Θ S) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) (θ : Θ) (s : S) :
    ∑ t, jointForward F G θ (s, t) = F θ s := by
  show ∑ t, F θ s * G s t = F θ s
  rw [← Finset.mul_sum, (hG s (Set.mem_univ s)).2, mul_one]

theorem jointReverse_marginal (F : FiniteExperiment Θ S) (G : S → T → ℝ) (R : T → S → ℝ)
    (θ : Θ) (s : S) :
    ∑ t, jointReverse F G R θ (s, t) = finiteDecisionLaw (finiteDecisionLaw F G) R θ s := rfl

theorem jointForward_isDist (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ) : IsDist (jointForward F G θ) := by
  constructor
  · intro z
    exact mul_nonneg ((hF θ).1 z.1) ((hG z.1 (Set.mem_univ _)).1 z.2)
  · rw [Fintype.sum_prod_type]
    show (∑ s, ∑ t, F θ s * G s t) = 1
    calc (∑ s, ∑ t, F θ s * G s t) = ∑ s, F θ s * ∑ t, G s t := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
      _ = ∑ s, F θ s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [(hG s (Set.mem_univ s)).2, mul_one]
      _ = 1 := (hF θ).2

theorem jointReverse_isDist (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (R : T → S → ℝ)
    (hR : R ∈ stochasticRules T S) (θ : Θ) : IsDist (jointReverse F G R θ) := by
  have hFG := finiteDecisionLaw_valid F hF G hG
  constructor
  · intro z
    exact mul_nonneg ((hFG θ).1 z.2) ((hR z.2 (Set.mem_univ _)).1 z.1)
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    show (∑ t, ∑ s, finiteDecisionLaw F G θ t * R t s) = 1
    calc (∑ t, ∑ s, finiteDecisionLaw F G θ t * R t s)
        = ∑ t, finiteDecisionLaw F G θ t * ∑ s, R t s := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
      _ = ∑ t, finiteDecisionLaw F G θ t := by
          apply Finset.sum_congr rfl
          intro t _
          rw [(hR t (Set.mem_univ t)).2, mul_one]
      _ = 1 := (hFG θ).2

/-- The Bayes reverse channel from garbled signals back to signals, with a
uniform row at null predictive mass. -/
def bayesReverseChannel [Nonempty S] (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) :
    T → S → ℝ :=
  fun t s =>
    if finiteBayesMass α (finiteDecisionLaw F G) t = 0 then uniformPrior S s
    else finiteBayesMass α F s * G s t / finiteBayesMass α (finiteDecisionLaw F G) t

theorem bayesReverseChannel_eq [Nonempty S] (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    bayesReverseChannel α F G =
      signalPosteriorReverse (finitePriorPosteriorSystem α hα F hF)
        (finitePriorPosteriorSystem α hα (finiteDecisionLaw F G) (finiteDecisionLaw_valid F hF G hG))
        G := rfl

theorem bayesReverseChannel_stochastic [Nonempty S] (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    bayesReverseChannel α F G ∈ stochasticRules T S := by
  rw [bayesReverseChannel_eq α hα F hF G hG]
  exact signalPosteriorReverse_stochastic _ _ G hG fun t => (finiteBayesMass_decisionLaw α F G t).symm

/-- Absolute continuity of the reverse joint law in every world of positive
prior mass. -/
theorem jointReverse_ac [Nonempty S] (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (θ : Θ)
    (hθ : α θ ≠ 0) :
    ∀ z, jointReverse F G (bayesReverseChannel α F G) θ z = 0 → jointForward F G θ z = 0 := by
  rintro ⟨s, t⟩ hz
  unfold jointReverse at hz
  unfold jointForward
  show F θ s * G s t = 0
  have hFnn : ∀ s', 0 ≤ F θ s' * G s' t :=
    fun s' => mul_nonneg ((hF θ).1 s') ((hG s' (Set.mem_univ s')).1 t)
  have hFG_zero : finiteDecisionLaw F G θ t = 0 → F θ s * G s t = 0 := fun h =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun s' _ => hFnn s')).1 h s (Finset.mem_univ s)
  have hp_zero : finiteBayesMass α F s = 0 → F θ s = 0 := by
    intro h
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c _ => mul_nonneg (hα.1 c) ((hF c).1 s))).1 h θ (Finset.mem_univ θ)
    exact (mul_eq_zero.1 this).resolve_left hθ
  by_cases hq : finiteBayesMass α (finiteDecisionLaw F G) t = 0
  · rw [finiteBayesMass_decisionLaw] at hq
    have hpG : finiteBayesMass α F s * G s t = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun s' _ => mul_nonneg
        (Finset.sum_nonneg fun c _ => mul_nonneg (hα.1 c) ((hF c).1 s'))
        ((hG s' (Set.mem_univ s')).1 t))).1 hq s (Finset.mem_univ s)
    rcases mul_eq_zero.1 hpG with h | h
    · rw [hp_zero h, zero_mul]
    · rw [h, mul_zero]
  · have hRts : bayesReverseChannel α F G t s =
        finiteBayesMass α F s * G s t / finiteBayesMass α (finiteDecisionLaw F G) t := by
      unfold bayesReverseChannel
      rw [if_neg hq]
    rw [hRts] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact hFG_zero h
    · rcases (div_eq_zero_iff.1 h) with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rw [hp_zero h, zero_mul]
        · rw [h, mul_zero]
      · exact absurd h hq

/-- Mutual information in log-ratio form. -/
theorem finiteBayesInformation_eq_sum_log (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F) :
    finiteBayesInformation α F =
      ∑ θ, ∑ s, α θ * F θ s * Real.log (F θ s / finiteBayesMass α F s) := by
  rw [finiteBayesInformation_eq_ent_mass_sub α hα F hF]
  have hkey : ∀ θ s, α θ * F θ s * Real.log (F θ s / finiteBayesMass α F s) =
      α θ * F θ s * Real.log (F θ s) - α θ * F θ s * Real.log (finiteBayesMass α F s) := by
    intro θ s
    by_cases h : α θ * F θ s = 0
    · rw [h]; ring
    · have hF0 : F θ s ≠ 0 := (mul_ne_zero_iff.1 h).2
      have hpos : 0 < α θ * F θ s :=
        lt_of_le_of_ne (mul_nonneg (hα.1 θ) ((hF θ).1 s)) (Ne.symm h)
      have hm : finiteBayesMass α F s ≠ 0 := by
        have hle : α θ * F θ s ≤ finiteBayesMass α F s :=
          Finset.single_le_sum (fun c _ => mul_nonneg (hα.1 c) ((hF c).1 s)) (Finset.mem_univ θ)
        exact ne_of_gt (lt_of_lt_of_le hpos hle)
      rw [Real.log_div hF0 hm]
      ring
  have h1 : ent (finiteBayesMass α F) =
      -∑ s, ∑ θ, α θ * F θ s * Real.log (finiteBayesMass α F s) := by
    unfold ent
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [Real.negMulLog, ← Finset.sum_mul]
    unfold finiteBayesMass
    ring
  have h2 : ∑ θ, α θ * ent (F θ) = -∑ θ, ∑ s, α θ * F θ s * Real.log (F θ s) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro θ _
    unfold ent
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [Real.negMulLog]
    ring
  have h3 : (∑ s, ∑ θ, α θ * F θ s * Real.log (finiteBayesMass α F s)) =
      ∑ θ, ∑ s, α θ * F θ s * Real.log (finiteBayesMass α F s) := Finset.sum_comm
  simp_rw [hkey]
  simp only [Finset.sum_sub_distrib]
  rw [h1, h2, h3]
  ring

theorem sum_triple_eq_source (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) (L : Θ → S → ℝ) :
    ∑ θ, ∑ s, ∑ t, α θ * F θ s * G s t * L θ s = ∑ θ, ∑ s, α θ * F θ s * L θ s := by
  apply Finset.sum_congr rfl
  intro θ _
  apply Finset.sum_congr rfl
  intro s _
  have e : ∀ t, α θ * F θ s * G s t * L θ s = (α θ * F θ s * L θ s) * G s t := fun t => by ring
  simp_rw [e]
  rw [← Finset.mul_sum, (hG s (Set.mem_univ s)).2, mul_one]

theorem sum_triple_eq_decisionLaw (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ)
    (L : Θ → T → ℝ) :
    ∑ θ, ∑ s, ∑ t, α θ * F θ s * G s t * L θ t =
      ∑ θ, ∑ t, α θ * finiteDecisionLaw F G θ t * L θ t := by
  apply Finset.sum_congr rfl
  intro θ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  unfold finiteDecisionLaw
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- **The joint KL identity.**  The prior-averaged KL divergence between the
forward and Bayes-reverse joint laws is exactly the information lost by the
garbling. -/
theorem weighted_finiteKL_joint_eq [Nonempty S] (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    ∑ θ, α θ * finiteKL (jointForward F G θ) (jointReverse F G (bayesReverseChannel α F G) θ) =
      finiteBayesInformation α F - finiteBayesInformation α (finiteDecisionLaw F G) := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  rw [finiteBayesInformation_eq_sum_log α hα F hF, finiteBayesInformation_eq_sum_log α hα _ hFG]
  have hkey : ∀ θ s t, α θ * (jointForward F G θ (s, t) * Real.log (jointForward F G θ (s, t) /
      jointReverse F G (bayesReverseChannel α F G) θ (s, t))) =
      α θ * F θ s * G s t * Real.log (F θ s / finiteBayesMass α F s) -
        α θ * F θ s * G s t * Real.log (finiteDecisionLaw F G θ t /
          finiteBayesMass α (finiteDecisionLaw F G) t) := by
    intro θ s t
    unfold jointForward jointReverse
    show α θ * (F θ s * G s t * Real.log (F θ s * G s t /
      (finiteDecisionLaw F G θ t * bayesReverseChannel α F G t s))) = _
    by_cases h : α θ * F θ s * G s t = 0
    · have e : ∀ L₁ L₂ L₃ : ℝ, α θ * (F θ s * G s t * L₁) =
          α θ * F θ s * G s t * L₂ - α θ * F θ s * G s t * L₃ := by
        intro L₁ L₂ L₃
        rw [show α θ * (F θ s * G s t * L₁) = (α θ * F θ s * G s t) * L₁ by ring, h]
        ring
      exact e _ _ _
    · have hαF : α θ * F θ s ≠ 0 := (mul_ne_zero_iff.1 h).1
      have hG0 : G s t ≠ 0 := (mul_ne_zero_iff.1 h).2
      have hα0 : α θ ≠ 0 := (mul_ne_zero_iff.1 hαF).1
      have hF0 : F θ s ≠ 0 := (mul_ne_zero_iff.1 hαF).2
      have hαpos : 0 < α θ := lt_of_le_of_ne (hα.1 θ) (Ne.symm hα0)
      have hFpos : 0 < F θ s := lt_of_le_of_ne ((hF θ).1 s) (Ne.symm hF0)
      have hGpos : 0 < G s t := lt_of_le_of_ne ((hG s (Set.mem_univ s)).1 t) (Ne.symm hG0)
      have hp : finiteBayesMass α F s ≠ 0 := by
        have hle : α θ * F θ s ≤ finiteBayesMass α F s :=
          Finset.single_le_sum (fun c _ => mul_nonneg (hα.1 c) ((hF c).1 s)) (Finset.mem_univ θ)
        exact ne_of_gt (lt_of_lt_of_le (mul_pos hαpos hFpos) hle)
      have hFGpos : 0 < finiteDecisionLaw F G θ t := by
        have hle : F θ s * G s t ≤ finiteDecisionLaw F G θ t :=
          Finset.single_le_sum
            (fun s' _ => mul_nonneg ((hF θ).1 s') ((hG s' (Set.mem_univ s')).1 t))
            (Finset.mem_univ s)
        exact lt_of_lt_of_le (mul_pos hFpos hGpos) hle
      have hq : finiteBayesMass α (finiteDecisionLaw F G) t ≠ 0 := by
        have hle : α θ * finiteDecisionLaw F G θ t ≤ finiteBayesMass α (finiteDecisionLaw F G) t :=
          Finset.single_le_sum (fun c _ => mul_nonneg (hα.1 c) ((hFG c).1 t)) (Finset.mem_univ θ)
        exact ne_of_gt (lt_of_lt_of_le (mul_pos hαpos hFGpos) hle)
      have hRts : bayesReverseChannel α F G t s =
          finiteBayesMass α F s * G s t / finiteBayesMass α (finiteDecisionLaw F G) t := by
        unfold bayesReverseChannel
        rw [if_neg hq]
      rw [hRts]
      have harg : F θ s * G s t / (finiteDecisionLaw F G θ t *
          (finiteBayesMass α F s * G s t / finiteBayesMass α (finiteDecisionLaw F G) t)) =
          (F θ s / finiteBayesMass α F s) /
            (finiteDecisionLaw F G θ t / finiteBayesMass α (finiteDecisionLaw F G) t) := by
        field_simp
      rw [harg, Real.log_div (div_ne_zero hF0 hp) (div_ne_zero hFGpos.ne' hq)]
      ring
  have hL : ∀ θ, α θ * finiteKL (jointForward F G θ)
      (jointReverse F G (bayesReverseChannel α F G) θ) =
      ∑ s, ∑ t, (α θ * F θ s * G s t * Real.log (F θ s / finiteBayesMass α F s) -
        α θ * F θ s * G s t * Real.log (finiteDecisionLaw F G θ t /
          finiteBayesMass α (finiteDecisionLaw F G) t)) := by
    intro θ
    unfold finiteKL
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact hkey θ s t
  simp_rw [hL]
  simp only [Finset.sum_sub_distrib]
  rw [sum_triple_eq_source α F G hG, sum_triple_eq_decisionLaw α F G]

/-- **The reverse-decoder Pinsker bound.**  The prior-weighted squared
total-variation error of the Bayes reverse channel is at most half the
information lost by the garbling. -/
theorem weighted_reverse_sq_le_information_gap [Nonempty S] (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) :
    ∑ θ, α θ * (finiteTV (F θ)
      (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)) ^ 2 ≤
      (finiteBayesInformation α F - finiteBayesInformation α (finiteDecisionLaw F G)) / 2 := by
  rw [← weighted_finiteKL_joint_eq α hα F hF G hG, Finset.sum_div]
  apply Finset.sum_le_sum
  intro θ _
  by_cases hθ : α θ = 0
  · rw [hθ]; simp
  · rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (hα.1 θ)
    have hmarg : finiteTV (F θ)
        (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ) ≤
        finiteTV (jointForward F G θ) (jointReverse F G (bayesReverseChannel α F G) θ) := by
      have h := finiteTV_marginal_fst_le (jointForward F G θ)
        (jointReverse F G (bayesReverseChannel α F G) θ)
      have e1 : (fun s => ∑ t, jointForward F G θ (s, t)) = F θ :=
        funext fun s => jointForward_marginal F G hG θ s
      have e2 : (fun s => ∑ t, jointReverse F G (bayesReverseChannel α F G) θ (s, t)) =
          finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ :=
        funext fun s => jointReverse_marginal F G _ θ s
      rwa [e1, e2] at h
    have hpin := finiteTV_sq_le_finiteKL_half _ _ (jointForward_isDist F hF G hG θ)
      (jointReverse_isDist F hF G hG _ (bayesReverseChannel_stochastic α hα F hF G hG) θ)
      (jointReverse_ac α hα F hF G hG θ hθ)
    calc (finiteTV (F θ)
          (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)) ^ 2
        ≤ (finiteTV (jointForward F G θ) (jointReverse F G (bayesReverseChannel α F G) θ)) ^ 2 :=
          by
            have h0 := finiteTV_nonneg (F θ)
              (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)
            nlinarith [h0, hmarg]
      _ ≤ _ := hpin

/-- Uniformization over a prior floor: a weighted mean-square bound gives a
pointwise bound. -/
theorem sq_le_of_weighted_sum_le (α : Θ → ℝ) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (e : Θ → ℝ) (g : ℝ) (hg : ∑ θ, α θ * e θ ^ 2 ≤ g) (θ : Θ) : e θ ^ 2 ≤ g / a := by
  have h1 : a * e θ ^ 2 ≤ α θ * e θ ^ 2 := mul_le_mul_of_nonneg_right (hlow θ) (sq_nonneg _)
  have h2 : α θ * e θ ^ 2 ≤ ∑ θ', α θ' * e θ' ^ 2 :=
    Finset.single_le_sum (fun θ' _ => mul_nonneg (ha.le.trans (hlow θ')) (sq_nonneg _))
      (Finset.mem_univ θ)
  rw [le_div_iff₀ ha]
  linarith

end Core

/-! ## The finite-class quantitative admissibility theorem -/

section Quantitative

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y] [Nonempty Θ] [Nonempty X] [Nonempty Y]

/-- **Finite-class quantitative admissibility.**  With prior floor `a`, if `F`
simulates `E` within `ρ` and gains at most `η` more information than `E`, then
`E` simulates `F` within `ρ + √((η + 2·ω_|X|(ρ)) / (2a))`, where `ω` is the
capped entropy TV-modulus.  The decoder is the attained near-optimal one and
the reverse channel is the Bayes reverse channel; nothing else is chosen. -/
theorem finiteDeficiency_le_of_information_gap (α : Θ → ℝ) (hα : IsDist α)
    (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F)
    (η : ℝ) (hη : finiteBayesInformation α F ≤ finiteBayesInformation α E + η)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : finiteDeficiency F E ≤ ρ) :
    finiteDeficiency E F ≤
      ρ + Real.sqrt ((η + 2 * cappedEntropyModulus (Fintype.card X) ρ) / (2 * a)) := by
  obtain ⟨G, hG, hGerr⟩ := exists_decoder_eq_finiteDeficiency F E
  have hGρ : ∀ θ, decodeErr F E G θ ≤ ρ := fun θ => (hGerr θ).trans hρ
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  have hrow : ∀ θ, finiteTV (E θ) (finiteDecisionLaw F G θ) ≤ ρ := fun θ => by
    rw [finiteTV_symm]
    exact hGρ θ
  have hcont := abs_finiteBayesInformation_sub_le α hα E (finiteDecisionLaw F G) hE hFG ρ hρ0 hrow
  have hgap : finiteBayesInformation α F - finiteBayesInformation α (finiteDecisionLaw F G) ≤
      η + 2 * cappedEntropyModulus (Fintype.card X) ρ := by
    have := (abs_le.1 hcont).2
    linarith
  have hsq := weighted_reverse_sq_le_information_gap α hα F hF G hG
  have hR : bayesReverseChannel α F G ∈ stochasticRules X Y :=
    bayesReverseChannel_stochastic α hα F hF G hG
  have hb : ∀ θ, decodeErr (finiteDecisionLaw F G) F (bayesReverseChannel α F G) θ ≤
      Real.sqrt ((η + 2 * cappedEntropyModulus (Fintype.card X) ρ) / (2 * a)) := by
    intro θ
    have h1 : (finiteTV (F θ)
        (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)) ^ 2 ≤
        (η + 2 * cappedEntropyModulus (Fintype.card X) ρ) / (2 * a) := by
      rw [← div_div]
      exact sq_le_of_weighted_sum_le α a ha hlow _ _ (hsq.trans (by linarith)) θ
    show finiteTV (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)
      (F θ) ≤ _
    rw [finiteTV_symm]
    calc finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)
        = Real.sqrt ((finiteTV (F θ)
            (finiteDecisionLaw (finiteDecisionLaw F G) (bayesReverseChannel α F G) θ)) ^ 2) :=
          (Real.sqrt_sq (finiteTV_nonneg _ _)).symm
      _ ≤ Real.sqrt ((η + 2 * cappedEntropyModulus (Fintype.card X) ρ) / (2 * a)) :=
          Real.sqrt_le_sqrt h1
  exact finiteDeficiency_le_of_simulator_and_reverse E F hE hF G hG ρ hGρ
    (bayesReverseChannel α F G) hR _ hb

end Quantitative

end

end IdExp
