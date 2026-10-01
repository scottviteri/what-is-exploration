import Formal.FiniteDecoderAttainment
import Formal.DeterministicDeficiency

/-!
# Deterministic versus randomized exact-label decoding

For a finite world class and a finite acquired signal, the deterministic
minimax error is the literal minimum over all label-valued decoding functions
of their worst-world probability of error. The randomized value is the
existing `finiteDeficiency` to the identity-label experiment.

Embedding deterministic decoders gives `δ ≤ e_det`. Rounding each stochastic
decoder row to a largest-probability label gives `e_det ≤ 2 δ`: an incorrectly
selected label implies that the true label had probability at most one half.
The stochastic infimum is attained by the compactness theorem already proved
in `BinaryBlackwell.lean`; no optimizer or selector is assumed.

The comparison is also proved for a sequence of changing finite signal types,
and then for the actual causal finite-prefix experiments. This supplies the
factor-two step in `thm:finite-recovery`, not its other terminal, singularity,
or posterior equivalences. No finite-POMDP specialization is imported.
-/

namespace IdExp

open Finset Set Filter Topology

noncomputable section

variable {Θ X : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ] [Fintype X]

/-- Full revelation of the finite world label, as the identity Dirac
experiment already used by the finite-deficiency development. -/
def finiteLabelExperiment (Θ : Type*) : FiniteExperiment Θ Θ := diracExp id

omit [Nonempty Θ] [DecidableEq Θ] in
theorem finiteLabelExperiment_valid : IsFiniteExperiment (finiteLabelExperiment Θ) :=
  diracExp_valid id

/-- The actual probability of an incorrect deterministic label in one world. -/
def deterministicLabelError (E : FiniteExperiment Θ X) (f : X → Θ) (θ : Θ) : ℝ :=
  ∑ x, if f x ≠ θ then E θ x else 0

/-- Worst-world error of a deterministic decoder. -/
def worstDeterministicLabelError (E : FiniteExperiment Θ X) (f : X → Θ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (deterministicLabelError E f)

/-- The finite minimum over every deterministic decoder, with no restriction
to any preselected decoding family. -/
def deterministicLabelMinimaxError (E : FiniteExperiment Θ X) : ℝ := by
  classical
  exact (Finset.univ : Finset (X → Θ)).inf' Finset.univ_nonempty
    (worstDeterministicLabelError E)

theorem deterministicLabelError_le_worst (E : FiniteExperiment Θ X) (f : X → Θ) (θ : Θ) :
    deterministicLabelError E f θ ≤ worstDeterministicLabelError E f :=
  Finset.le_sup' _ (Finset.mem_univ θ)

theorem worstDeterministicLabelError_le (E : FiniteExperiment Θ X) (f : X → Θ) (c : ℝ)
    (h : ∀ θ, deterministicLabelError E f θ ≤ c) :
    worstDeterministicLabelError E f ≤ c :=
  Finset.sup'_le _ _ (fun θ _ => h θ)

theorem deterministicLabelMinimaxError_le_decoder (E : FiniteExperiment Θ X) (f : X → Θ) :
    deterministicLabelMinimaxError E ≤ worstDeterministicLabelError E f := by
  classical
  exact Finset.inf'_le _ (Finset.mem_univ f)

/-- The displayed deterministic minimum is attained by a genuine decoding
function, because its entire search space is finite and nonempty. -/
theorem exists_deterministicLabelMinimizer (E : FiniteExperiment Θ X) :
    ∃ f : X → Θ, worstDeterministicLabelError E f = deterministicLabelMinimaxError E := by
  classical
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (X → Θ)).Nonempty)
    (worstDeterministicLabelError E)
  exact ⟨f, hf.symm⟩

/-- Operational interpretation of the minimum: a bound holds exactly when
one deterministic decoder achieves it simultaneously in every world. -/
theorem deterministicLabelMinimaxError_le_iff (E : FiniteExperiment Θ X) (c : ℝ) :
    deterministicLabelMinimaxError E ≤ c ↔
      ∃ f : X → Θ, ∀ θ, deterministicLabelError E f θ ≤ c := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := exists_deterministicLabelMinimizer E
    refine ⟨f, fun θ => ?_⟩
    exact (deterministicLabelError_le_worst E f θ).trans (hf.le.trans h)
  · rintro ⟨f, hf⟩
    exact (deterministicLabelMinimaxError_le_decoder E f).trans
      (worstDeterministicLabelError_le E f c hf)

omit [Fintype Θ] [Nonempty Θ] in
theorem deterministicLabelError_nonneg (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (f : X → Θ) (θ : Θ) :
    0 ≤ deterministicLabelError E f θ := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact (hE θ).1 x
  · exact le_rfl

theorem deterministicLabelMinimaxError_nonneg (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) : 0 ≤ deterministicLabelMinimaxError E := by
  obtain ⟨f, hf⟩ := exists_deterministicLabelMinimizer E
  exact (deterministicLabelError_nonneg E hE f (Classical.arbitrary Θ)).trans
    ((deterministicLabelError_le_worst E f (Classical.arbitrary Θ)).trans_eq hf)

/-! ## TV to a label is exactly the probability of incorrect decoding -/

omit [Nonempty Θ] in
theorem decodeErr_finiteLabel_eq_one_sub (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (G : X → Θ → ℝ)
    (hG : G ∈ stochasticRules X Θ) (θ : Θ) :
    decodeErr E (finiteLabelExperiment Θ) G θ = 1 - finiteDecisionLaw E G θ θ := by
  classical
  have hp := finiteDecisionLaw_valid E hE G hG θ
  have hpθ : finiteDecisionLaw E G θ θ ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun y _ => hp.1 y) (Finset.mem_univ θ)
  have hterm (y : Θ) :
      |finiteDecisionLaw E G θ y - finiteLabelExperiment Θ θ y| =
        finiteDecisionLaw E G θ y +
          if y = θ then 1 - 2 * finiteDecisionLaw E G θ θ else 0 := by
    by_cases hy : y = θ
    · subst y
      simp only [finiteLabelExperiment, diracExp_apply, id_eq, if_true]
      rw [abs_of_nonpos (by linarith)]
      ring
    · simp [finiteLabelExperiment, diracExp_apply, hy, abs_of_nonneg (hp.1 y)]
  change (1 / 2 : ℝ) * ∑ y,
    |finiteDecisionLaw E G θ y - finiteLabelExperiment Θ θ y| = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hp.2]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

omit [Nonempty Θ] in
/-- Randomized exact-label error is the source-weighted mass the decoder
assigns to labels other than the true one. -/
theorem decodeErr_finiteLabel_eq_weighted_error (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (G : X → Θ → ℝ)
    (hG : G ∈ stochasticRules X Θ) (θ : Θ) :
    decodeErr E (finiteLabelExperiment Θ) G θ = ∑ x, E θ x * (1 - G x θ) := by
  rw [decodeErr_finiteLabel_eq_one_sub E hE G hG θ]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, (hE θ).2, finiteDecisionLaw]

omit [Nonempty Θ] [DecidableEq Θ] [Fintype X] in
theorem deterministicLabelRule_valid (f : X → Θ) :
    diracExp f ∈ stochasticRules X Θ :=
  fun x _ => diracExp_valid f x

/-- Embedding a deterministic decoder into the stochastic rules preserves
its literal probability of error. -/
theorem deterministicLabelError_eq_decodeErr (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (f : X → Θ) (θ : Θ) :
    deterministicLabelError E f θ = decodeErr E (finiteLabelExperiment Θ) (diracExp f) θ := by
  rw [decodeErr_finiteLabel_eq_weighted_error E hE _ (deterministicLabelRule_valid f) θ]
  unfold deterministicLabelError
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f x = θ
  · simp [diracExp_apply, hx]
  · simp [diracExp_apply, hx, Ne.symm hx]

/-- Randomization can only improve the minimax error, because deterministic
decoders are included in the existing deficiency infimum. -/
theorem finiteLabelDeficiency_le_deterministicMinimaxError
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    finiteDeficiency E (finiteLabelExperiment Θ) ≤ deterministicLabelMinimaxError E := by
  obtain ⟨f, hf⟩ := exists_deterministicLabelMinimizer E
  apply finiteDeficiency_le_of_decoder E (finiteLabelExperiment Θ) (diracExp f)
    (deterministicLabelRule_valid f)
  intro θ
  rw [← deterministicLabelError_eq_decodeErr E hE f θ]
  exact (deterministicLabelError_le_worst E f θ).trans_eq hf

/-! ## Largest-entry rounding of a stochastic label decoder -/

/-- Choose any largest-probability label in each stochastic decoder row.
The source is finite, so every such function is an admissible deterministic
finite-signal decoder; no measurable selection theorem is needed. -/
def roundedLabelDecoder (G : X → Θ → ℝ) : X → Θ :=
  fun x => Classical.choose (Finset.exists_max_image Finset.univ (G x) Finset.univ_nonempty)

omit [DecidableEq Θ] [Fintype X] in
theorem roundedLabelDecoder_max (G : X → Θ → ℝ) (x : X) (θ : Θ) :
    G x θ ≤ G x (roundedLabelDecoder G x) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (G x)
    Finset.univ_nonempty)).2 θ (Finset.mem_univ θ)

omit [DecidableEq Θ] in
/-- A wrong largest-entry choice forces the true label's probability to be
at most one half, even with ties and any number of labels. -/
theorem roundedLabelDecoder_wrong_le_half (G : X → Θ → ℝ)
    (hG : G ∈ stochasticRules X Θ) (x : X) (θ : Θ)
    (hwrong : roundedLabelDecoder G x ≠ θ) : G x θ ≤ 1 / 2 := by
  have hs := stochasticRules_add_le_one hG x (Ne.symm hwrong)
  have hm := roundedLabelDecoder_max G x θ
  linarith

/-- Argmax rounding costs at most a factor of two in every individual world. -/
theorem roundedLabelDecoder_error_le_two (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (G : X → Θ → ℝ)
    (hG : G ∈ stochasticRules X Θ) (θ : Θ) :
    deterministicLabelError E (roundedLabelDecoder G) θ ≤
      2 * decodeErr E (finiteLabelExperiment Θ) G θ := by
  rw [decodeErr_finiteLabel_eq_weighted_error E hE G hG θ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hx := (hE θ).1 x
  by_cases hwrong : roundedLabelDecoder G x ≠ θ
  · simp only [if_pos hwrong]
    have hhalf := roundedLabelDecoder_wrong_le_half G hG x θ hwrong
    nlinarith
  · simp only [if_neg hwrong]
    have hle := stochasticRules_le_one hG x θ
    nlinarith

/-- **Factor-two rounding theorem.** The deterministic minimax error is at
most twice the actual randomized exact-label deficiency. Stochastic
attainment is invoked as a proved theorem, not an extra hypothesis. -/
theorem deterministicMinimaxError_le_two_finiteLabelDeficiency
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    deterministicLabelMinimaxError E ≤ 2 * finiteDeficiency E (finiteLabelExperiment Θ) := by
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency E (finiteLabelExperiment Θ)
  apply (deterministicLabelMinimaxError_le_decoder E (roundedLabelDecoder G)).trans
  apply worstDeterministicLabelError_le
  intro θ
  exact (roundedLabelDecoder_error_le_two E hE G hG θ).trans
    (mul_le_mul_of_nonneg_left (herr θ) (by norm_num))

/-- Both inequalities in the paper's deterministic/randomized comparison. -/
theorem deterministic_randomized_label_error_comparison
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    finiteDeficiency E (finiteLabelExperiment Θ) ≤ deterministicLabelMinimaxError E ∧
      deterministicLabelMinimaxError E ≤ 2 * finiteDeficiency E (finiteLabelExperiment Θ) :=
  ⟨finiteLabelDeficiency_le_deterministicMinimaxError E hE,
    deterministicMinimaxError_le_two_finiteLabelDeficiency E hE⟩

/-! ## Time-varying finite signals, including causal prefixes -/

theorem tendsto_deterministicMinimaxError_iff_finiteLabelDeficiency
    {S : ℕ → Type*} [∀ t, Fintype (S t)]
    (E : (t : ℕ) → FiniteExperiment Θ (S t)) (hE : ∀ t, IsFiniteExperiment (E t)) :
    Tendsto (fun t => deterministicLabelMinimaxError (E t)) atTop (𝓝 0) ↔
      Tendsto (fun t => finiteDeficiency (E t) (finiteLabelExperiment Θ)) atTop (𝓝 0) := by
  constructor
  · intro h
    exact squeeze_zero
      (fun t => finiteDeficiency_nonneg_of_fintype (E t) (finiteLabelExperiment Θ))
      (fun t => finiteLabelDeficiency_le_deterministicMinimaxError (E t) (hE t)) h
  · intro h
    have htwo : Tendsto (fun t => 2 * finiteDeficiency (E t) (finiteLabelExperiment Θ))
        atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul h
    exact squeeze_zero
      (fun t => deterministicLabelMinimaxError_nonneg (E t) (hE t))
      (fun t => deterministicMinimaxError_le_two_finiteLabelDeficiency (E t) (hE t)) htwo

/-- The same zero-limit property for the actual finite causal prefix
experiments, whose source alphabet grows with time. -/
theorem causalPrefix_deterministic_randomized_label_tendsto_zero_iff
    {A O : Type*} [Fintype A] [Fintype O]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π) :
    Tendsto (fun t => deterministicLabelMinimaxError (causalFiniteExperiment π Qs t))
        atTop (𝓝 0) ↔
      Tendsto (fun t => finiteDeficiency (causalFiniteExperiment π Qs t)
        (finiteLabelExperiment Θ)) atTop (𝓝 0) :=
  tendsto_deterministicMinimaxError_iff_finiteLabelDeficiency
    (fun t => causalFiniteExperiment π Qs t) (fun t => causalFiniteExperiment_valid π hπ Qs hQ t)

end
end IdExp
