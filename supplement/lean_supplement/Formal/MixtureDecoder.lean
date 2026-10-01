import Formal.FiniteTV

/-!
# The mixture-decoder step of finite-horizon universality

Theorem "Finite-horizon universality" (`Paper/draft/main.tex`,
`thm:finite-universality`) / Proposition "Worst-test deficiency is the distance to the
finite-horizon attainable region" (`TheoryDocs/native_test_geometry.tex`,
`prop:finite-horizon`) states
`Γ_{≤n}(E) = sup { δ(E, K_{σ,t}) : σ a policy, t ≤ n }`.

Its nontrivial inequality mixes decoders.  By Kuhn's theorem a randomized policy's
acquired experiment is a world-independent convex combination of the experiments of
deterministic contingency plans, `K_{σ,n}(Q) = Σ_τ w_σ(τ) K_{τ,n}(Q)`; given decoders
`G_τ`, each simulating `K_{τ,n}` from `E` with worst-world total-variation error at most
`c`, the mixture decoder `G = Σ_τ w_σ(τ) G_τ` (draw the label, run that component,
forget the label) simulates `K_{σ,n}` within the same bound `c`, by convexity of total
variation.  This file machine-checks that step in the finite-matrix model of
`FiniteBlackwell.lean`; `Kuhn.lean` checks the causal policy's product weights and
finite-event marginals. `CausalUniversality.lean` now closes the causal wrapper: it
identifies the induced full-trace mixture, proves lossless observation/action
relabeling for deterministic plans, and packages the observation-only decoder
implication for an arbitrary behavioral policy.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset

variable {Θ X Y ι : Type*} [Fintype X] [Fintype Y] [Fintype ι]

/-- Total-variation error, at world `θ`, of decoding the target `F` from `E` through the
stochastic matrix `G`: half the ℓ¹ distance between the decoded law `(E θ) ⋅ G` and
`F θ`. -/
noncomputable def decodeErr (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (θ : Θ) : ℝ :=
  (1 / 2) * ∑ y, |(∑ x, E θ x * G x y) - F θ y|

theorem decodeErr_nonneg (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (θ : Θ) : 0 ≤ decodeErr E F G θ :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => abs_nonneg _)

/-- Decoder error between valid finite experiments is at most one. -/
theorem decodeErr_le_one (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (θ : Θ) :
    decodeErr E F G θ ≤ 1 := by
  change finiteTV (finiteDecisionLaw E G θ) (F θ) ≤ 1
  exact finiteTV_le_one_of_isDist _ _
    ((finiteDecisionLaw_valid E hE G hG) θ) (hF θ)

/-- Post-processing both a decoded law and its target by the same stochastic
rule cannot increase decoder error. -/
theorem decodeErr_stochasticRuleComp_le
    {Z : Type*} [Fintype Z]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (H : Y → Z → ℝ)
    (hH : H ∈ stochasticRules Y Z) (θ : Θ) :
    decodeErr E (finiteDecisionLaw F H) (stochasticRuleComp G H) θ ≤
      decodeErr E F G θ := by
  change finiteTV
      (finiteDecisionLaw E (stochasticRuleComp G H) θ)
      (finiteDecisionLaw F H θ) ≤
    finiteTV (finiteDecisionLaw E G θ) (F θ)
  rw [finiteDecisionLaw_stochasticRuleComp]
  exact finiteTV_postprocess_le (finiteDecisionLaw E G θ) (F θ) H hH


/-- A convex combination of stochastic decoders is a stochastic decoder. -/
theorem mixtureDecoder_mem_stochasticRules {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    {G : ι → X → Y → ℝ} (hG : ∀ τ, G τ ∈ stochasticRules X Y) :
    (fun x y => ∑ τ, w τ * G τ x y) ∈ stochasticRules X Y := by
  intro x _
  constructor
  · intro y
    exact Finset.sum_nonneg fun τ _ =>
      mul_nonneg (hw.1 τ) ((hG τ x (Set.mem_univ x)).1 y)
  · rw [Finset.sum_comm]
    calc
      ∑ τ, ∑ y, w τ * G τ x y = ∑ τ, w τ * ∑ y, G τ x y := by
        simp [Finset.mul_sum]
      _ = ∑ τ, w τ * 1 := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [(hG τ x (Set.mem_univ x)).2]
      _ = 1 := by simpa using hw.2

/-- **The mixture-decoder bound.**  If the target experiment is a world-independent
convex combination `F θ = Σ_τ w τ • Fs τ θ` of experiments each decodable from `E` with
worst-world error at most `c`, then the mixed decoder `Σ_τ w τ • G τ` decodes the
mixture within the same bound.  This is the nontrivial inequality of the finite-horizon
universality theorem, applied after Kuhn's decomposition of a randomized policy. -/
theorem decodeErr_mixture_le (E : FiniteExperiment Θ X)
    (Fs : ι → FiniteExperiment Θ Y) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    (G : ι → X → Y → ℝ) {c : ℝ}
    (hG : ∀ τ θ, decodeErr E (Fs τ) (G τ) θ ≤ c) (θ : Θ) :
    decodeErr E (fun θ' y => ∑ τ, w τ * Fs τ θ' y)
      (fun x y => ∑ τ, w τ * G τ x y) θ ≤ c := by
  have hswap : ∀ y, (∑ x, E θ x * ∑ τ, w τ * G τ x y)
      = ∑ τ, w τ * ∑ x, E θ x * G τ x y := by
    intro y
    calc
      ∑ x, E θ x * ∑ τ, w τ * G τ x y
          = ∑ x, ∑ τ, w τ * (E θ x * G τ x y) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun τ _ => by ring
      _ = ∑ τ, ∑ x, w τ * (E θ x * G τ x y) := Finset.sum_comm
      _ = ∑ τ, w τ * ∑ x, E θ x * G τ x y := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            rw [Finset.mul_sum]
  calc
    decodeErr E (fun θ' y => ∑ τ, w τ * Fs τ θ' y)
        (fun x y => ∑ τ, w τ * G τ x y) θ
        = (1 / 2) * ∑ y, |∑ τ, w τ * ((∑ x, E θ x * G τ x y) - Fs τ θ y)| := by
          unfold decodeErr
          congr 1
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hswap y, ← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl fun τ _ => (mul_sub _ _ _).symm
    _ ≤ (1 / 2) * ∑ y, ∑ τ, w τ * |(∑ x, E θ x * G τ x y) - Fs τ θ y| := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum fun y _ => ?_
          calc
            |∑ τ, w τ * ((∑ x, E θ x * G τ x y) - Fs τ θ y)|
                ≤ ∑ τ, |w τ * ((∑ x, E θ x * G τ x y) - Fs τ θ y)| :=
                  Finset.abs_sum_le_sum_abs _ _
            _ = ∑ τ, w τ * |(∑ x, E θ x * G τ x y) - Fs τ θ y| := by
                  refine Finset.sum_congr rfl fun τ _ => ?_
                  rw [abs_mul, abs_of_nonneg (hw.1 τ)]
    _ = ∑ τ, w τ * decodeErr E (Fs τ) (G τ) θ := by
          unfold decodeErr
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [← Finset.mul_sum]
          ring
    _ ≤ ∑ τ, w τ * c :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hG τ θ) (hw.1 τ)
    _ = c := by rw [← Finset.sum_mul, hw.2, one_mul]

/-- Convex mixtures of two families have no more TV than the worst
component pair. The weights are identical in the two worlds. -/
theorem finiteTV_mixture_le {I X : Type*} [Fintype I] [Fintype X]
    (p q : I → X → ℝ) (w : I → ℝ) (hw : IsDist w)
    (c : ℝ) (h : ∀ i, finiteTV (p i) (q i) ≤ c) :
    finiteTV (fun x => ∑ i, w i * p i x) (fun x => ∑ i, w i * q i x) ≤ c := by
  have he := decodeErr_mixture_le
    (fun (_ : Unit) (_ : Unit) => (1 : ℝ))
    (fun i (_ : Unit) => q i) hw (fun i (_ : Unit) => p i)
    (c := c) (fun i _ => by simpa [decodeErr, finiteTV] using h i) ()
  simpa [decodeErr, finiteTV] using he

/-- Packaged form: a stochastic decoder within `c` for every component of a
world-independent mixture yields one stochastic decoder within `c` for the mixture. -/
theorem exists_mixture_decoder (E : FiniteExperiment Θ X)
    (Fs : ι → FiniteExperiment Θ Y) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) {c : ℝ}
    (h : ∀ τ, ∃ G ∈ stochasticRules X Y, ∀ θ, decodeErr E (Fs τ) G θ ≤ c) :
    ∃ G ∈ stochasticRules X Y,
      ∀ θ, decodeErr E (fun θ' y => ∑ τ, w τ * Fs τ θ' y) G θ ≤ c := by
  choose G hGmem hGerr using h
  exact ⟨_, mixtureDecoder_mem_stochasticRules hw hGmem,
    fun θ => decodeErr_mixture_le E Fs hw G hGerr θ⟩

end IdExp
