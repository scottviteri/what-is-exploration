import Formal.ProfileSpace
import Formal.WeightedObjectiveRegularity

/-!
# Continuous scores on closed attainable profile sets

The analytic part of `prop:capability-profile-scalarization`. The attainable
family is arbitrary and need not be closed, and the zero profile need not be
attained. Scores are continuous only on its closure, as in the paper.
-/

namespace IdExp

open Set Filter Topology

noncomputable section

variable {P : Type*} [Nonempty P]

/-- The closure of the actually attainable profiles. -/
def attainableProfileClosure (ℓ : P → ProfileCube) : Set ProfileCube :=
  closure (range ℓ)

omit [Nonempty P] in
/-- A continuous score on the closed profile set is bounded on the feasible family. -/
theorem profileScore_bddAbove (ℓ : P → ProfileCube) (f : ProfileCube → ℝ)
    (hf : ContinuousOn f (attainableProfileClosure ℓ)) :
    BddAbove (range (f ∘ ℓ)) := by
  have hc : IsCompact (attainableProfileClosure ℓ) := isClosed_closure.isCompact
  apply (hc.bddAbove_image hf).mono
  rintro _ ⟨π, rfl⟩
  exact ⟨ℓ π, subset_closure (mem_range_self π), rfl⟩

/-- Every profile-limit score is at most the supremum of feasible scores. -/
theorem profileScore_le_sup (ℓ : P → ProfileCube) (f : ProfileCube → ℝ)
    (hf : ContinuousOn f (attainableProfileClosure ℓ)) {p : ProfileCube}
    (hp : p ∈ attainableProfileClosure ℓ) : f p ≤ sSup (range (f ∘ ℓ)) := by
  have him : f p ∈ closure (range (f ∘ ℓ)) := by
    have h := hf.image_closure ⟨p, hp, rfl⟩
    have heq : f '' range ℓ = range (f ∘ ℓ) := by ext; simp
    rwa [heq] at h
  exact (closure_minimal (fun x hx => le_csSup (profileScore_bddAbove ℓ f hf) hx)
    isClosed_Iic) him

/-- The supremum on the feasible family is attained on its profile closure. -/
theorem exists_profileScore_eq_sup (ℓ : P → ProfileCube) (f : ProfileCube → ℝ)
    (hf : ContinuousOn f (attainableProfileClosure ℓ)) :
    ∃ p ∈ attainableProfileClosure ℓ, f p = sSup (range (f ∘ ℓ)) := by
  have hc : IsCompact (attainableProfileClosure ℓ) := isClosed_closure.isCompact
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn
    (Set.range_nonempty ℓ).closure hf
  refine ⟨p, hp, le_antisymm (profileScore_le_sup ℓ f hf hp) ?_⟩
  apply csSup_le (range_nonempty _)
  rintro _ ⟨π, rfl⟩
  exact hmax (subset_closure (mem_range_self π))

/-- The positive weighted profile score, on the product cube. -/
def weightedProfileScore (w : ℕ → ℝ) : ProfileCube → ℝ :=
  weightedScore w (fun j p => (p j : ℝ))

theorem continuous_weightedProfileScore {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hsum : Summable w) :
    Continuous (weightedProfileScore w) :=
  continuous_weightedScore hw hsum (fun j p => (p j).2)
    (fun j => continuous_subtype_val.comp (continuous_apply j))

@[simp] theorem weightedProfileScore_zero (w : ℕ → ℝ) :
    weightedProfileScore w zeroProfile = 1 := by
  simp [weightedProfileScore, weightedScore, zeroProfile]

/-- The coordinate regret bound does not require zero to be approachable. -/
theorem profile_coordinate_le_weighted_regret {w : ℕ → ℝ}
    (hw : ∀ j, 0 < w j) (hsum : Summable w) (p : ProfileCube) (j : ℕ) :
    (p j : ℝ) ≤ (1 - weightedProfileScore w p) / w j := by
  apply (le_div_iff₀ (hw j)).2
  have hs := summable_weightedScore_loss (fun j => (hw j).le) hsum
    (fun j (p : ProfileCube) => (p j).2) p
  have hle := hs.le_tsum j (fun k _ => mul_nonneg (hw k).le (p k).2.1)
  dsimp [weightedProfileScore, weightedScore]
  nlinarith

/-- Approachable zero gives supremum one even when no feasible policy completes. -/
theorem weightedProfileScore_sup_eq_one (ℓ : P → ProfileCube) {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    (hz : zeroProfile ∈ attainableProfileClosure ℓ) :
    sSup (range (weightedProfileScore w ∘ ℓ)) = 1 := by
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨π, rfl⟩
    dsimp [Function.comp_def, weightedProfileScore, weightedScore]
    have : 0 ≤ ∑' j, w j * (ℓ π j : ℝ) :=
      tsum_nonneg (fun j => mul_nonneg (hw j) (ℓ π j).2.1)
    linarith
  · simpa using profileScore_le_sup ℓ (weightedProfileScore w)
      (continuous_weightedProfileScore hw hsum).continuousOn hz

/-- An explicit targetwise tolerance; no common collection deadline is asserted. -/
theorem weightedProfileScore_calibration (ℓ : P → ProfileCube) {w : ℕ → ℝ}
    (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (hz : zeroProfile ∈ attainableProfileClosure ℓ) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ π : P,
      sSup (range (weightedProfileScore w ∘ ℓ)) - weightedProfileScore w (ℓ π) ≤ η →
      (ℓ π j : ℝ) < ε := by
  refine ⟨w j * ε / 2, div_pos (mul_pos (hw j) hε) (by norm_num), ?_⟩
  intro π hπ
  rw [weightedProfileScore_sup_eq_one ℓ (fun j => (hw j).le) hsum hz] at hπ
  have hcoord := profile_coordinate_le_weighted_regret hw hsum (ℓ π) j
  have hsmall : (1 - weightedProfileScore w (ℓ π)) / w j < ε := by
    apply (div_lt_iff₀ (hw j)).2
    nlinarith [mul_pos (hw j) hε]
  exact hcoord.trans_lt hsmall

end
end IdExp
