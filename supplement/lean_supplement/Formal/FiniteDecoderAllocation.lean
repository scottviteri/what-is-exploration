import Formal.BoundedApproachCertificate

/-!
# Exact linear decoder allocations and deficiency sublevels

For nonnegative source weights w, nonnegative allocations with row totals w
are exactly w times unrestricted stochastic decoder rows. Division at positive
weights and a uniform zero-weight fallback reconstruct the decoder. This
turns the absolute-error slack system into exact deficiency sublevels,
including equality at the infimum and arbitrary finite weighted libraries.
-/
namespace IdExp
open Finset Set
noncomputable section
set_option linter.unusedSectionVars false

section Allocation
variable {X Y Θ : Type*} [Fintype X] [Fintype Y] [Nonempty Y]

/-- Allocation rows sum to the source's realization weight, not to one. -/
structure IsDecoderAllocation (w : X → ℝ) (r : X → Y → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ r x y
  sum : ∀ x, ∑ y, r x y = w x

def decoderOfAllocation (w : X → ℝ) (r : X → Y → ℝ) : X → Y → ℝ :=
  fun x y => if w x = 0 then (Fintype.card Y : ℝ)⁻¹ else r x y / w x

theorem decoderOfAllocation_stochastic (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (r : X → Y → ℝ) (hr : IsDecoderAllocation w r) :
    decoderOfAllocation w r ∈ stochasticRules X Y := by
  intro x _
  by_cases hz : w x = 0
  · have hc : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    constructor
    · intro y; simp only [decoderOfAllocation, if_pos hz]; positivity
    · simp [decoderOfAllocation, hz, hc]
  · constructor
    · intro y
      simp only [decoderOfAllocation, if_neg hz]
      exact div_nonneg (hr.nonneg x y) (hw x)
    · simp only [decoderOfAllocation, if_neg hz, ← Finset.sum_div, hr.sum, div_self hz]

theorem weight_mul_decoderOfAllocation (w : X → ℝ)
    (r : X → Y → ℝ) (hr : IsDecoderAllocation w r) (x : X) (y : Y) :
    w x * decoderOfAllocation w r x y = r x y := by
  classical
  by_cases hz : w x = 0
  · have hle : r x y ≤ w x := by
      rw [← hr.sum]
      exact Finset.single_le_sum (fun z _ => hr.nonneg x z) (Finset.mem_univ y)
    have hrz : r x y = 0 := le_antisymm (by simpa [hz] using hle) (hr.nonneg x y)
    simp [hz, hrz]
  · simp only [decoderOfAllocation, if_neg hz]
    exact mul_div_cancel₀ _ hz

/-- Allocations are precisely weighted stochastic rows, including zero weights. -/
theorem isDecoderAllocation_iff (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (r : X → Y → ℝ) :
    IsDecoderAllocation w r ↔ ∃ G ∈ stochasticRules X Y,
      r = fun x y => w x * G x y := by
  constructor
  · intro hr
    refine ⟨decoderOfAllocation w r, decoderOfAllocation_stochastic w hw r hr, ?_⟩
    funext x y
    exact (weight_mul_decoderOfAllocation w r hr x y).symm
  · rintro ⟨G, hG, rfl⟩
    constructor
    · intro x y; exact mul_nonneg (hw x) ((hG x (mem_univ x)).1 y)
    · intro x
      rw [← Finset.mul_sum, (hG x (mem_univ x)).2, mul_one]

/-- A fixed controlled-likelihood matrix multiplied by policy weights. -/
def allocationSource (p : Θ → X → ℝ) (w : X → ℝ) : FiniteExperiment Θ X :=
  fun θ x => w x * p θ x

/-- Decoded output is linear in allocation variables. -/
def allocationOutput (p : Θ → X → ℝ) (r : X → Y → ℝ) : Θ → Y → ℝ :=
  fun θ y => ∑ x, p θ x * r x y

theorem allocationSource_decoded (p : Θ → X → ℝ) (w : X → ℝ) (G : X → Y → ℝ) :
    finiteDecisionLaw (allocationSource p w) G =
      allocationOutput p (fun x y => w x * G x y) := by
  funext θ y
  unfold finiteDecisionLaw allocationSource allocationOutput
  apply Finset.sum_congr rfl
  intro x _
  ring

end Allocation

section Deficiency
variable {X Y Θ : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
  [Fintype Θ] [Nonempty Θ]

/-- Exact TV formulation at every real threshold, including the attained boundary. -/
theorem finiteDeficiency_le_iff_allocation_tv (p : Θ → X → ℝ)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (T : FiniteExperiment Θ Y) (c : ℝ) :
    finiteDeficiency (allocationSource p w) T ≤ c ↔
      ∃ r : X → Y → ℝ, IsDecoderAllocation w r ∧
        ∀ θ, finiteTV (allocationOutput p r θ) (T θ) ≤ c := by
  constructor
  · intro hc
    obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency (allocationSource p w) T
    refine ⟨fun x y => w x * G x y,
      (isDecoderAllocation_iff w hw _).mpr ⟨G, hG, rfl⟩, ?_⟩
    intro θ
    rw [← allocationSource_decoded]
    exact (herr θ).trans hc
  · rintro ⟨r, hr, herr⟩
    obtain ⟨G, hG, rfl⟩ := (isDecoderAllocation_iff w hw r).mp hr
    apply finiteDeficiency_le_of_decoder _ _ G hG c
    intro θ
    change finiteTV (finiteDecisionLaw (allocationSource p w) G θ) (T θ) ≤ c
    rw [allocationSource_decoded]
    exact herr θ

/-- The literal nonnegative allocation and two-sided TV-slack constraints. -/
structure AllocationSlackCertificate (p : Θ → X → ℝ) (w : X → ℝ)
    (T : FiniteExperiment Θ Y) (d : ℝ) (r : X → Y → ℝ) (z : Θ → Y → ℝ) : Prop where
  allocation : IsDecoderAllocation w r
  slack_nonneg : ∀ θ y, 0 ≤ z θ y
  error_nonneg : 0 ≤ d
  lower : ∀ θ y, -z θ y ≤ allocationOutput p r θ y - T θ y
  upper : ∀ θ y, allocationOutput p r θ y - T θ y ≤ z θ y
  budget : ∀ θ, (1 / 2 : ℝ) * ∑ y, z θ y ≤ d

/-- Exact LP sublevels: decoder allocations are not a relaxation. No strict
positivity of source weights, target probabilities, or threshold is assumed. -/
theorem finiteDeficiency_le_iff_allocation_slacks (p : Θ → X → ℝ)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (T : FiniteExperiment Θ Y) (c : ℝ) :
    finiteDeficiency (allocationSource p w) T ≤ c ↔
      ∃ (r : X → Y → ℝ) (z : Θ → Y → ℝ), AllocationSlackCertificate p w T c r z := by
  constructor
  · intro hc
    obtain ⟨r, hr, herr⟩ := (finiteDeficiency_le_iff_allocation_tv p w hw T c).mp hc
    refine ⟨r, fun θ y => |allocationOutput p r θ y - T θ y|, hr,
      fun θ y => abs_nonneg _, (finiteDeficiency_nonneg_of_fintype _ _).trans hc,
      fun θ y => neg_abs_le _, fun θ y => le_abs_self _, ?_⟩
    exact herr
  · rintro ⟨r, z, hz⟩
    apply (finiteDeficiency_le_iff_allocation_tv p w hw T c).mpr
    refine ⟨r, hz.allocation, fun θ => ?_⟩
    apply le_trans _ (hz.budget θ)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact Finset.sum_le_sum fun y _ => abs_le.mpr ⟨hz.lower θ y, hz.upper θ y⟩

end Deficiency

section Library
variable {X Θ J : Type*} {Y : J → Type*}
  [Fintype X] [Fintype Θ] [Nonempty Θ] [Fintype J]
  [∀ j, Fintype (Y j)] [∀ j, Nonempty (Y j)]

/-- Exact weighted finite-library sublevels, with heterogeneous target alphabets
and arbitrary nonnegative unnormalized weights. Every target has its own
world-independent stochastic decoder, sharing the acquired source signal. -/
theorem weightedDeficiency_le_iff_allocation_slacks
    (p : Θ → X → ℝ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (v : J → ℝ) (hv : ∀ j, 0 ≤ v j) (c : ℝ) :
    (∑ j, v j * finiteDeficiency (allocationSource p w) (T j)) ≤ c ↔
      ∃ (d : J → ℝ) (r : ∀ j, X → Y j → ℝ) (z : ∀ j, Θ → Y j → ℝ),
        (∀ j, AllocationSlackCertificate p w (T j) (d j) (r j) (z j)) ∧
        (∑ j, v j * d j) ≤ c := by
  constructor
  · intro hc
    have hex : ∀ j, ∃ (r : X → Y j → ℝ) (z : Θ → Y j → ℝ),
        AllocationSlackCertificate p w (T j)
          (finiteDeficiency (allocationSource p w) (T j)) r z := by
      intro j
      exact (finiteDeficiency_le_iff_allocation_slacks p w hw (T j) _).mp le_rfl
    choose r z hz using hex
    exact ⟨fun j => finiteDeficiency (allocationSource p w) (T j), r, z, hz, hc⟩
  · rintro ⟨d, r, z, hz, hc⟩
    apply le_trans _ hc
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      ((finiteDeficiency_le_iff_allocation_slacks p w hw (T j) (d j)).mpr ⟨r j, z j, hz j⟩)
      (hv j)

end Library
end
end IdExp
