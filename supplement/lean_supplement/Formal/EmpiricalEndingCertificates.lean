import Formal.DualCertificate

/-! Exact rational finite-experiment bounds for empirical-ending diagnostics.
The bridge does not verify solvers, policy optimality, target enumeration, or
bindings to floating-point files. Those are separate evidence obligations. -/
namespace IdExp.EmpiricalEnding
open Finset Set
variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]

def RatRows (E : Θ → X → ℚ) : Prop :=
  ∀ θ, (∀ x, 0 ≤ E θ x) ∧ ∑ x, E θ x = 1

def realRows (E : Θ → X → ℚ) : FiniteExperiment Θ X :=
  fun θ x => (E θ x : ℝ)

theorem realRows_valid (E : Θ → X → ℚ) (hE : RatRows E) :
    IsFiniteExperiment (realRows E) := by
  intro θ
  constructor
  · intro x
    change (0 : ℝ) ≤ (E θ x : ℝ)
    exact_mod_cast (hE θ).1 x
  · change (∑ x, (E θ x : ℝ)) = 1
    exact_mod_cast (hE θ).2

/-- A checked rational lower witness bounds the infimum over every real
stochastic decoder, with no optimizer premise. -/
theorem rational_lower_bound [Nonempty Θ] [Nonempty Y]
    (E : Θ → X → ℚ) (F : Θ → Y → ℚ)
    (hE : RatRows E) (hF : RatRows F)
    (lambda : Θ → ℚ) (hl0 : ∀ θ, 0 ≤ lambda θ)
    (hl1 : ∑ θ, lambda θ = 1)
    (mu : Θ → Y → ℚ)
    (hm0 : ∀ θ y, 0 ≤ mu θ y)
    (hml : ∀ θ y, mu θ y ≤ lambda θ)
    (floor : X → ℚ) (hf : ∀ x y, floor x ≤ ∑ θ, mu θ y * E θ x)
    (lower : ℚ) (hv : lower ≤ (∑ x, floor x) - ∑ θ, ∑ y, mu θ y * F θ y) :
    (lower : ℝ) ≤ finiteDeficiency (realRows E) (realRows F) := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty (realRows E) (realRows F))
  rintro c ⟨G, hG, hc⟩
  have hl : IsDist (fun θ => (lambda θ : ℝ)) := by
    constructor
    · intro θ; change (0 : ℝ) ≤ (lambda θ : ℝ); exact_mod_cast hl0 θ
    · change (∑ θ, (lambda θ : ℝ)) = 1
      exact_mod_cast hl1
  have hmr0 : ∀ θ y, (0 : ℝ) ≤ (mu θ y : ℝ) := by
    intro θ y; exact_mod_cast hm0 θ y
  have hmrl : ∀ θ y, (mu θ y : ℝ) ≤ (lambda θ : ℝ) := by
    intro θ y; exact_mod_cast hml θ y
  have hfr : ∀ x y, (floor x : ℝ) ≤ ∑ θ, (mu θ y : ℝ) * realRows E θ x := by
    intro x y
    change (floor x : ℝ) ≤ ∑ θ, (mu θ y : ℝ) * (E θ x : ℝ)
    exact_mod_cast hf x y
  have hb := finiteDualCertificate_le (realRows E) (realRows F)
    (realRows_valid E hE) (realRows_valid F hF) G hG
    (fun θ => (lambda θ : ℝ)) hl (fun θ y => (mu θ y : ℝ)) hmr0 hmrl
    (fun x => (floor x : ℝ)) hfr c hc
  have hvr : (lower : ℝ) ≤ (∑ x, (floor x : ℝ)) -
      ∑ θ, ∑ y, (mu θ y : ℝ) * realRows F θ y := by
    change (lower : ℝ) ≤ (∑ x, (floor x : ℝ)) -
      ∑ θ, ∑ y, (mu θ y : ℝ) * (F θ y : ℝ)
    exact_mod_cast hv
  exact hvr.trans hb

/-- A rational stochastic decoder supplies the opposite bound after exact
half-l1 arithmetic at each world. -/
theorem rational_upper_bound [Nonempty Θ]
    (E : Θ → X → ℚ) (F : Θ → Y → ℚ)
    (G : X → Y → ℚ) (hG : RatRows G) (upper : ℚ)
    (herr : ∀ θ, ∑ y, |(∑ x, E θ x * G x y) - F θ y| ≤ 2 * upper) :
    finiteDeficiency (realRows E) (realRows F) ≤ (upper : ℝ) := by
  apply finiteDeficiency_le_of_decoder (realRows E) (realRows F)
    (fun x y => (G x y : ℝ))
  · intro x _
    constructor
    · intro y; change (0 : ℝ) ≤ (G x y : ℝ); exact_mod_cast (hG x).1 y
    · change (∑ y, (G x y : ℝ)) = 1
      exact_mod_cast (hG x).2
  · intro θ
    change (1/2 : ℝ) * ∑ y, |(∑ x, (E θ x : ℝ) * (G x y : ℝ)) -
      (F θ y : ℝ)| ≤ (upper : ℝ)
    have hh : (∑ y, |(∑ x, (E θ x : ℝ) * (G x y : ℝ)) -
        (F θ y : ℝ)|) ≤ 2 * (upper : ℝ) := by exact_mod_cast herr θ
    linarith

/-- This conclusion concerns finite records, not eventual process order. -/
theorem incomparable_of_positive_bounds
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hEF : a ≤ finiteDeficiency E F) (hFE : b ≤ finiteDeficiency F E) :
    0 < finiteDeficiency E F ∧ 0 < finiteDeficiency F E :=
  ⟨ha.trans_le hEF, hb.trans_le hFE⟩
end IdExp.EmpiricalEnding
