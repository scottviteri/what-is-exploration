import Formal.DualCertificate

/-!
# Compact finite decoder attainment

The finite-world compactness argument and zero-deficiency equivalence for
arbitrary real matrices. No two-world or call-function hypothesis is needed.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {Θ X Y : Type*} [Fintype X] [Fintype Y]

/-! ### Attainment of the deficiency infimum -/

/-- A deterministic constant rule shows the decoder simplex is nonempty. -/
theorem stochasticRules_nonempty_of_nonempty [Nonempty Y] :
    (stochasticRules X Y).Nonempty := by
  classical
  let y0 : Y := Classical.arbitrary Y
  refine ⟨fun _ y => if y = y0 then 1 else 0, fun x _ => ⟨fun y => ?_, ?_⟩⟩
  · by_cases h : y = y0 <;> simp [h]
  · simp

theorem continuous_decodeErr (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (θ : Θ) :
    Continuous (fun G : X → Y → ℝ => decodeErr E F G θ) := by
  unfold decodeErr
  fun_prop

/-- Worst-world decoding error of a decoder, over a finite nonempty world class. -/
noncomputable def worstDecodeErr [Fintype Θ] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun θ => decodeErr E F G θ)

theorem decodeErr_le_worstDecodeErr [Fintype Θ] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) (θ : Θ) :
    decodeErr E F G θ ≤ worstDecodeErr E F G :=
  Finset.le_sup' (fun θ => decodeErr E F G θ) (Finset.mem_univ θ)

theorem worstDecodeErr_le [Fintype Θ] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) (c : ℝ)
    (h : ∀ θ, decodeErr E F G θ ≤ c) : worstDecodeErr E F G ≤ c :=
  Finset.sup'_le _ _ (fun θ _ => h θ)

theorem continuous_worstDecodeErr [Fintype Θ] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    Continuous (worstDecodeErr E F) := by
  unfold worstDecodeErr
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun θ _ => continuous_decodeErr E F θ)

/-- **Attainment of the deficiency infimum.**  Over a finite nonempty world
class and a nonempty target alphabet, some stochastic decoder has every
worldwise error at most the deficiency.  No validity of `E` or `F` is needed:
the decoder set is compact and the worst-world error is continuous. -/
theorem exists_decoder_eq_finiteDeficiency [Fintype Θ] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    ∃ G ∈ stochasticRules X Y, ∀ θ, decodeErr E F G θ ≤ finiteDeficiency E F := by
  obtain ⟨G, hG, hmin⟩ := (isCompact_stochasticRules X Y).exists_isMinOn
    stochasticRules_nonempty_of_nonempty (continuous_worstDecodeErr E F).continuousOn
  refine ⟨G, hG, fun θ => (decodeErr_le_worstDecodeErr E F G θ).trans ?_⟩
  apply le_csInf (finiteDeficiencyCandidates_nonempty E F)
  rintro c ⟨G', hG', herr⟩
  exact (hmin hG').trans (worstDecodeErr_le E F G' c herr)

/-- The deficiency infimum is a minimum: it equals the worst-world error of
the attaining decoder. -/
theorem exists_decoder_worstDecodeErr_eq_finiteDeficiency [Fintype Θ] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    ∃ G ∈ stochasticRules X Y, worstDecodeErr E F G = finiteDeficiency E F := by
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency E F
  refine ⟨G, hG, le_antisymm (worstDecodeErr_le E F G _ herr) ?_⟩
  exact csInf_le (finiteDeficiencyCandidates_bddBelow E F)
    ⟨G, hG, fun θ => decodeErr_le_worstDecodeErr E F G θ⟩

/-- Deficiency over a finite nonempty world class is nonnegative for arbitrary
real matrices, by attainment. -/
theorem finiteDeficiency_nonneg_of_fintype [Fintype Θ] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    0 ≤ finiteDeficiency E F := by
  obtain ⟨G, _, herr⟩ := exists_decoder_eq_finiteDeficiency E F
  exact (decodeErr_nonneg E F G (Classical.arbitrary Θ)).trans (herr _)

/-- Zero decoding error at a world means the decoded row equals the target row. -/
theorem decodeErr_eq_zero_iff (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (θ : Θ) :
    decodeErr E F G θ = 0 ↔ ∀ y, (∑ x, E θ x * G x y) = F θ y := by
  unfold decodeErr
  rw [mul_eq_zero, or_iff_right (by norm_num),
    Finset.sum_eq_zero_iff_of_nonneg (fun y _ => abs_nonneg _)]
  simp only [Finset.mem_univ, true_implies, abs_eq_zero, sub_eq_zero]

/-- Zero deficiency over a finite nonempty world class is attained by an exact
stochastic garbling. -/
theorem finiteBlackwellLE_of_finiteDeficiency_eq_zero [Fintype Θ] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : finiteDeficiency E F = 0) : FiniteBlackwellLE F E := by
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency E F
  refine ⟨G, hG, ?_⟩
  funext θ y
  have h0 : decodeErr E F G θ = 0 :=
    le_antisymm (h ▸ herr θ) (decodeErr_nonneg E F G θ)
  exact (decodeErr_eq_zero_iff E F G θ).1 h0 y

/-- An exact stochastic garbling has zero deficiency. -/
theorem finiteDeficiency_eq_zero_of_finiteBlackwellLE [Fintype Θ] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : FiniteBlackwellLE F E) : finiteDeficiency E F = 0 := by
  obtain ⟨G, hG, hEG⟩ := h
  refine le_antisymm ?_ (finiteDeficiency_nonneg_of_fintype E F)
  apply csInf_le (finiteDeficiencyCandidates_bddBelow E F)
  refine ⟨G, hG, fun θ => le_of_eq ?_⟩
  rw [decodeErr_eq_zero_iff]
  intro y
  exact congrFun (congrFun hEG θ) y

/-- Exact garbling is zero deficiency, over a finite nonempty world class. -/
theorem finiteBlackwellLE_iff_finiteDeficiency_eq_zero [Fintype Θ] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    FiniteBlackwellLE F E ↔ finiteDeficiency E F = 0 :=
  ⟨finiteDeficiency_eq_zero_of_finiteBlackwellLE E F,
    finiteBlackwellLE_of_finiteDeficiency_eq_zero E F⟩

end IdExp
