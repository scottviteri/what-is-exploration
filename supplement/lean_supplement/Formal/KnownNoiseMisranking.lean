import Formal.SurprisalDecomposition
import Formal.SurrogateBlindness

/-!
# Known four-symbol noise strictly misranks a one-step experiment

Two worlds encode an unknown bit with a fair prior. READ returns that bit,
embedded in a four-symbol observation alphabet; NOISE returns four uniform
symbols independently of the world. The exact conditional-on-action
surprisal of every randomized causal policy is `2-r` bits, where `r` is its
initial READ probability. Its one-step information is `r` bits. Directed
deficiencies between the native root observations are zero and one half.
-/

namespace IdExp.KnownNoise

open Finset

noncomputable section

abbrev World := Fin 2
abbrev Action := Fin 2
abbrev Observation := Fin 4

/-- Action zero reads the fixed world bit; action one samples known noise. -/
def response (θ : World) : CausalResponse Action Observation :=
  fun _ a o => if a = 0 then if o.val = θ.val then 1 else 0 else 1 / 4

/-- The experiment is valid at every history. Only its first step is scored. -/
theorem response_valid (θ : World) : IsCausalResponse (response θ) := by
  intro h a
  constructor
  · intro o
    simp only [response]
    split_ifs <;> norm_num
  · fin_cases θ <;> fin_cases a <;> norm_num [response, Fin.sum_univ_succ] <;> decide

/-- Exactly the fair prior on the two fixed-bit worlds. -/
def prior : World → ℝ := fun _ => 1 / 2

theorem prior_valid : IsDist prior := by
  constructor
  · intro θ; norm_num [prior]
  · norm_num [prior, Fin.sum_univ_succ]

/-- The conditional observation experiment at READ. -/
def readExperiment : FiniteExperiment World Observation := fun θ => response θ [] 0
/-- The conditional observation experiment at NOISE. -/
def noiseExperiment : FiniteExperiment World Observation := fun θ => response θ [] 1

theorem readExperiment_valid : IsFiniteExperiment readExperiment :=
  fun θ => response_valid θ [] 0

theorem noiseExperiment_valid : IsFiniteExperiment noiseExperiment :=
  fun θ => response_valid θ [] 1

theorem read_pairTV : finiteTV (readExperiment 0) (readExperiment 1) = 1 := by
  norm_num [finiteTV, readExperiment, response, Fin.sum_univ_succ]

/-- Four-symbol noise has exactly one-half reverse simulation deficiency. -/
theorem noise_read_deficiency : finiteDeficiency noiseExperiment readExperiment = 1 / 2 := by
  rw [finiteDeficiency_classIndependent_binary_eq_half_pairTV _ _
    noiseExperiment_valid readExperiment_valid (by intro θ θ'; rfl), read_pairTV]

/-- Ignoring READ's bit and drawing a uniform symbol simulates NOISE exactly. -/
theorem read_noise_deficiency : finiteDeficiency readExperiment noiseExperiment = 0 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder readExperiment noiseExperiment
      (fun _ _ => (1 / 4 : ℝ))
    · intro x _
      constructor
      · intro y; norm_num
      · norm_num [Fin.sum_univ_succ]
    · intro θ
      fin_cases θ <;>
        norm_num [decodeErr, finiteDecisionLaw, finiteTV, readExperiment, noiseExperiment,
          response, Fin.sum_univ_succ]
  · exact finiteDeficiency_nonneg_of_valid _ _ readExperiment_valid noiseExperiment_valid

private theorem log_quarter : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0), Real.log_one]
  have hh : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [hh]
  ring

private theorem log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
  ring

/-- All randomized policies are covered, including zero-probability actions.
The policy's own randomization is absent from the scored conditional surprisal. -/
theorem expected_surprisal (π : ValidCausalPolicy Action Observation) :
    expectedLastSurprisal π.1 response prior 0 =
      (2 - π.1 [] 0) * Real.log 2 := by
  rw [expectedLastSurprisal_eq π.1 response prior prior_valid π.2 response_valid]
  have hr : π.1 [] 0 + π.1 [] 1 = 1 := by
    simpa [Fin.sum_univ_succ] using (π.2 []).2
  norm_num [stepJointMass, finiteBayesMass, causalFiniteExperiment, causalTraceProb,
    causalTraceProbFrom, prior, response, Fintype.sum_prod_type, Fin.sum_univ_succ,
    log_half, log_quarter]
  linear_combination 2 * Real.log 2 * hr

/-- The residual world-conditional entropy comes entirely from NOISE. -/
theorem conditional_entropy (π : ValidCausalPolicy Action Observation) :
    stepConditionalEntropy π.1 response prior 0 =
      2 * (1 - π.1 [] 0) * Real.log 2 := by
  have hr : π.1 [] 0 + π.1 [] 1 = 1 := by
    simpa [Fin.sum_univ_succ] using (π.2 []).2
  norm_num [stepConditionalEntropy, causalFiniteExperiment, causalTraceProb,
    causalTraceProbFrom, prior, response, ent, Real.negMulLog, Fin.sum_univ_succ,
    log_quarter]
  linear_combination 2 * Real.log 2 * hr

/-- Exact one-step information of the retained action-observation record. -/
theorem information (π : ValidCausalPolicy Action Observation) :
    finiteBayesInformation prior (causalFiniteExperiment π.1 response 1) =
      π.1 [] 0 * Real.log 2 := by
  have h := expectedLastSurprisal_eq_information_add π.1 response prior prior_valid
    π.2 response_valid 0
  rw [expected_surprisal, conditional_entropy,
    finiteBayesInformation_zero π.1 response prior prior_valid] at h
  norm_num at h
  linarith

/-- Conversion from natural-log quantities to the paper's bits is explicit. -/
theorem scores_in_bits (π : ValidCausalPolicy Action Observation) :
    expectedLastSurprisal π.1 response prior 0 / Real.log 2 = 2 - π.1 [] 0 ∧
    finiteBayesInformation prior (causalFiniteExperiment π.1 response 1) /
      Real.log 2 = π.1 [] 0 := by
  have hn : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [expected_surprisal, information]
  constructor <;> field_simp [hn]

/-- A deterministic policy choosing one fixed action at every history. -/
def purePolicy (a : Action) : ValidCausalPolicy Action Observation :=
  ⟨detPolicy (fun _ => a), isCausalPolicy_detPolicy (fun _ => a)⟩

/-- READ and NOISE respectively score `(1,1)` and `(2,0)` in
(surprisal, information) bits. -/
theorem pure_scores_in_bits :
    expectedLastSurprisal (purePolicy 0).1 response prior 0 / Real.log 2 = 1 ∧
    finiteBayesInformation prior (causalFiniteExperiment (purePolicy 0).1 response 1) /
      Real.log 2 = 1 ∧
    expectedLastSurprisal (purePolicy 1).1 response prior 0 / Real.log 2 = 2 ∧
    finiteBayesInformation prior (causalFiniteExperiment (purePolicy 1).1 response 1) /
      Real.log 2 = 0 := by
  have hr := scores_in_bits (purePolicy 0)
  have hn := scores_in_bits (purePolicy 1)
  norm_num [purePolicy, detPolicy] at hr hn
  exact ⟨hr.1, hr.2, hn.1, by simpa [purePolicy] using
      (congrArg (fun x : ℝ => x / Real.log 2) hn.2)⟩

/-- Every exact surprisal optimum chooses NOISE initially, over all valid
randomized policies. Behavior after the initial action is unrestricted. -/
theorem surprisal_maximizers (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      expectedLastSurprisal ρ.1 response prior 0 ≤ expectedLastSurprisal π.1 response prior 0) ↔
    π.1 [] 0 = 0 := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · intro h
    have hn := h (purePolicy 1)
    rw [expected_surprisal, expected_surprisal] at hn
    norm_num [purePolicy, detPolicy] at hn
    nlinarith [(π.2 []).1 0]
  · intro hπ ρ
    rw [expected_surprisal, expected_surprisal, hπ]
    nlinarith [(ρ.2 []).1 0]

/-- Every exact information optimum chooses READ initially. -/
theorem information_maximizers (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      finiteBayesInformation prior (causalFiniteExperiment ρ.1 response 1) ≤
        finiteBayesInformation prior (causalFiniteExperiment π.1 response 1)) ↔
    π.1 [] 0 = 1 := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hrow (ρ : ValidCausalPolicy Action Observation) : ρ.1 [] 0 ≤ 1 := by
    have hh := (ρ.2 []).2
    simp only [Fin.sum_univ_two] at hh
    linarith [(ρ.2 []).1 1]
  constructor
  · intro h
    have hr := h (purePolicy 0)
    rw [information, information] at hr
    norm_num [purePolicy, detPolicy] at hr
    nlinarith [hrow π]
  · intro hπ ρ
    rw [information, information, hπ]
    nlinarith [hrow ρ]

/-- The literal length-one retained record has the expected action factor. -/
theorem record_one (π : ValidCausalPolicy Action Observation) (θ : World)
    (w : CausalFiniteTrace Action Observation 1) :
    causalFiniteExperiment π.1 response 1 θ w =
      π.1 [] (w 0).1 * response θ [] (w 0).1 (w 0).2 := by
  simp [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom, List.ofFn_succ]

/-- The two literal causal record experiments used in the strict comparison. -/
def pureRecord (a : Action) : FiniteExperiment World (CausalFiniteTrace Action Observation 1) :=
  causalFiniteExperiment (purePolicy a).1 response 1

theorem pureRecord_valid (a : Action) : IsFiniteExperiment (pureRecord a) :=
  causalFiniteExperiment_valid _ (purePolicy a).2 response response_valid 1

theorem noise_record_classIndependent : ClassIndependentFiniteExperiment (pureRecord 1) := by
  intro θ θ'
  funext w
  change causalFiniteExperiment (purePolicy 1).1 response 1 θ w =
    causalFiniteExperiment (purePolicy 1).1 response 1 θ' w
  rw [record_one (purePolicy 1), record_one (purePolicy 1)]
  simp only [purePolicy, detPolicy]
  by_cases h : (w 0).1 = 1
  · simp [h, response]
  · simp [h]

theorem read_record_pairTV : finiteTV (pureRecord 0 0) (pureRecord 0 1) = 1 := by
  unfold finiteTV pureRecord
  rw [sum_trace_succ]
  norm_num [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    List.ofFn_succ, purePolicy, detPolicy, response,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.snoc_zero]

/-- The one-half loss also holds on the full retained causal records, which
include the chosen action. -/
theorem noise_read_record_deficiency : finiteDeficiency (pureRecord 1) (pureRecord 0) = 1 / 2 := by
  rw [finiteDeficiency_classIndependent_binary_eq_half_pairTV _ _
    (pureRecord_valid 1) (pureRecord_valid 0) noise_record_classIndependent,
    read_record_pairTV]

/-- The literal READ record simulates the literal NOISE record exactly. -/
theorem read_noise_record_deficiency : finiteDeficiency (pureRecord 0) (pureRecord 1) = 0 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder (pureRecord 0) (pureRecord 1)
      (fun _ => pureRecord 1 0)
    · intro x _
      exact pureRecord_valid 1 0
    · intro θ
      have he : finiteDecisionLaw (pureRecord 0) (fun _ => pureRecord 1 0) θ =
          pureRecord 1 θ := by
        funext y
        simp only [finiteDecisionLaw, ← Finset.sum_mul, (pureRecord_valid 0 θ).2, one_mul]
        exact congrFun (noise_record_classIndependent 0 θ) y
      change finiteTV (finiteDecisionLaw (pureRecord 0) (fun _ => pureRecord 1 0) θ)
        (pureRecord 1 θ) ≤ 0
      rw [he]
      simp [finiteTV]
  · exact finiteDeficiency_nonneg_of_valid _ _ (pureRecord_valid 0) (pureRecord_valid 1)

/-- Every surprisal optimum collects exactly the NOISE experiment at this
budget; root lotteries cannot avoid the strict loss by a different tie rule. -/
theorem optimal_surprisal_record (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation,
      expectedLastSurprisal ρ.1 response prior 0 ≤ expectedLastSurprisal π.1 response prior 0) :
    causalFiniteExperiment π.1 response 1 = pureRecord 1 := by
  have h0 := (surprisal_maximizers π).mp hopt
  have h1 : π.1 [] 1 = 1 := by
    have hh := (π.2 []).2
    simp only [Fin.sum_univ_two] at hh
    linarith
  funext θ w
  rw [record_one]
  change _ = causalFiniteExperiment (purePolicy 1).1 response 1 θ w
  rw [record_one]
  have hh : (w 0).1 = 0 ∨ (w 0).1 = 1 := by
    generalize (w 0).1 = a
    fin_cases a <;> simp
  rcases hh with h | h <;> simp [h, h0, h1, purePolicy, detPolicy]

/-- The opening paper claim on full retained records: every optimal surprisal
collector is strictly less informative than the available READ collector. -/
theorem every_surprisal_optimum_strictly_misranks
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation,
      expectedLastSurprisal ρ.1 response prior 0 ≤ expectedLastSurprisal π.1 response prior 0) :
    π.1 [] 0 = 0 ∧
    finiteDeficiency (pureRecord 0) (causalFiniteExperiment π.1 response 1) = 0 ∧
    finiteDeficiency (causalFiniteExperiment π.1 response 1) (pureRecord 0) = 1 / 2 := by
  rw [optimal_surprisal_record π hopt]
  exact ⟨(surprisal_maximizers π).mp hopt,
    read_noise_record_deficiency, noise_read_record_deficiency⟩

end
end IdExp.KnownNoise
