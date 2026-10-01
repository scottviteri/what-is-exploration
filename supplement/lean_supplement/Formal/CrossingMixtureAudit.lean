import Formal.CrossingPartitionScores
import Formal.CausalPartialExecution

/-!
# The recorded-mixture audit of the crossing partitions

The third number of the paper's crossing-partition example.  On the worlds
`00, 01, 10, 11` let `A` reveal whether the world is `00` and `B` reveal the
second bit.  A collector that runs `A` with probability `r`, otherwise `B`, and
records its choice has exact deficiencies

`δ(M_r, A) = (1 − r)/2`,  `δ(M_r, B) = r/2`,

so its audit against the target family `{A, B}` is `½·max{r, 1 − r}`: both
pure tests audit at `½`, and the balanced mixture is the unique minimizer with
audit `¼`.  Upper bounds are explicit decoders (return the saved result when
the requested test was run, otherwise guess fairly on the ambiguous signal);
lower bounds are the pairwise separation certificate on a world pair that the
target separates and the source does not.
-/

namespace IdExp

open Finset

noncomputable section

/-- The pure tests as experiments on the four worlds. -/
def testA : FiniteExperiment (Fin 4) (Fin 2) := deterministicExperiment crossingA
def testB : FiniteExperiment (Fin 4) (Fin 2) := deterministicExperiment crossingB

theorem testA_valid : IsFiniteExperiment testA := by
  intro θ
  refine ⟨fun s => by unfold testA deterministicExperiment; split_ifs <;> norm_num, ?_⟩
  fin_cases θ <;> simp [testA, deterministicExperiment, crossingA, Fin.sum_univ_two]

theorem testB_valid : IsFiniteExperiment testB := by
  intro θ
  refine ⟨fun s => by unfold testB deterministicExperiment; split_ifs <;> norm_num, ?_⟩
  fin_cases θ <;> simp [testB, deterministicExperiment, crossingB, Fin.sum_univ_two]

/-- Run `A` with probability `r` (label `0`), otherwise `B` (label `1`), and
record the label with the result. -/
def recordedMixture (r : ℝ) : FiniteExperiment (Fin 4) (Fin 2 × Fin 2) :=
  fun θ z => if z.1 = 0 then r * testA θ z.2 else (1 - r) * testB θ z.2

theorem recordedMixture_valid {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsFiniteExperiment (recordedMixture r) := by
  intro θ
  constructor
  · intro z
    unfold recordedMixture
    split_ifs
    · exact mul_nonneg hr0 ((testA_valid θ).1 _)
    · exact mul_nonneg (by linarith) ((testB_valid θ).1 _)
  · unfold recordedMixture
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte, ← Finset.mul_sum, (testA_valid θ).2, (testB_valid θ).2]
    ring

/-! ## Mixtures with a recorded label: total variation and decoding are linear -/

/-- Recording the label makes total variation the weighted sum of the pure
tests' total variations. -/
theorem finiteTV_recordedMixture {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (θ θ' : Fin 4) :
    finiteTV (recordedMixture r θ) (recordedMixture r θ') =
      r * finiteTV (testA θ) (testA θ') + (1 - r) * finiteTV (testB θ) (testB θ') := by
  unfold finiteTV recordedMixture
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte]
  have hA : ∀ s, |r * testA θ s - r * testA θ' s| = r * |testA θ s - testA θ' s| := fun s => by
    rw [← mul_sub, abs_mul, abs_of_nonneg hr0]
  have hB : ∀ s, |(1 - r) * testB θ s - (1 - r) * testB θ' s| =
      (1 - r) * |testB θ s - testB θ' s| := fun s => by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith)]
  simp only [hA, hB, ← Finset.mul_sum]
  ring

/-- Lift a decoder from `B`-signals to `A`-signals to the recorded mixture:
return the saved `A`-result when `A` was run, otherwise decode the `B`-result. -/
def liftDecoderA (G : Fin 2 → Fin 2 → ℝ) : Fin 2 × Fin 2 → Fin 2 → ℝ :=
  fun z a => if z.1 = 0 then (if a = z.2 then 1 else 0) else G z.2 a

/-- Lift a decoder from `A`-signals to `B`-signals to the recorded mixture. -/
def liftDecoderB (G : Fin 2 → Fin 2 → ℝ) : Fin 2 × Fin 2 → Fin 2 → ℝ :=
  fun z b => if z.1 = 1 then (if b = z.2 then 1 else 0) else G z.2 b

theorem liftDecoderA_stochastic (G : Fin 2 → Fin 2 → ℝ) (hG : G ∈ stochasticRules (Fin 2) (Fin 2)) :
    liftDecoderA G ∈ stochasticRules (Fin 2 × Fin 2) (Fin 2) := by
  rintro ⟨c, o⟩ _
  by_cases hc : c = 0
  · subst hc
    refine ⟨fun a => by simp only [liftDecoderA, Fin.isValue, ↓reduceIte]; split_ifs <;> norm_num, ?_⟩
    simp [liftDecoderA, Fin.sum_univ_two]
  · refine ⟨fun a => by simp only [liftDecoderA, hc, ↓reduceIte]; exact (hG o (Set.mem_univ o)).1 a, ?_⟩
    simp only [liftDecoderA, hc, ↓reduceIte]
    exact (hG o (Set.mem_univ o)).2

theorem liftDecoderB_stochastic (G : Fin 2 → Fin 2 → ℝ) (hG : G ∈ stochasticRules (Fin 2) (Fin 2)) :
    liftDecoderB G ∈ stochasticRules (Fin 2 × Fin 2) (Fin 2) := by
  rintro ⟨c, o⟩ _
  by_cases hc : c = 1
  · subst hc
    refine ⟨fun b => by simp only [liftDecoderB, Fin.isValue, ↓reduceIte]; split_ifs <;> norm_num, ?_⟩
    simp [liftDecoderB, Fin.sum_univ_two]
  · refine ⟨fun b => by simp only [liftDecoderB, hc, ↓reduceIte]; exact (hG o (Set.mem_univ o)).1 b, ?_⟩
    simp only [liftDecoderB, hc, ↓reduceIte]
    exact (hG o (Set.mem_univ o)).2

theorem decisionLaw_liftDecoderA (r : ℝ) (G : Fin 2 → Fin 2 → ℝ) (θ : Fin 4) :
    finiteDecisionLaw (recordedMixture r) (liftDecoderA G) θ =
      fun a => r * testA θ a + (1 - r) * finiteDecisionLaw testB G θ a := by
  funext a
  unfold finiteDecisionLaw recordedMixture liftDecoderA
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, Finset.mul_sum]
  ring

theorem decisionLaw_liftDecoderB (r : ℝ) (G : Fin 2 → Fin 2 → ℝ) (θ : Fin 4) :
    finiteDecisionLaw (recordedMixture r) (liftDecoderB G) θ =
      fun b => (1 - r) * testB θ b + r * finiteDecisionLaw testA G θ b := by
  funext b
  unfold finiteDecisionLaw recordedMixture liftDecoderB
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp only [h10, h01, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, Finset.mul_sum]
  ring

/-- Total variation from a mixture `r·p + (1−r)·q` to `p` is `(1−r)` times the
total variation from `q` to `p`. -/
theorem finiteTV_mix_left {X : Type*} [Fintype X] (p q : X → ℝ) {r : ℝ} (hr1 : r ≤ 1) :
    finiteTV (fun x => r * p x + (1 - r) * q x) p = (1 - r) * finiteTV q p := by
  unfold finiteTV
  have h : ∀ x, |r * p x + (1 - r) * q x - p x| = (1 - r) * |q x - p x| := fun x => by
    rw [show r * p x + (1 - r) * q x - p x = (1 - r) * (q x - p x) by ring, abs_mul,
      abs_of_nonneg (by linarith)]
  simp only [h, ← Finset.mul_sum]
  ring

/-! ## The pure decoders and their errors -/

/-- From a `B`-signal to an `A`-signal: `B = 1` forces `A = 1`; on `B = 0`
guess fairly. -/
def decodeBA : Fin 2 → Fin 2 → ℝ := fun o a => if o = 1 then (if a = 1 then 1 else 0) else 1 / 2

/-- From an `A`-signal to a `B`-signal: `A = 0` forces `B = 0`; on `A = 1`
guess fairly. -/
def decodeAB : Fin 2 → Fin 2 → ℝ := fun o b => if o = 0 then (if b = 0 then 1 else 0) else 1 / 2

theorem decodeBA_stochastic : decodeBA ∈ stochasticRules (Fin 2) (Fin 2) := by
  intro o _
  refine ⟨fun a => by unfold decodeBA; split_ifs <;> norm_num, ?_⟩
  fin_cases o <;> simp [decodeBA, Fin.sum_univ_two] <;> norm_num

theorem decodeAB_stochastic : decodeAB ∈ stochasticRules (Fin 2) (Fin 2) := by
  intro o _
  refine ⟨fun b => by unfold decodeAB; split_ifs <;> norm_num, ?_⟩
  fin_cases o <;> simp [decodeAB, Fin.sum_univ_two] <;> norm_num

theorem decodeBA_error (θ : Fin 4) : finiteTV (finiteDecisionLaw testB decodeBA θ) (testA θ) ≤ 1 / 2 := by
  fin_cases θ <;>
    simp [finiteTV, finiteDecisionLaw, testA, testB, deterministicExperiment, crossingA, crossingB,
      decodeBA, Fin.sum_univ_two] <;> norm_num

theorem decodeAB_error (θ : Fin 4) : finiteTV (finiteDecisionLaw testA decodeAB θ) (testB θ) ≤ 1 / 2 := by
  fin_cases θ <;>
    simp [finiteTV, finiteDecisionLaw, testA, testB, deterministicExperiment, crossingA, crossingB,
      decodeAB, Fin.sum_univ_two] <;> norm_num

/-! ## Pairwise separations -/

theorem testA_tv_00_10 : finiteTV (testA 0) (testA 2) = 1 := by
  simp [finiteTV, testA, deterministicExperiment, crossingA, Fin.sum_univ_two]; norm_num

theorem testB_tv_00_10 : finiteTV (testB 0) (testB 2) = 0 := by
  simp [finiteTV, testB, deterministicExperiment, crossingB, Fin.sum_univ_two]

theorem testA_tv_01_10 : finiteTV (testA 1) (testA 2) = 0 := by
  simp [finiteTV, testA, deterministicExperiment, crossingA, Fin.sum_univ_two]

theorem testB_tv_01_10 : finiteTV (testB 1) (testB 2) = 1 := by
  simp [finiteTV, testB, deterministicExperiment, crossingB, Fin.sum_univ_two]; norm_num

/-! ## Exact deficiencies -/

/-- `δ(M_r, A) = (1 − r)/2`. -/
theorem recordedMixture_deficiency_A {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteDeficiency (recordedMixture r) testA = (1 - r) / 2 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (liftDecoderA decodeBA)
      (liftDecoderA_stochastic decodeBA decodeBA_stochastic)
    intro θ
    change finiteTV (finiteDecisionLaw (recordedMixture r) (liftDecoderA decodeBA) θ) (testA θ) ≤ _
    rw [decisionLaw_liftDecoderA, finiteTV_mix_left _ _ hr1]
    have := decodeBA_error θ
    nlinarith
  · have h := finiteDeficiency_pairwise_lower (recordedMixture r) testA
      (recordedMixture_valid hr0 hr1) testA_valid 0 2
    rw [testA_tv_00_10, finiteTV_recordedMixture hr0 hr1, testA_tv_00_10, testB_tv_00_10] at h
    linarith

/-- `δ(M_r, B) = r/2`. -/
theorem recordedMixture_deficiency_B {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteDeficiency (recordedMixture r) testB = r / 2 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (liftDecoderB decodeAB)
      (liftDecoderB_stochastic decodeAB decodeAB_stochastic)
    intro θ
    change finiteTV (finiteDecisionLaw (recordedMixture r) (liftDecoderB decodeAB) θ) (testB θ) ≤ _
    rw [decisionLaw_liftDecoderB]
    have hmix := finiteTV_mix_left (testB θ) (finiteDecisionLaw testA decodeAB θ)
      (r := 1 - r) (by linarith)
    simp only [sub_sub_cancel] at hmix
    rw [hmix]
    have := decodeAB_error θ
    nlinarith
  · have h := finiteDeficiency_pairwise_lower (recordedMixture r) testB
      (recordedMixture_valid hr0 hr1) testB_valid 1 2
    rw [testB_tv_01_10, finiteTV_recordedMixture hr0 hr1, testA_tv_01_10, testB_tv_01_10] at h
    linarith

/-- `δ(A, B) = 1/2`: `A` cannot tell `01` from `10`. -/
theorem testA_deficiency_B : finiteDeficiency testA testB = 1 / 2 := by
  apply le_antisymm
  · exact finiteDeficiency_le_of_decoder _ _ decodeAB decodeAB_stochastic _ fun θ => decodeAB_error θ
  · have h := finiteDeficiency_pairwise_lower testA testB testA_valid testB_valid 1 2
    rw [testB_tv_01_10, testA_tv_01_10] at h
    linarith

/-- `δ(B, A) = 1/2`: `B` cannot tell `00` from `10`. -/
theorem testB_deficiency_A : finiteDeficiency testB testA = 1 / 2 := by
  apply le_antisymm
  · exact finiteDeficiency_le_of_decoder _ _ decodeBA decodeBA_stochastic _ fun θ => decodeBA_error θ
  · have h := finiteDeficiency_pairwise_lower testB testA testB_valid testA_valid 0 2
    rw [testA_tv_00_10, testB_tv_00_10] at h
    linarith

/-! ## The audit against `{A, B}` -/

/-- The audit of the recorded mixture against the target family `{A, B}`. -/
def recordedMixtureAudit (r : ℝ) : ℝ :=
  max (finiteDeficiency (recordedMixture r) testA) (finiteDeficiency (recordedMixture r) testB)

/-- `Γ(r) = ½·max{r, 1 − r}`. -/
theorem recordedMixtureAudit_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    recordedMixtureAudit r = (1 / 2) * max r (1 - r) := by
  unfold recordedMixtureAudit
  rw [recordedMixture_deficiency_A hr0 hr1, recordedMixture_deficiency_B hr0 hr1]
  rcases le_total r (1 - r) with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : r / 2 ≤ (1 - r) / 2)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith : (1 - r) / 2 ≤ r / 2)]; ring

/-- The balanced mixture audits at `1/4`. -/
theorem recordedMixtureAudit_half : recordedMixtureAudit (1 / 2) = 1 / 4 := by
  rw [recordedMixtureAudit_eq (by norm_num) (by norm_num)]
  norm_num

/-- Every mixture audits at least `1/4`, with equality only at `r = 1/2`. -/
theorem recordedMixtureAudit_ge_quarter {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    1 / 4 ≤ recordedMixtureAudit r := by
  rw [recordedMixtureAudit_eq hr0 hr1]
  rcases le_total r (1 - r) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem recordedMixtureAudit_eq_quarter_iff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    recordedMixtureAudit r = 1 / 4 ↔ r = 1 / 2 := by
  rw [recordedMixtureAudit_eq hr0 hr1]
  constructor
  · intro h
    rcases le_total r (1 - r) with hle | hle
    · rw [max_eq_right hle] at h; linarith
    · rw [max_eq_left hle] at h; linarith
  · rintro rfl; norm_num

/-- The pure tests audit at `1/2` (`δ(A, A) = 0`, `δ(A, B) = 1/2`, and symmetrically). -/
theorem pure_audits_half :
    recordedMixtureAudit 1 = 1 / 2 ∧ recordedMixtureAudit 0 = 1 / 2 := by
  constructor
  · rw [recordedMixtureAudit_eq (by norm_num) (by norm_num)]; norm_num
  · rw [recordedMixtureAudit_eq (by norm_num) (by norm_num)]; norm_num

end

end IdExp
