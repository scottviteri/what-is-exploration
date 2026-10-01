import Formal.RecordedMixtureScores

/-!
# Decision witnesses for the crossing partitions

The paper's "concrete decision witnesses" paragraph and its displayed
identity `eq:crossing-mixture-decision-distance`, in exact form.  On the worlds
`00, 01, 10, 11` with prior `(3, 5, 1, 1)/10`, `A` reveals whether the world is
`00`, `B` reveals the second bit, and `E_r` runs `A` with recorded probability
`r`.  For the two unit-payoff questions "is the world `00`?" and "is the second
bit `1`?":

| value | `A` | `B` | `E_r` |
|---|---|---|---|
| first question | `1` | `9/10` | `9/10 + r/10` |
| second question | `9/10` | `1` | `1 − r/10` |

The uniform witnesses `P_A` (equal mass on `00, 10`, first question) and `P_B`
(equal mass on `01, 10`, second question) have benchmark one and regrets
`R_{P_A}(E_r) = (1 − r)/2`, `R_{P_B}(E_r) = r/2`, and for all `r, s ∈ [0, 1]`

`δ(E_r, E_s) = |r − s|/2 = max{0, V_{P_A}(E_s) − V_{P_A}(E_r), V_{P_B}(E_s) − V_{P_B}(E_r)}`.

Upper bounds: for `r ≥ s` retain probability `s/r` of each `A`-labelled signal
and turn the rest into a fair `B` answer; for `r < s` the mirror image.  Lower
bounds: the two witness values.  Distinct mixtures are therefore incomparable,
and the same two tasks recover the audit `½·max{r, 1 − r}`.
-/

namespace IdExp

open Finset

noncomputable section

/-- A `sup'` over `Fin 2` is a `max`. -/
theorem sup'_univ_fin_two (f : Fin 2 → ℝ) : univ.sup' univ_nonempty f = max (f 0) (f 1) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i _ => by fin_cases i <;> simp
  · exact max_le (Finset.le_sup' f (mem_univ 0)) (Finset.le_sup' f (mem_univ 1))

/-! ## The two unit-payoff questions -/

/-- "Is the world `00`?": unit payoff for reporting `A`'s label. -/
def askA : Fin 4 → Fin 2 → ℝ := fun θ d => if d = crossingA θ then 1 else 0

/-- "Is the second bit `1`?": unit payoff for reporting `B`'s label. -/
def askB : Fin 4 → Fin 2 → ℝ := fun θ d => if d = crossingB θ then 1 else 0

theorem askA_unit (θ : Fin 4) (d : Fin 2) : askA θ d ∈ Set.Icc (0 : ℝ) 1 := by
  unfold askA; split_ifs <;> norm_num

theorem askB_unit (θ : Fin 4) (d : Fin 2) : askB θ d ∈ Set.Icc (0 : ℝ) 1 := by
  unfold askB; split_ifs <;> norm_num

theorem value_A_askA : finiteBayesValue testA crossingPrior askA = 1 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testA, deterministicExperiment, askA, crossingPrior, crossingA, Fin.sum_univ_succ] <;>
    norm_num [max_def]

theorem value_B_askA : finiteBayesValue testB crossingPrior askA = 9 / 10 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testB, deterministicExperiment, askA, crossingPrior, crossingA, crossingB, Fin.sum_univ_succ] <;>
    norm_num [max_def]

theorem value_A_askB : finiteBayesValue testA crossingPrior askB = 9 / 10 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testA, deterministicExperiment, askB, crossingPrior, crossingA, crossingB, Fin.sum_univ_succ] <;>
    norm_num [max_def]

theorem value_B_askB : finiteBayesValue testB crossingPrior askB = 1 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testB, deterministicExperiment, askB, crossingPrior, crossingB, Fin.sum_univ_succ] <;>
    norm_num [max_def]

/-- Values of recorded mixtures are the `r`-mixtures of the pure values. -/
theorem value_recordedMixture {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (α : Fin 4 → ℝ)
    (u : Fin 4 → Fin 2 → ℝ) :
    finiteBayesValue (recordedMixture r) α u =
      r * finiteBayesValue testA α u + (1 - r) * finiteBayesValue testB α u := by
  rw [recordedMixture_eq_mixtureCollector]
  have h := purposeValue_mixtureCollector (Y := Fin 2) ![testA, testB] ![r, 1 - r]
    (by intro i; fin_cases i <;> simp <;> linarith) (α, u)
  simp only [purposeValue, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h
  exact h

theorem value_mixture_askA {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteBayesValue (recordedMixture r) crossingPrior askA = 9 / 10 + r / 10 := by
  rw [value_recordedMixture hr0 hr1, value_A_askA, value_B_askA]; ring

theorem value_mixture_askB {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteBayesValue (recordedMixture r) crossingPrior askB = 1 - r / 10 := by
  rw [value_recordedMixture hr0 hr1, value_A_askB, value_B_askB]; ring

/-! ## The uniform witnesses -/

/-- Equal mass on `00` and `10`. -/
def priorA : Fin 4 → ℝ := ![1 / 2, 0, 1 / 2, 0]

/-- Equal mass on `01` and `10`. -/
def priorB : Fin 4 → ℝ := ![0, 1 / 2, 1 / 2, 0]

theorem priorA_isDist : IsDist priorA := by
  refine ⟨fun θ => ?_, ?_⟩
  · fin_cases θ <;> simp [priorA]
  · norm_num [priorA, Fin.sum_univ_succ]

theorem priorB_isDist : IsDist priorB := by
  refine ⟨fun θ => ?_, ?_⟩
  · fin_cases θ <;> simp [priorB]
  · norm_num [priorB, Fin.sum_univ_succ]

theorem valueA_A_priorA : finiteBayesValue testA priorA askA = 1 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testA, deterministicExperiment, askA, priorA, crossingA, Fin.sum_univ_succ] <;>
    norm_num [max_def]

theorem valueB_A_priorA : finiteBayesValue testB priorA askA = 1 / 2 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testB, deterministicExperiment, askA, priorA, crossingA, crossingB, Fin.sum_univ_succ] <;>
    norm_num [max_def]

theorem valueA_B_priorB : finiteBayesValue testA priorB askB = 1 / 2 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testA, deterministicExperiment, askB, priorB, crossingA, crossingB, Fin.sum_univ_succ] <;>
    norm_num [max_def]

theorem valueB_B_priorB : finiteBayesValue testB priorB askB = 1 := by
  simp only [finiteBayesValue, finiteDecisionScore, sup'_univ_fin_two]
  simp [testB, deterministicExperiment, askB, priorB, crossingB, Fin.sum_univ_succ] <;>
    norm_num [max_def]

/-- `V_{P_A}(E_r) = (1 + r)/2`. -/
theorem value_mixture_priorA {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteBayesValue (recordedMixture r) priorA askA = (1 + r) / 2 := by
  rw [value_recordedMixture hr0 hr1, valueA_A_priorA, valueB_A_priorA]; ring

/-- `V_{P_B}(E_r) = 1 − r/2`. -/
theorem value_mixture_priorB {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteBayesValue (recordedMixture r) priorB askB = 1 - r / 2 := by
  rw [value_recordedMixture hr0 hr1, valueA_B_priorB, valueB_B_priorB]; ring

/-- The benchmark of `P_A` over the targets `{A, B}` is one, and the regret of
`E_r` is `(1 − r)/2`. -/
theorem regret_priorA {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    benchmark ![testA, testB] ((priorA, askA) : Purpose (Fin 4) (Fin 2)) = 1 ∧
    benchmark ![testA, testB] ((priorA, askA) : Purpose (Fin 4) (Fin 2)) -
      purposeValue (recordedMixture r) (priorA, askA) = (1 - r) / 2 := by
  have hb : benchmark ![testA, testB] ((priorA, askA) : Purpose (Fin 4) (Fin 2)) = 1 := by
    unfold benchmark
    rw [sup'_univ_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, purposeValue,
      valueA_A_priorA, valueB_A_priorA]
    norm_num
  refine ⟨hb, ?_⟩
  rw [hb]
  show 1 - finiteBayesValue (recordedMixture r) priorA askA = (1 - r) / 2
  rw [value_mixture_priorA hr0 hr1]; ring

/-- The benchmark of `P_B` is one, and the regret of `E_r` is `r/2`. -/
theorem regret_priorB {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    benchmark ![testA, testB] ((priorB, askB) : Purpose (Fin 4) (Fin 2)) = 1 ∧
    benchmark ![testA, testB] ((priorB, askB) : Purpose (Fin 4) (Fin 2)) -
      purposeValue (recordedMixture r) (priorB, askB) = r / 2 := by
  have hb : benchmark ![testA, testB] ((priorB, askB) : Purpose (Fin 4) (Fin 2)) = 1 := by
    unfold benchmark
    rw [sup'_univ_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, purposeValue,
      valueA_B_priorB, valueB_B_priorB]
    norm_num
  refine ⟨hb, ?_⟩
  rw [hb]
  show 1 - finiteBayesValue (recordedMixture r) priorB askB = r / 2
  rw [value_mixture_priorB hr0 hr1]; ring

/-! ## The decision distance between two mixtures -/

/-- Retain probability `t` of each `A`-labelled signal; turn the rest into a
fair `B` answer; keep every `B`-labelled signal. -/
def shrinkA (t : ℝ) : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℝ := fun z z' =>
  if z.1 = 0 then (if z'.1 = 0 then (if z'.2 = z.2 then t else 0) else (1 - t) / 2)
  else (if z'.1 = 1 then (if z'.2 = z.2 then 1 else 0) else 0)

/-- The mirror image: retain probability `t` of each `B`-labelled signal; turn
the rest into a fair `A` answer; keep every `A`-labelled signal. -/
def shrinkB (t : ℝ) : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℝ := fun z z' =>
  if z.1 = 1 then (if z'.1 = 1 then (if z'.2 = z.2 then t else 0) else (1 - t) / 2)
  else (if z'.1 = 0 then (if z'.2 = z.2 then 1 else 0) else 0)

theorem shrinkA_stochastic {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    shrinkA t ∈ stochasticRules (Fin 2 × Fin 2) (Fin 2 × Fin 2) := by
  rintro ⟨c, o⟩ _
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine ⟨fun z' => ?_, ?_⟩
  · unfold shrinkA; split_ifs <;> linarith
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases c <;> fin_cases o <;> simp [shrinkA, Fin.sum_univ_two, h10] <;> ring

theorem shrinkB_stochastic {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    shrinkB t ∈ stochasticRules (Fin 2 × Fin 2) (Fin 2 × Fin 2) := by
  rintro ⟨c, o⟩ _
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  refine ⟨fun z' => ?_, ?_⟩
  · unfold shrinkB; split_ifs <;> linarith
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases c <;> fin_cases o <;> simp [shrinkB, Fin.sum_univ_two, h10, h01] <;> ring

theorem decisionLaw_shrinkA (r t : ℝ) (θ : Fin 4) :
    finiteDecisionLaw (recordedMixture r) (shrinkA t) θ = fun z =>
      if z.1 = 0 then r * t * testA θ z.2 else r * (1 - t) / 2 + (1 - r) * testB θ z.2 := by
  funext ⟨c', o'⟩
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  unfold finiteDecisionLaw recordedMixture shrinkA
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases c' <;>
    simp only [Fin.zero_eta, Fin.mk_one, h10, h01, ↓reduceIte, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, Finset.sum_const_zero, add_zero,
      zero_add, ← Finset.sum_mul, ← Finset.mul_sum, (testA_valid θ).2, (testB_valid θ).2] <;>
    ring

theorem decisionLaw_shrinkB (r t : ℝ) (θ : Fin 4) :
    finiteDecisionLaw (recordedMixture r) (shrinkB t) θ = fun z =>
      if z.1 = 0 then r * testA θ z.2 + (1 - r) * (1 - t) / 2 else (1 - r) * t * testB θ z.2 := by
  funext ⟨c', o'⟩
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  unfold finiteDecisionLaw recordedMixture shrinkB
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases c' <;>
    simp only [Fin.zero_eta, Fin.mk_one, h10, h01, ↓reduceIte, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, Finset.sum_const_zero, add_zero,
      zero_add, ← Finset.sum_mul, ← Finset.mul_sum, (testA_valid θ).2, (testB_valid θ).2] <;>
    ring

theorem testA_bit (θ : Fin 4) (o : Fin 2) : testA θ o = 0 ∨ testA θ o = 1 := by
  unfold testA deterministicExperiment; split_ifs <;> simp

theorem testB_bit (θ : Fin 4) (o : Fin 2) : testB θ o = 0 ∨ testB θ o = 1 := by
  unfold testB deterministicExperiment; split_ifs <;> simp

theorem abs_half_sub_mul_bit (c b : ℝ) (hc : 0 ≤ c) (hb : b = 0 ∨ b = 1) :
    |c / 2 - c * b| = c / 2 := by
  rcases hb with rfl | rfl
  · rw [mul_zero, sub_zero, abs_of_nonneg (by linarith)]
  · rw [mul_one, abs_of_nonpos (by linarith)]; ring

/-- Row-TV error of the `A`-shrinking decoder for `s ≤ r`: `(r − s)/2`. -/
theorem shrinkA_error {r s : ℝ} (hs0 : 0 ≤ s) (hsr : s ≤ r) (hr1 : r ≤ 1) (θ : Fin 4) :
    finiteTV (finiteDecisionLaw (recordedMixture r) (shrinkA (s / r)) θ) (recordedMixture s θ) =
      (r - s) / 2 := by
  have hrt : r * (s / r) = s := by
    by_cases hr : r = 0
    · have : s = 0 := le_antisymm (hr ▸ hsr) hs0
      rw [hr, this, zero_mul]
    · field_simp
  have hrt' : r * (1 - s / r) = r - s := by
    rw [mul_sub, mul_one, hrt]
  rw [decisionLaw_shrinkA]
  unfold finiteTV recordedMixture
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte, hrt, hrt', sub_self, abs_zero, Finset.sum_const_zero, zero_add]
  have hterm : ∀ o, |(r - s) / 2 + (1 - r) * testB θ o - (1 - s) * testB θ o| = (r - s) / 2 := by
    intro o
    rw [show (r - s) / 2 + (1 - r) * testB θ o - (1 - s) * testB θ o =
      (r - s) / 2 - (r - s) * testB θ o by ring]
    exact abs_half_sub_mul_bit (r - s) (testB θ o) (by linarith) (testB_bit θ o)
  simp only [hterm, Fin.sum_univ_two]
  ring

/-- Row-TV error of the `B`-shrinking decoder for `r ≤ s`: `(s − r)/2`. -/
theorem shrinkB_error {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s ≤ 1) (θ : Fin 4) :
    finiteTV (finiteDecisionLaw (recordedMixture r) (shrinkB ((1 - s) / (1 - r))) θ)
      (recordedMixture s θ) = (s - r) / 2 := by
  have hrt : (1 - r) * ((1 - s) / (1 - r)) = 1 - s := by
    by_cases hr : 1 - r = 0
    · have : s = 1 := le_antisymm hs1 (by linarith)
      rw [hr, this, zero_mul, sub_self]
    · field_simp
  have hrt' : (1 - r) * (1 - (1 - s) / (1 - r)) / 2 = (s - r) / 2 := by
    rw [mul_sub, mul_one, hrt]; ring
  rw [decisionLaw_shrinkB]
  unfold finiteTV recordedMixture
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte, hrt, hrt', sub_self, abs_zero, Finset.sum_const_zero, add_zero]
  have hterm : ∀ o, |r * testA θ o + (s - r) / 2 - s * testA θ o| = (s - r) / 2 := by
    intro o
    rw [show r * testA θ o + (s - r) / 2 - s * testA θ o =
      (s - r) / 2 - (s - r) * testA θ o by ring]
    exact abs_half_sub_mul_bit (s - r) (testA θ o) (by linarith) (testA_bit θ o)
  simp only [hterm, Fin.sum_univ_two]
  ring

/-- Lower bounds from the two witnesses. -/
theorem abs_sub_div_two_le_deficiency {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |r - s| / 2 ≤ finiteDeficiency (recordedMixture r) (recordedMixture s) := by
  have hA := finiteBayesValue_sub_le_finiteDeficiency (recordedMixture r) (recordedMixture s)
    (recordedMixture_valid hr0 hr1) (recordedMixture_valid hs0 hs1) priorA priorA_isDist askA
    askA_unit
  have hB := finiteBayesValue_sub_le_finiteDeficiency (recordedMixture r) (recordedMixture s)
    (recordedMixture_valid hr0 hr1) (recordedMixture_valid hs0 hs1) priorB priorB_isDist askB
    askB_unit
  rw [value_mixture_priorA hs0 hs1, value_mixture_priorA hr0 hr1] at hA
  rw [value_mixture_priorB hs0 hs1, value_mixture_priorB hr0 hr1] at hB
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **The decision distance between two recorded mixtures**: `δ(E_r, E_s) = |r − s|/2`. -/
theorem deficiency_recordedMixture_pair {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    finiteDeficiency (recordedMixture r) (recordedMixture s) = |r - s| / 2 := by
  apply le_antisymm _ (abs_sub_div_two_le_deficiency hr0 hr1 hs0 hs1)
  rcases le_total s r with hsr | hrs
  · rw [abs_of_nonneg (by linarith)]
    have ht0 : 0 ≤ s / r := div_nonneg hs0 (by linarith)
    have ht1 : s / r ≤ 1 := by
      by_cases hr : r = 0
      · rw [hr, div_zero]; norm_num
      · rw [div_le_one (lt_of_le_of_ne (by linarith) (Ne.symm hr))]; exact hsr
    exact finiteDeficiency_le_of_decoder _ _ (shrinkA (s / r)) (shrinkA_stochastic ht0 ht1) _
      fun θ => (shrinkA_error hs0 hsr hr1 θ).le
  · rw [abs_of_nonpos (by linarith)]
    have ht0 : 0 ≤ (1 - s) / (1 - r) := div_nonneg (by linarith) (by linarith)
    have ht1 : (1 - s) / (1 - r) ≤ 1 := by
      by_cases hr : 1 - r = 0
      · rw [hr, div_zero]; norm_num
      · rw [div_le_one (lt_of_le_of_ne (by linarith) (Ne.symm hr))]; linarith
    have h := finiteDeficiency_le_of_decoder _ _ (shrinkB ((1 - s) / (1 - r)))
      (shrinkB_stochastic ht0 ht1) _ fun θ => (shrinkB_error hr0 hrs hs1 θ).le
    calc finiteDeficiency (recordedMixture r) (recordedMixture s) ≤ (s - r) / 2 := h
      _ = -(r - s) / 2 := by ring

/-- The displayed identity: the two witnesses' value gaps recover the distance. -/
theorem deficiency_recordedMixture_eq_max_gaps {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    finiteDeficiency (recordedMixture r) (recordedMixture s) =
      max 0 (max (finiteBayesValue (recordedMixture s) priorA askA -
          finiteBayesValue (recordedMixture r) priorA askA)
        (finiteBayesValue (recordedMixture s) priorB askB -
          finiteBayesValue (recordedMixture r) priorB askB)) := by
  rw [deficiency_recordedMixture_pair hr0 hr1 hs0 hs1, value_mixture_priorA hs0 hs1,
    value_mixture_priorA hr0 hr1, value_mixture_priorB hs0 hs1, value_mixture_priorB hr0 hr1]
  rcases le_total s r with hsr | hrs
  · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith : (1 + s) / 2 - (1 + r) / 2 ≤
      1 - s / 2 - (1 - r / 2)), max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith : 1 - s / 2 - (1 - r / 2) ≤
      (1 + s) / 2 - (1 + r) / 2), max_eq_right (by linarith)]
    ring

/-- **Distinct mixtures are incomparable**, whatever their audits. -/
theorem recordedMixtures_incomparable {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hrs : r ≠ s) :
    0 < finiteDeficiency (recordedMixture r) (recordedMixture s) ∧
    0 < finiteDeficiency (recordedMixture s) (recordedMixture r) := by
  rw [deficiency_recordedMixture_pair hr0 hr1 hs0 hs1,
    deficiency_recordedMixture_pair hs0 hs1 hr0 hr1]
  have h1 : 0 < |r - s| := abs_pos.2 (sub_ne_zero.2 hrs)
  have h2 : 0 < |s - r| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hrs))
  constructor <;> positivity

/-- The two witness regrets recover the audit `½·max{r, 1 − r}`. -/
theorem max_regrets_eq_audit {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    max ((1 - r) / 2) (r / 2) = recordedMixtureAudit r := by
  rw [recordedMixtureAudit_eq hr0 hr1]
  rcases le_total r (1 - r) with h | h
  · rw [max_eq_left (by linarith), max_eq_right h]; ring
  · rw [max_eq_right (by linarith), max_eq_left h]; ring

end

end IdExp
