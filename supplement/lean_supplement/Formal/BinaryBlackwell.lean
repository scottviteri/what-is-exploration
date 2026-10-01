import Formal.BinaryDeficiencyIdentity
import Formal.FiniteDecoderAttainment

/-!
# Attainment of the deficiency infimum and the exact binary Blackwell theorem

Three results that close the two-world coherence argument at the matrix level.

* **Attainment.**  The finite deficiency `finiteDeficiency E F` is an infimum
  over stochastic decoders.  The decoder set is compact and the worst-world
  decoding error is continuous, so some decoder attains the infimum exactly.
  Consequently `finiteDeficiency E F = 0` gives an exact stochastic garbling.

* **Binary Blackwell.**  For valid two-world experiments, `F` is an exact
  stochastic garbling of `E` (`FiniteBlackwellLE F E`) if and only if the
  posterior-score call function of `F` lies below that of `E` on `[0, 1]`.
  The easy direction pulls the positive-score event back through the
  garbling; the hard direction combines the binary deficiency identity
  `finiteDeficiency E F = binaryCallGap E F` with attainment.

* **Unnormalized form.**  For nonnegative two-row matrices, exact garbling is
  equivalent to equal row totals together with call-function order.  A strike
  reparametrization reduces the positive-total case to the valid case; a zero
  row total makes the target a constant-decoder garbling.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {Θ X Y : Type*} [Fintype X] [Fintype Y]

/-! ### The exact binary Blackwell theorem -/

/-- An exact stochastic garbling never raises the call function.  No
normalization is needed: the positive-score event of the target pulls back
through the garbling to a randomized event of the source. -/
theorem binaryCall_le_of_stochasticGarbling
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (hEF : ∀ b y, F b y = ∑ x, E b x * G x y) (k : ℝ) :
    binaryCall F k ≤ binaryCall E k := by
  let u : Y → ℝ := binaryCallEvent F k
  let v : X → ℝ := fun x => ∑ y, G x y * u y
  have hu0 : ∀ y, 0 ≤ u y := fun y => binaryCallEvent_nonneg F k y
  have hu1 : ∀ y, u y ≤ 1 := fun y => binaryCallEvent_le_one F k y
  have hv0 : ∀ x, 0 ≤ v x := by
    intro x
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg ((hG x (Set.mem_univ x)).1 y) (hu0 y)
  have hv1 : ∀ x, v x ≤ 1 := by
    intro x
    calc
      v x = ∑ y, G x y * u y := rfl
      _ ≤ ∑ y, G x y * 1 := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hu1 y) ((hG x (Set.mem_univ x)).1 y)
      _ = 1 := by simpa using (hG x (Set.mem_univ x)).2
  have hrow : ∀ b : Bool, (∑ y, F b y * u y) = ∑ x, E b x * v x := by
    intro b
    simp_rw [hEF b]
    exact (sum_mul_decoderPullback (E b) G u).symm
  calc
    binaryCall F k = (1 - k) * (∑ y, F true y * u y) - k * (∑ y, F false y * u y) :=
      (binaryCallEvent_score F k).symm
    _ = (1 - k) * (∑ x, E true x * v x) - k * (∑ x, E false x * v x) := by
      rw [hrow true, hrow false]
    _ ≤ binaryCall E k := binaryEventScore_le_call E k v hv0 hv1

/-- Easy direction of binary Blackwell: matrix garbling lowers every call value. -/
theorem binaryCall_le_of_finiteBlackwellLE
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (h : FiniteBlackwellLE F E) (k : ℝ) :
    binaryCall F k ≤ binaryCall E k := by
  obtain ⟨G, hG, hEG⟩ := h
  exact binaryCall_le_of_stochasticGarbling E F G hG
    (fun b y => (congrFun (congrFun hEG b) y).symm) k

/-- Call order on `[0, 1]` makes the optimized call gap nonpositive. -/
theorem binaryCallGap_nonpos_of_binaryCall_le
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hcall : ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k) :
    binaryCallGap E F ≤ 0 := by
  unfold binaryCallGap
  apply csSup_le (binaryCallGapValues_nonempty E F hE hF)
  rintro d ⟨k, hk, rfl⟩
  exact sub_nonpos.mpr (hcall k hk)

/-- Hard direction of binary Blackwell: call order on `[0, 1]` forces an exact
stochastic garbling.  The binary deficiency identity gives zero deficiency,
and attainment turns zero deficiency into an exact decoder. -/
theorem finiteBlackwellLE_of_binaryCall_le
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hcall : ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k) :
    FiniteBlackwellLE F E := by
  have : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  apply finiteBlackwellLE_of_finiteDeficiency_eq_zero
  refine le_antisymm ?_ (finiteDeficiency_nonneg_of_fintype E F)
  exact (finiteDeficiency_le_binaryCallGap E F hE hF).trans
    (binaryCallGap_nonpos_of_binaryCall_le E F hE hF hcall)

/-- **The exact binary Blackwell theorem.**  For valid two-world finite
experiments, `F` is an exact stochastic garbling of `E` if and only if the
posterior-score call function of `F` is below that of `E` at every strike in
`[0, 1]`. -/
theorem finiteBlackwellLE_iff_binaryCall_le
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    FiniteBlackwellLE F E ↔
      ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k :=
  ⟨fun h k _ => binaryCall_le_of_finiteBlackwellLE E F h k,
    finiteBlackwellLE_of_binaryCall_le E F hE hF⟩

/-- Garbling form of the binary Blackwell theorem: the matrix statement with
the garbling written as an explicit row-stochastic matrix. -/
theorem exists_garbling_iff_binaryCall_le_of_valid
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    (∃ G ∈ stochasticRules X Y, ∀ b y, ∑ x, E b x * G x y = F b y) ↔
      ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k := by
  rw [← finiteBlackwellLE_iff_binaryCall_le E F hE hF]
  constructor
  · rintro ⟨G, hG, h⟩
    exact ⟨G, hG, funext fun b => funext fun y => h b y⟩
  · rintro ⟨G, hG, h⟩
    exact ⟨G, hG, fun b y => congrFun (congrFun h b) y⟩

/-- Quantitative form: the optimized call gap is attained by one decoder
uniformly over both worlds. -/
theorem exists_decoder_le_binaryCallGap
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    ∃ G ∈ stochasticRules X Y, ∀ b, decodeErr E F G b ≤ binaryCallGap E F := by
  have : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  rw [← finiteDeficiency_eq_binaryCallGap E F hE hF]
  exact exists_decoder_eq_finiteDeficiency E F

/-! ### The unnormalized form: equal row totals and call order -/

/-- A stochastic garbling preserves row totals. -/
theorem sum_eq_of_stochasticGarbling
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (hEF : ∀ θ y, ∑ x, E θ x * G x y = F θ y) (θ : Θ) :
    ∑ x, E θ x = ∑ y, F θ y := by
  simp_rw [← hEF θ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, (hG x (Set.mem_univ x)).2, mul_one]

/-- The strike-reparametrization denominator is positive on `[0, 1]`. -/
theorem rescaleDenom_pos_bool {t : Bool → ℝ} (h0 : 0 < t false) (h1 : 0 < t true)
    {k : ℝ} (hk : k ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 - k) * t false + k * t true := by
  obtain ⟨hk0, hk1⟩ := hk
  rcases hk1.lt_or_eq with hlt | heq
  · have : 0 < (1 - k) * t false := mul_pos (by linarith) h0
    nlinarith [mul_nonneg hk0 h1.le]
  · subst heq
    simpa using h1

/-- The reparametrized strike stays in `[0, 1]`. -/
theorem rescaleStrike_mem_Icc_bool {t : Bool → ℝ} (h0 : 0 < t false) (h1 : 0 < t true)
    {k : ℝ} (hk : k ∈ Set.Icc (0 : ℝ) 1) :
    k * t true / ((1 - k) * t false + k * t true) ∈ Set.Icc (0 : ℝ) 1 := by
  have hD := rescaleDenom_pos_bool h0 h1 hk
  obtain ⟨hk0, hk1⟩ := hk
  constructor
  · exact div_nonneg (mul_nonneg hk0 h1.le) hD.le
  · rw [div_le_one hD]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) h0.le]

/-- **Strike reparametrization under row rescaling.**  Dividing the rows of a
two-row matrix by positive weights `t` multiplies the call function by a
positive factor depending only on `k` and `t`, and moves the strike to
`k t₁ / ((1 - k) t₀ + k t₁)`.  The factor and the new strike are the same for
every matrix with the same weights, so call order is invariant under a common
row rescaling. -/
theorem binaryCall_rowNormalize (E : FiniteExperiment Bool X) (t : Bool → ℝ)
    (h0 : 0 < t false) (h1 : 0 < t true) (k : ℝ) (hk : k ∈ Set.Icc (0 : ℝ) 1) :
    binaryCall (fun b x => E b x / t b) k =
      (((1 - k) * t false + k * t true) / (t false * t true)) *
        binaryCall E (k * t true / ((1 - k) * t false + k * t true)) := by
  have hD := rescaleDenom_pos_bool h0 h1 hk
  have hc : 0 ≤ ((1 - k) * t false + k * t true) / (t false * t true) :=
    div_nonneg hD.le (mul_pos h0 h1).le
  unfold binaryCall
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_max_of_nonneg _ _ hc, mul_zero]
  congr 1
  field_simp
  ring

/-- Row normalization of a nonnegative matrix with positive row totals is a
valid experiment. -/
theorem isFiniteExperiment_rowNormalize (E : FiniteExperiment Bool X)
    (hE : ∀ b x, 0 ≤ E b x) (t : Bool → ℝ) (ht : ∀ b, t b = ∑ x, E b x)
    (hpos : ∀ b, 0 < t b) :
    IsFiniteExperiment (fun b x => E b x / t b) := by
  intro b
  refine ⟨fun x => div_nonneg (hE b x) (hpos b).le, ?_⟩
  simp only
  rw [← Finset.sum_div, ← ht b, div_self (hpos b).ne']

/-- Call order on `[0, 1]` is invariant under a common row rescaling. -/
theorem binaryCall_rowRescale_le
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y) (t : Bool → ℝ)
    (h0 : 0 < t false) (h1 : 0 < t true)
    (hcall : ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k) :
    ∀ k ∈ Set.Icc (0 : ℝ) 1,
      binaryCall (fun b y => F b y / t b) k ≤ binaryCall (fun b x => E b x / t b) k := by
  intro k hk
  rw [binaryCall_rowNormalize E t h0 h1 k hk, binaryCall_rowNormalize F t h0 h1 k hk]
  exact mul_le_mul_of_nonneg_left (hcall _ (rescaleStrike_mem_Icc_bool h0 h1 hk))
    (div_nonneg (rescaleDenom_pos_bool h0 h1 hk).le (mul_pos h0 h1).le)

/-- A nonnegative row with zero total vanishes. -/
theorem row_eq_zero_of_sum_eq_zero (E : FiniteExperiment Θ X) (θ : Θ)
    (hE : ∀ x, 0 ≤ E θ x) (h : ∑ x, E θ x = 0) : ∀ x, E θ x = 0 := fun x =>
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hE x)).1 h x (Finset.mem_univ x)

/-- Positive-total case of the unnormalized binary Blackwell theorem: normalize
both matrices by the common row totals, apply the valid case, and scale back. -/
theorem exists_garbling_of_binaryCall_le_of_pos
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : ∀ b x, 0 ≤ E b x) (hF : ∀ b y, 0 ≤ F b y)
    (htot : ∀ b, ∑ x, E b x = ∑ y, F b y)
    (hpos : ∀ b, 0 < ∑ x, E b x)
    (hcall : ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k) :
    ∃ G ∈ stochasticRules X Y, ∀ b y, ∑ x, E b x * G x y = F b y := by
  set t : Bool → ℝ := fun b => ∑ x, E b x with ht
  have hE' : IsFiniteExperiment (fun b x => E b x / t b) :=
    isFiniteExperiment_rowNormalize E hE t (fun b => rfl) hpos
  have hF' : IsFiniteExperiment (fun b y => F b y / t b) :=
    isFiniteExperiment_rowNormalize F hF t (fun b => htot b) hpos
  obtain ⟨G, hG, hEG⟩ := finiteBlackwellLE_of_binaryCall_le _ _ hE' hF'
    (binaryCall_rowRescale_le E F t (hpos false) (hpos true) hcall)
  refine ⟨G, hG, fun b y => ?_⟩
  have h := congrFun (congrFun hEG b) y
  simp only [finiteDecisionLaw] at h
  have htb : t b ≠ 0 := (hpos b).ne'
  calc
    ∑ x, E b x * G x y = t b * ∑ x, E b x / t b * G x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      field_simp
    _ = t b * (F b y / t b) := by rw [h]
    _ = F b y := by field_simp

/-- Degenerate case of the unnormalized binary Blackwell theorem: one row
total is zero, so that row vanishes in both matrices and the other row of the
target is reproduced by a signal-independent decoder.  No call hypothesis is
needed. -/
theorem exists_garbling_of_row_sum_eq_zero [Nonempty Y]
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : ∀ b x, 0 ≤ E b x) (hF : ∀ b y, 0 ≤ F b y)
    (htot : ∀ b, ∑ x, E b x = ∑ y, F b y)
    (b0 : Bool) (hb0 : ∑ x, E b0 x = 0) :
    ∃ G ∈ stochasticRules X Y, ∀ b y, ∑ x, E b x * G x y = F b y := by
  classical
  have hE0 : ∀ x, E b0 x = 0 := row_eq_zero_of_sum_eq_zero E b0 (hE b0) hb0
  have hF0 : ∀ y, F b0 y = 0 :=
    row_eq_zero_of_sum_eq_zero F b0 (hF b0) (by rw [← htot b0, hb0])
  have hcases : ∀ b : Bool, b = b0 ∨ b = !b0 := by
    intro b; cases b <;> cases b0 <;> simp
  by_cases h1 : ∑ x, E (!b0) x = 0
  · have hE1 : ∀ x, E (!b0) x = 0 := row_eq_zero_of_sum_eq_zero E (!b0) (hE _) h1
    have hF1 : ∀ y, F (!b0) y = 0 :=
      row_eq_zero_of_sum_eq_zero F (!b0) (hF _) (by rw [← htot (!b0), h1])
    obtain ⟨G, hG⟩ := stochasticRules_nonempty_of_nonempty (X := X) (Y := Y)
    refine ⟨G, hG, fun b y => ?_⟩
    rcases hcases b with rfl | rfl
    · simp [hE0, hF0]
    · simp [hE1, hF1]
  · refine ⟨fun _ y => F (!b0) y / ∑ y', F (!b0) y',
      fun x _ => ⟨fun y => ?_, ?_⟩, fun b y => ?_⟩
    · exact div_nonneg (hF _ y) (Finset.sum_nonneg fun y' _ => hF _ y')
    · rw [← Finset.sum_div, div_self]
      rwa [← htot]
    · rw [← Finset.sum_mul]
      rcases hcases b with rfl | rfl
      · rw [hb0, hF0, zero_mul]
      · rw [htot]
        have hne : ∑ y', F (!b0) y' ≠ 0 := by rwa [← htot]
        field_simp

/-- **Unnormalized binary Blackwell, hard direction (finite Strassen).**  For
nonnegative two-row matrices with equal row totals, call order on `[0, 1]`
yields an exact row-stochastic garbling.  Normalization happens exactly once,
here, through the strike reparametrization; a zero row total is handled by a
signal-independent decoder. -/
theorem exists_garbling_of_binaryCall_le [Nonempty Y]
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : ∀ b x, 0 ≤ E b x) (hF : ∀ b y, 0 ≤ F b y)
    (htot : ∀ b, ∑ x, E b x = ∑ y, F b y)
    (hcall : ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k) :
    ∃ G ∈ stochasticRules X Y, ∀ b y, ∑ x, E b x * G x y = F b y := by
  by_cases hpos : ∀ b, 0 < ∑ x, E b x
  · exact exists_garbling_of_binaryCall_le_of_pos E F hE hF htot hpos hcall
  · push Not at hpos
    obtain ⟨b0, hb0⟩ := hpos
    exact exists_garbling_of_row_sum_eq_zero E F hE hF htot b0
      (le_antisymm hb0 (Finset.sum_nonneg fun x _ => hE b0 x))

/-- **Unnormalized binary Blackwell theorem.**  For nonnegative two-row
matrices, `F` is an exact row-stochastic garbling of `E` if and only if the
row totals agree and the call function of `F` lies below that of `E` on
`[0, 1]`.  This is the convex-order characterization used by the two-world
coherence induction, with convex order encoded as call order plus equal
totals. -/
theorem exists_garbling_iff_binaryCall_le [Nonempty Y]
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : ∀ b x, 0 ≤ E b x) (hF : ∀ b y, 0 ≤ F b y) :
    (∃ G ∈ stochasticRules X Y, ∀ b y, ∑ x, E b x * G x y = F b y) ↔
      (∀ b, ∑ x, E b x = ∑ y, F b y) ∧
        ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k := by
  constructor
  · rintro ⟨G, hG, hEG⟩
    exact ⟨sum_eq_of_stochasticGarbling E F G hG hEG,
      fun k _ => binaryCall_le_of_stochasticGarbling E F G hG
        (fun b y => (hEG b y).symm) k⟩
  · rintro ⟨htot, hcall⟩
    exact exists_garbling_of_binaryCall_le E F hE hF htot hcall

/-- Unnormalized binary Blackwell in `FiniteBlackwellLE` form. -/
theorem finiteBlackwellLE_iff_binaryCall_le_of_nonneg [Nonempty Y]
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : ∀ b x, 0 ≤ E b x) (hF : ∀ b y, 0 ≤ F b y) :
    FiniteBlackwellLE F E ↔
      (∀ b, ∑ x, E b x = ∑ y, F b y) ∧
        ∀ k ∈ Set.Icc (0 : ℝ) 1, binaryCall F k ≤ binaryCall E k := by
  rw [← exists_garbling_iff_binaryCall_le E F hE hF]
  constructor
  · rintro ⟨G, hG, h⟩
    exact ⟨G, hG, fun b y => congrFun (congrFun h b) y⟩
  · rintro ⟨G, hG, h⟩
    exact ⟨G, hG, funext fun b => funext fun y => h b y⟩

end IdExp
