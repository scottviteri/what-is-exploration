import Formal.EffectiveBinary
import Formal.DeficiencyTriangle

/-!
# The two-world call-function lower bound

For a finite experiment on two worlds, the posterior-score call function is
the support function of its receiver-operating-characteristic region. This
module formalizes the support-function half of the binary randomization
criterion:

    sup over k in [0,1] of (call F k - call E k) <= deficiency E F.

The proof is constructive at a fixed decoder. The positive-score event of the
target is pulled back through the decoder, bounded by the source call
function, and the two remaining expectation errors are controlled sharply by
the rowwise total-variation errors.

The reverse inequality is checked in `BinaryDeficiencyIdentity.lean` using
the strong duality of `DeficiencyDuality.lean` and a reduction of dual convex
piecewise-linear payoffs to call payoffs. `BinaryBlackwell.lean` supplies the
exact comparison criterion. Shadow allocation and all-depth causal-tree
gluing still remain outside Lean; the binary matrix identity alone is not the
paper's causal coherence theorem.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The binary posterior-score call function, in the paper's prior-free
two-row coordinates. The false row is world zero and the true row is world
one. -/
noncomputable def binaryCall
    (E : FiniteExperiment Bool X) (k : Real) : Real :=
  ∑ x, max ((1 - k) * E true x - k * E false x) 0

/-- The deterministic event attaining the call support function. -/
noncomputable def binaryCallEvent
    (E : FiniteExperiment Bool X) (k : Real) (x : X) : Real :=
  if 0 <= (1 - k) * E true x - k * E false x then 1 else 0

theorem binaryCallEvent_nonneg
    (E : FiniteExperiment Bool X) (k : Real) :
    forall x, 0 <= binaryCallEvent E k x := by
  classical
  intro x
  unfold binaryCallEvent
  split <;> norm_num

theorem binaryCallEvent_le_one
    (E : FiniteExperiment Bool X) (k : Real) :
    forall x, binaryCallEvent E k x <= 1 := by
  classical
  intro x
  unfold binaryCallEvent
  split <;> norm_num

/-- Every randomized event has binary score at most the call function. -/
theorem binaryEventScore_le_call
    (E : FiniteExperiment Bool X) (k : Real) (u : X -> Real)
    (hu0 : forall x, 0 <= u x) (hu1 : forall x, u x <= 1) :
    (1 - k) * (∑ x, E true x * u x) -
        k * (∑ x, E false x * u x) <=
      binaryCall E k := by
  unfold binaryCall
  calc
    (1 - k) * (∑ x, E true x * u x) -
        k * (∑ x, E false x * u x) =
      ∑ x, (((1 - k) * E true x - k * E false x) * u x) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ <= ∑ x, max ((1 - k) * E true x - k * E false x) 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases h : 0 <= (1 - k) * E true x - k * E false x
      · rw [max_eq_left h]
        exact mul_le_of_le_one_right h (hu1 x)
      · have hn : (1 - k) * E true x - k * E false x <= 0 :=
          le_of_not_ge h
        rw [max_eq_right hn]
        exact mul_nonpos_of_nonpos_of_nonneg hn (hu0 x)

/-- The positive-score event attains the binary call function exactly. -/
theorem binaryCallEvent_score
    (E : FiniteExperiment Bool X) (k : Real) :
    (1 - k) * (∑ x, E true x * binaryCallEvent E k x) -
        k * (∑ x, E false x * binaryCallEvent E k x) =
      binaryCall E k := by
  classical
  unfold binaryCall
  calc
    (1 - k) * (∑ x, E true x * binaryCallEvent E k x) -
        k * (∑ x, E false x * binaryCallEvent E k x) =
      ∑ x, (((1 - k) * E true x - k * E false x) *
        binaryCallEvent E k x) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = ∑ x, max ((1 - k) * E true x - k * E false x) 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : 0 <= (1 - k) * E true x - k * E false x
      · simp [binaryCallEvent, h]
      · have hn : (1 - k) * E true x - k * E false x <= 0 :=
          le_of_not_ge h
        simp [binaryCallEvent, h, max_eq_right hn]

/-- Interchange finite expectation with a decoder pullback. -/
theorem sum_mul_decoderPullback
    (p : X -> Real) (G : X -> Y -> Real) (u : Y -> Real) :
    (∑ x, p x * (∑ y, G x y * u y)) =
      ∑ y, (∑ x, p x * G x y) * u y := by
  calc
    (∑ x, p x * (∑ y, G x y * u y)) =
        ∑ x, ∑ y, p x * (G x y * u y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = ∑ y, ∑ x, p x * (G x y * u y) := Finset.sum_comm
    _ = ∑ y, (∑ x, p x * G x y) * u y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- A fixed decoder loses at least the target-minus-source call advantage.
The sharper displayed bound retains the two decoder row errors with their
binary-prior weights. -/
theorem binaryCall_sub_le_weighted_decodeErr
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y)
    (k : Real) (hk0 : 0 <= k) (hk1 : k <= 1) :
    binaryCall F k - binaryCall E k <=
      (1 - k) * decodeErr E F G true +
        k * decodeErr E F G false := by
  let u : Y -> Real := binaryCallEvent F k
  let v : X -> Real := fun x => ∑ y, G x y * u y
  have hu0 : forall y, 0 <= u y := by
    intro y
    exact binaryCallEvent_nonneg F k y
  have hu1 : forall y, u y <= 1 := by
    intro y
    exact binaryCallEvent_le_one F k y
  have hv0 : forall x, 0 <= v x := by
    intro x
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg ((hG x (Set.mem_univ x)).1 y) (hu0 y)
  have hv1 : forall x, v x <= 1 := by
    intro x
    calc
      v x = ∑ y, G x y * u y := rfl
      _ <= ∑ y, G x y * 1 := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hu1 y)
          ((hG x (Set.mem_univ x)).1 y)
      _ = 1 := by
        simpa using (hG x (Set.mem_univ x)).2
  have hFcall :
      (1 - k) * (∑ y, F true y * u y) -
          k * (∑ y, F false y * u y) =
        binaryCall F k := by
    exact binaryCallEvent_score F k
  have hEevent :
      (1 - k) * (∑ x, E true x * v x) -
          k * (∑ x, E false x * v x) <=
        binaryCall E k :=
    binaryEventScore_le_call E k v hv0 hv1
  have hrow : forall b : Bool,
      (∑ x, E b x * v x) =
        ∑ y, finiteDecisionLaw E G b y * u y := by
    intro b
    simpa [v, finiteDecisionLaw] using
      (sum_mul_decoderPullback (E b) G u)
  have hP : IsFiniteExperiment (finiteDecisionLaw E G) :=
    finiteDecisionLaw_valid E hE G hG
  have htrue :
      (∑ y, F true y * u y) -
          ∑ y, finiteDecisionLaw E G true y * u y <=
        decodeErr E F G true := by
    have htv := expectation_sub_le_finiteTV
      (F true) (finiteDecisionLaw E G true) u
      (by rw [(hF true).2, (hP true).2]) hu0 hu1
    calc
      (∑ y, F true y * u y) -
          ∑ y, finiteDecisionLaw E G true y * u y <=
        finiteTV (F true) (finiteDecisionLaw E G true) := htv
      _ = decodeErr E F G true := by
        rw [finiteTV_symm]
        rfl
  have hfalse :
      (∑ y, finiteDecisionLaw E G false y * u y) -
          ∑ y, F false y * u y <=
        decodeErr E F G false := by
    have htv := expectation_sub_le_finiteTV
      (finiteDecisionLaw E G false) (F false) u
      (by rw [(hP false).2, (hF false).2]) hu0 hu1
    exact htv
  calc
    binaryCall F k - binaryCall E k =
        ((1 - k) * (∑ y, F true y * u y) -
          k * (∑ y, F false y * u y)) -
            binaryCall E k := by rw [hFcall]
    _ <= ((1 - k) * (∑ y, F true y * u y) -
          k * (∑ y, F false y * u y)) -
        ((1 - k) * (∑ x, E true x * v x) -
          k * (∑ x, E false x * v x)) :=
      sub_le_sub_left hEevent _
    _ = (1 - k) *
          ((∑ y, F true y * u y) -
            ∑ y, finiteDecisionLaw E G true y * u y) +
        k * ((∑ y, finiteDecisionLaw E G false y * u y) -
          ∑ y, F false y * u y) := by
      rw [hrow true, hrow false]
      ring
    _ <= (1 - k) * decodeErr E F G true +
        k * decodeErr E F G false := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left htrue (sub_nonneg.mpr hk1))
        (mul_le_mul_of_nonneg_left hfalse hk0)

/-- Every candidate uniform decoder bound dominates every call-function gap. -/
theorem binaryCall_sub_le_of_decodeErr_le
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y)
    (k c : Real) (hk0 : 0 <= k) (hk1 : k <= 1)
    (herr : forall b, decodeErr E F G b <= c) :
    binaryCall F k - binaryCall E k <= c := by
  calc
    binaryCall F k - binaryCall E k <=
        (1 - k) * decodeErr E F G true +
          k * decodeErr E F G false :=
      binaryCall_sub_le_weighted_decodeErr E F hE hF G hG k hk0 hk1
    _ <= (1 - k) * c + k * c := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (herr true) (sub_nonneg.mpr hk1))
        (mul_le_mul_of_nonneg_left (herr false) hk0)
    _ = c := by ring

/-- Pointwise call-gap lower bound on directed deficiency. This is the
support-function direction of the paper's binary deficiency identity. -/
theorem binaryCall_sub_le_finiteDeficiency
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (k : Real) (hk0 : 0 <= k) (hk1 : k <= 1) :
    binaryCall F k - binaryCall E k <= finiteDeficiency E F := by
  let _ : Nonempty Y := nonempty_of_isFiniteExperiment F hF
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid E F hE hF)
  rintro c ⟨G, hG, herr⟩
  exact binaryCall_sub_le_of_decodeErr_le
    E F hE hF G hG k c hk0 hk1 herr

theorem binaryCall_zero
    (E : FiniteExperiment Bool X) (hE : IsFiniteExperiment E) :
    binaryCall E 0 = 1 := by
  unfold binaryCall
  have hpoint : forall x,
      max ((1 - (0 : Real)) * E true x - 0 * E false x) 0 =
        E true x := by
    intro x
    simp [(hE true).1 x]
  simp_rw [hpoint]
  exact (hE true).2

theorem binaryCall_one
    (E : FiniteExperiment Bool X) (hE : IsFiniteExperiment E) :
    binaryCall E 1 = 0 := by
  unfold binaryCall
  have hpoint : forall x,
      max ((1 - (1 : Real)) * E true x - 1 * E false x) 0 = 0 := by
    intro x
    have hn : -E false x <= 0 :=
      neg_nonpos.mpr ((hE false).1 x)
    simp [hn]
  simp_rw [hpoint]
  simp

/-- Values attained by the call gap on the binary-prior interval. -/
def binaryCallGapValues
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y) : Set Real :=
  {d | exists k : Real, k ∈ Set.Icc 0 1 /\
    d = binaryCall F k - binaryCall E k}

theorem binaryCallGapValues_nonempty
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    (binaryCallGapValues E F).Nonempty := by
  refine ⟨0, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  rw [binaryCall_zero F hF, binaryCall_zero E hE, sub_self]

theorem binaryCallGapValues_bddAbove
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    BddAbove (binaryCallGapValues E F) := by
  refine ⟨finiteDeficiency E F, ?_⟩
  rintro d ⟨k, ⟨hk0, hk1⟩, rfl⟩
  exact binaryCall_sub_le_finiteDeficiency E F hE hF k hk0 hk1

/-- The optimized call gap, written as a supremum so no separate compactness
argument is needed. -/
noncomputable def binaryCallGap
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y) : Real :=
  sSup (binaryCallGapValues E F)

/-- The optimized binary call gap is nonnegative for valid experiments. -/
theorem binaryCallGap_nonneg
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    0 <= binaryCallGap E F := by
  unfold binaryCallGap
  apply le_csSup (binaryCallGapValues_bddAbove E F hE hF)
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
    rw [binaryCall_zero F hF, binaryCall_zero E hE, sub_self]⟩

/-- Supremum form of the two-world support-function lower bound. -/
theorem binaryCallGap_le_finiteDeficiency
    (E : FiniteExperiment Bool X) (F : FiniteExperiment Bool Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    binaryCallGap E F <= finiteDeficiency E F := by
  unfold binaryCallGap
  apply csSup_le (binaryCallGapValues_nonempty E F hE hF)
  rintro d ⟨k, ⟨hk0, hk1⟩, rfl⟩
  exact binaryCall_sub_le_finiteDeficiency E F hE hF k hk0 hk1

end IdExp
