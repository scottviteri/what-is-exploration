import Formal.WaitingQueryGeometric
import Formal.PulseBehavior

/-!
# Complete full-label Brier prediction on the countable pulse class

Reports are probability vectors on every world in `Option Nat`, and the score
is the ordinary unweighted quadratic score `2 p θ - ∑' η, p η ^ 2`.
The record is the literal controlled-behavior record. At each horizon the value
optimizes over every report rule; the complete objective is its supremum over
finite prefixes. WAIT attains the universal upper bound although QUERY strictly
finitarily dominates it. The proof uses the genuine full-support geometric prior.

The actual-posterior identification is checked in `PulseBrierPosterior`; the
finite telescope and convergent squared-movement series are checked separately
in `PulseBrierMovement`.
-/

namespace IdExp

open MeasureTheory Finset Set Filter Topology
noncomputable section

/-- A report on every label, with summability and probability normalization. -/
structure FullLabelBrierReport (Θ : Type*) where
  probability : Θ → ℝ
  nonneg : ∀ θ, 0 ≤ probability θ
  summable : Summable probability
  sum_one : ∑' θ, probability θ = 1

instance {Θ : Type*} : CoeFun (FullLabelBrierReport Θ) (fun _ => Θ → ℝ) :=
  ⟨FullLabelBrierReport.probability⟩

namespace FullLabelBrierReport

variable {Θ : Type*}

theorem le_one (p : FullLabelBrierReport Θ) (θ : Θ) : p θ ≤ 1 := by
  have h := p.summable.le_tsum θ (fun η _ => p.nonneg η)
  rwa [p.sum_one] at h

theorem summable_square (p : FullLabelBrierReport Θ) : Summable (fun θ => p θ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun θ => sq_nonneg (p θ)) _ p.summable
  intro θ
  have hn := p.nonneg θ
  have hu := p.le_one θ
  nlinarith

def potential (p : FullLabelBrierReport Θ) : ℝ := ∑' θ, p θ ^ 2

theorem potential_bounds (p : FullLabelBrierReport Θ) :
    0 ≤ p.potential ∧ p.potential ≤ 1 := by
  refine ⟨tsum_nonneg (fun θ => sq_nonneg _), ?_⟩
  have h := p.summable_square.tsum_le_tsum (fun θ => ?_) p.summable
  · simpa [potential, p.sum_one] using h
  · have hn := p.nonneg θ
    have hu := p.le_one θ
    nlinarith

/-- The usual full-label Brier reward, up to a policy-independent constant. -/
def score (p : FullLabelBrierReport Θ) (θ : Θ) : ℝ := 2 * p θ - p.potential

theorem score_bounds (p : FullLabelBrierReport Θ) (θ : Θ) :
    -1 ≤ p.score θ ∧ p.score θ ≤ 1 := by
  have hn := p.nonneg θ
  have hu := p.potential_bounds.2
  have hsq : p θ ^ 2 ≤ p.potential :=
    p.summable_square.le_tsum θ (fun η _ => sq_nonneg _)
  constructor <;> unfold score <;> nlinarith [sq_nonneg (p θ - 1)]

/-- A point prediction remains an allowed full-label probability report. -/
def point (θ : Θ) : FullLabelBrierReport Θ := by
  classical
  exact ⟨fun η => if η = θ then 1 else 0,
    by intro η; split_ifs <;> norm_num,
    (hasSum_ite_eq θ (1 : ℝ)).summable, (hasSum_ite_eq θ (1 : ℝ)).tsum_eq⟩

theorem point_score [DecidableEq Θ] (θ η : Θ) : (point θ).score η = if η = θ then 1 else -1 := by
  classical
  have hp : (point θ).potential = 1 := by
    simp [potential, point]
  rw [score, hp]
  by_cases h : η = θ <;> norm_num [point, h]

/-- The all-label quadratic score is proper, with its exact squared-error gap.
No geometric feature weights or finite selected label family occur. -/
theorem proper_identity (p q : FullLabelBrierReport Θ) :
    (∑' θ, p θ * q.score θ) = p.potential - ∑' θ, (p θ - q θ) ^ 2 := by
  have hpq : Summable (fun θ => p θ * q θ) := by
    apply Summable.of_nonneg_of_le (fun θ => mul_nonneg (p.nonneg θ) (q.nonneg θ))
      (fun θ => mul_le_of_le_one_right (p.nonneg θ) (q.le_one θ)) p.summable
  have hs : Summable (fun θ => p θ ^ 2 - 2 * (p θ * q θ) + q θ ^ 2) :=
    (p.summable_square.sub (hpq.mul_left 2)).add q.summable_square
  have hsq : (∑' θ, (p θ - q θ) ^ 2) =
      p.potential - 2 * (∑' θ, p θ * q θ) + q.potential := by
    calc
      _ = ∑' θ, (p θ ^ 2 - 2 * (p θ * q θ) + q θ ^ 2) := by
        apply tsum_congr; intro θ; ring
      _ = _ := by
        rw [(p.summable_square.sub (hpq.mul_left 2)).tsum_add q.summable_square,
          p.summable_square.tsum_sub (hpq.mul_left 2), tsum_mul_left]
        rfl
  have hexp : (∑' θ, p θ * q.score θ) = 2 * (∑' θ, p θ * q θ) - q.potential := by
    calc
      _ = ∑' θ, (2 * (p θ * q θ) - p θ * q.potential) := by
        apply tsum_congr; intro θ; simp only [score]; ring
      _ = _ := by
        rw [(hpq.mul_left 2).tsum_sub (p.summable.mul_right q.potential),
          tsum_mul_left, tsum_mul_right, p.sum_one, one_mul]
  rw [hsq, hexp]
  ring

end FullLabelBrierReport

namespace PulseBrierScore

abbrev World := WaitingQueryWorld
abbrev Report := FullLabelBrierReport World
abbrev prior := waitingQueryGeometricPrior

/-- Finite-record expected full-label quadratic score of an arbitrary reporting rule. -/
def rulePayoff {S : Type*} [Fintype S] (E : FiniteExperiment World S)
    (r : S → Report) (θ : World) : ℝ := ∑ s, E θ s * (r s).score θ

def ruleValue {S : Type*} [Fintype S] (E : FiniteExperiment World S)
    (r : S → Report) : ℝ := ∫ θ, rulePayoff E r θ ∂prior

theorem rulePayoff_bounds {S : Type*} [Fintype S] (E : FiniteExperiment World S)
    (hE : IsFiniteExperiment E) (r : S → Report) (θ : World) :
    -1 ≤ rulePayoff E r θ ∧ rulePayoff E r θ ≤ 1 := by
  constructor
  · calc
      -1 = ∑ s, E θ s * (-1) := by rw [← sum_mul, (hE θ).2]; ring
      _ ≤ rulePayoff E r θ := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left ((r s).score_bounds θ).1 ((hE θ).1 s)
  · calc
      rulePayoff E r θ ≤ ∑ s, E θ s * 1 := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left ((r s).score_bounds θ).2 ((hE θ).1 s)
      _ = 1 := by simpa using (hE θ).2

theorem rulePayoff_integrable {S : Type*} [Fintype S] (E : FiniteExperiment World S)
    (hE : IsFiniteExperiment E) (r : S → Report) : Integrable (rulePayoff E r) prior := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_le]
    exact rulePayoff_bounds E hE r θ

theorem ruleValue_le_one {S : Type*} [Fintype S] (E : FiniteExperiment World S)
    (hE : IsFiniteExperiment E) (r : S → Report) : ruleValue E r ≤ 1 := by
  calc
    _ ≤ ∫ _ : World, (1 : ℝ) ∂prior := integral_mono
      (rulePayoff_integrable E hE r) (integrable_const _) (fun θ => (rulePayoff_bounds E hE r θ).2)
    _ = 1 := by simp

def experimentScore {S : Type*} [Fintype S] (E : FiniteExperiment World S) : ℝ :=
  sSup (Set.range (ruleValue E))

theorem experimentScore_le_one {S : Type*} [Fintype S] (E : FiniteExperiment World S)
    (hE : IsFiniteExperiment E) : experimentScore E ≤ 1 := by
  have : Nonempty (S → Report) := ⟨fun _ => FullLabelBrierReport.point none⟩
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨r, rfl⟩; exact ruleValue_le_one E hE r)

theorem ruleValue_le_experimentScore {S : Type*} [Fintype S]
    (E : FiniteExperiment World S) (hE : IsFiniteExperiment E) (r : S → Report) :
    ruleValue E r ≤ experimentScore E :=
  le_csSup ⟨1, by rintro _ ⟨r, rfl⟩; exact ruleValue_le_one E hE r⟩ (Set.mem_range_self r)

/-- The expected full-label score optimized from each actual retained prefix. -/
def prefixScore (π : ValidCausalPolicy Bool Bool) (t : ℕ) : ℝ :=
  experimentScore (causalBehaviorFiniteExperiment π.1 pulseBehavior t)

def completeScore (π : ValidCausalPolicy Bool Bool) : ℝ := sSup (Set.range (prefixScore π))

theorem prefixScore_le_one (π : ValidCausalPolicy Bool Bool) (t : ℕ) : prefixScore π t ≤ 1 :=
  experimentScore_le_one _ (causalBehaviorFiniteExperiment_valid π.1 π.2 pulseBehavior t)

theorem completeScore_le_one (π : ValidCausalPolicy Bool Bool) : completeScore π ≤ 1 :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact prefixScore_le_one π t)

def waitReport (t : ℕ) (x : CausalFiniteTrace Bool Bool t) : Report :=
  FullLabelBrierReport.point (waitingQueryGuess t x)

theorem wait_point_payoff (t : ℕ) (θ : World) :
    rulePayoff (pulseExperiment false t) (waitReport t) θ =
      1 - 2 * (waitingQueryTailSet t).indicator (fun _ => (1 : ℝ)) θ := by
  classical
  rw [pulseExperiment_wait, waitingQueryExperiment_eq_dirac]
  simp only [rulePayoff, diracExp, waitReport, FullLabelBrierReport.point_score]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']
  by_cases ht : θ ∈ waitingQueryTailSet t
  · obtain ⟨k, rfl, hk⟩ := ht
    rw [waitingQueryTrace_undetected t k hk,
      waitingQueryGuess_exact t none (Or.inl rfl),
      Set.indicator_of_mem (show some k ∈ waitingQueryTailSet t from ⟨k, rfl, hk⟩)]
    norm_num
    simp
  · rw [waitingQueryGuess_exact_off_tail t θ ht, if_pos rfl, Set.indicator_of_notMem ht]
    norm_num

theorem wait_point_value (t : ℕ) :
    ruleValue (pulseExperiment false t) (waitReport t) = 1 - 2 * waitingQueryTail prior t := by
  unfold ruleValue
  simp_rw [wait_point_payoff]
  rw [integral_sub (integrable_const _)
    (((integrable_const (1 : ℝ)).indicator (show MeasurableSet (waitingQueryTailSet t) from trivial)).const_mul 2),
    integral_const_mul, integral_indicator_const _ (show MeasurableSet (waitingQueryTailSet t) from trivial)]
  simp [waitingQueryTail, smul_eq_mul]

theorem wait_completeScore : completeScore (pulsePolicy false) = 1 := by
  apply le_antisymm (completeScore_le_one _)
  have hlimit : Tendsto (fun t => 1 - 2 * waitingQueryTail prior t) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub ((waitingQueryTail_tendsto_zero prior).const_mul 2)
  apply le_of_tendsto hlimit
  apply Eventually.of_forall
  intro t
  rw [← wait_point_value]
  apply (ruleValue_le_experimentScore _ (pulseExperiment_valid false t) (waitReport t)).trans
  exact le_csSup ⟨1, by rintro _ ⟨n, rfl⟩; exact prefixScore_le_one _ n⟩
    (Set.mem_range_self t)

/-- WAIT maximizes a complete full-label Brier prediction objective over all
randomized history policies, despite a feasible strict finitary improvement. -/
theorem dominated_maximizer :
    (∀ π : ValidCausalPolicy Bool Bool, completeScore π ≤ completeScore (pulsePolicy false)) ∧
    CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy true) (pulsePolicy false) ∧
      ¬ CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy false) (pulsePolicy true) := by
  refine ⟨?_, pulse_query_strictly_dominates_wait⟩
  intro π
  rw [wait_completeScore]
  exact completeScore_le_one π

end PulseBrierScore
end
end IdExp
