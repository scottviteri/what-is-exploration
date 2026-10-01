import Formal.AlarmPanelVariance
import Formal.CountableBrierScore

/-! Published expected Hellinger and Absolute knowledge-seeking rewards.
The local reward is the posterior mean of the divergence between a world's
next-observation distribution and the Bayesian predictive distribution (Orseau,
Lattimore and Hutter, 2013, equations 4--5). No state/observation substitution is
made. The paper also gives the equivalent posterior-movement expression. -/
noncomputable section
namespace IdExp.PosteriorMovement
open MeasureTheory Finset Set

inductive Kind | hellinger | absolute deriving DecidableEq

def loss : Kind → ℝ → ℝ → ℝ
  | .hellinger, x, y => (Real.sqrt x - Real.sqrt y)^2
  | .absolute, x, y => |x-y|

def coordinate {Θ : Type*} [MeasurableSpace Θ] (kind : Kind)
    (μ : Measure Θ) (q : Θ → ℝ) : ℝ :=
  ∫ θ, loss kind (q θ) (∫ η, q η ∂μ) ∂μ

def reward {Θ O : Type*} [MeasurableSpace Θ] [Fintype O]
    (kind : Kind) (μ : Measure Θ) (q : Θ → O → ℝ) : ℝ :=
  ∑ o, coordinate kind μ (fun θ => q θ o)

def binaryReward : Kind → ℝ → ℝ
  | .hellinger, p => 2 * (1 - p * Real.sqrt p - (1-p) * Real.sqrt (1-p))
  | .absolute, p => 4*p*(1-p)

def fairReward : Kind → ℝ
  | .hellinger => 2-Real.sqrt 2
  | .absolute => 1

@[simp] theorem loss_self (kind : Kind) (x : ℝ) : loss kind x x = 0 := by
  cases kind <;> simp [loss]

theorem reward_constant {Θ O : Type*} [MeasurableSpace Θ] [Fintype O]
    (kind : Kind) (μ : Measure Θ) [IsProbabilityMeasure μ] (q : O → ℝ) :
    reward kind μ (fun _ => q) = 0 := by simp [reward, coordinate]

@[simp] theorem binaryReward_zero (kind : Kind) : binaryReward kind 0 = 0 := by
  cases kind <;> norm_num [binaryReward]

@[simp] theorem binaryReward_one (kind : Kind) : binaryReward kind 1 = 0 := by
  cases kind <;> norm_num [binaryReward]

theorem sqrt_half : Real.sqrt (1/2 : ℝ) = Real.sqrt 2 / 2 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h' := Real.sq_sqrt (show (0:ℝ) ≤ 1/2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hn' := Real.sqrt_nonneg (1/2:ℝ)
  nlinarith

@[simp] theorem binaryReward_half (kind : Kind) :
    binaryReward kind (1/2) = fairReward kind := by
  cases kind
  · change 2 * (1 - (1/2:ℝ) * Real.sqrt (1/2) - (1-1/2) * Real.sqrt (1-1/2)) = _
    rw [show (1-(1/2:ℝ)) = 1/2 by norm_num, sqrt_half]
    simp only [fairReward]; ring
  · norm_num [binaryReward, fairReward]

theorem binaryReward_symm (kind : Kind) (p : ℝ) :
    binaryReward kind (1-p) = binaryReward kind p := by
  cases kind <;> simp [binaryReward] <;> ring

/-- One coordinate of a deterministic observation, including probability-zero
and probability-one events. -/
theorem coordinate_indicator {Θ : Type*} [MeasurableSpace Θ]
    (kind : Kind) (μ : Measure Θ) [IsProbabilityMeasure μ]
    (s : Set Θ) (hs : MeasurableSet s) :
    coordinate kind μ (s.indicator (fun _ => (1:ℝ))) =
      match kind with
      | .hellinger => 2 * μ.real s * (1-Real.sqrt (μ.real s))
      | .absolute => 2 * μ.real s * (1-μ.real s) := by
  have hp : 0 ≤ μ.real s := measureReal_nonneg
  have hp1 : μ.real s ≤ 1 := by
    simpa using measureReal_mono (show s ⊆ Set.univ from subset_univ s)
  have hi : (∫ θ, s.indicator (fun _ => (1:ℝ)) θ ∂μ) = μ.real s := by
    rw [integral_indicator_const _ hs]; simp
  have he (f : ℝ → ℝ) :
      (fun θ => f (s.indicator (fun _ => (1:ℝ)) θ)) =
      fun θ => s.indicator (fun _ => f 1) θ + sᶜ.indicator (fun _ => f 0) θ := by
    funext θ; by_cases h : θ ∈ s <;> simp [Set.indicator_apply, h]
  unfold coordinate
  rw [hi, he (fun x => loss kind x (μ.real s)), integral_add ((integrable_const _).indicator hs)
    ((integrable_const _).indicator hs.compl), integral_indicator_const _ hs,
    integral_indicator_const _ hs.compl]
  simp only [smul_eq_mul, measureReal_compl hs]
  simp only [probReal_univ]
  cases kind
  · simp only [loss, Real.sqrt_one, Real.sqrt_zero, zero_sub, neg_sq]
    have hsq := Real.sq_sqrt hp
    nlinarith
  · simp only [loss, abs_of_nonneg (sub_nonneg.mpr hp1), zero_sub,
      abs_neg, abs_of_nonneg hp]
    ring

/-- A deterministic yes/no query pays a function only of its posterior answer
probability, irrespective of the cardinalities of the two world sets. -/
theorem reward_binary {Θ : Type*} [MeasurableSpace Θ]
    (kind : Kind) (μ : Measure Θ) [IsProbabilityMeasure μ]
    (s : Set Θ) (hs : MeasurableSet s) :
    reward kind μ (fun θ (b : Bool) => if b then
      s.indicator (fun _ => (1:ℝ)) θ else sᶜ.indicator (fun _ => (1:ℝ)) θ) =
      binaryReward kind (μ.real s) := by
  simp only [reward, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  rw [coordinate_indicator kind μ s hs, coordinate_indicator kind μ sᶜ hs.compl,
    measureReal_compl hs]
  cases kind <;> simp [binaryReward] <;> ring

/-- Positive homogeneity is what preserves the literal posterior reward under
Bayes' change of measure; it fails for ordinary squared movement. -/
theorem loss_scale (kind : Kind) (c x y : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    loss kind (c*x) (c*y) = c*loss kind x y := by
  cases kind
  · simp only [loss, Real.sqrt_mul hc]
    rw [← mul_sub, mul_pow, Real.sq_sqrt hc]
  · simp only [loss, ← mul_sub, abs_mul, abs_of_nonneg hc]

/-- Coordinatewise Bayes identity, on every nonnull observation. Summing over
worlds and observations gives the source's equations (4)--(5). -/
theorem bayes_coordinate_identity (kind : Kind) (b q m : ℝ)
    (hb : 0 ≤ b) (hq : 0 ≤ q) (hm : 0 < m) :
    m*loss kind (b*q/m) b = b*loss kind q m := by
  have he : b=(b/m)*m := (div_mul_cancel₀ b hm.ne').symm
  calc
    m*loss kind (b*q/m) b = m*loss kind ((b/m)*q) ((b/m)*m) := by
      congr 1
      · congr 1 <;> field_simp
    _ = m*((b/m)*loss kind q m) := by
      rw [loss_scale kind (b/m) q m (div_nonneg hb hm.le) hq hm.le]
    _ = _ := by field_simp

end IdExp.PosteriorMovement
