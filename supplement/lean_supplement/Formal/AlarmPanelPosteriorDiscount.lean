import Formal.AlarmPanelNativePosteriorControls
import Formal.AlarmPanelBayesEntropy
import Formal.WorstPriorInformation

/-! Proper-discount information and ordinary Brier movement strictly favor
inspection on the alarm. The undiscounted complete-return tie is unchanged. -/
noncomputable section
namespace IdExp.PrefixDiscount
open Finset

def value (γ : ℝ) (v : ℕ → ℝ) : ℝ := ∑' n, γ^n*(v (n+1)-v n)

theorem weighted_summable (γ C : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ<1)
    (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n ∧ v n ≤ C) : Summable (fun n => γ^n*v n) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hγ _) (hv n).1) _
    ((summable_geometric_of_lt_one hγ hγ1).mul_right C)
  intro n; exact mul_le_mul_of_nonneg_left (hv n).2 (pow_nonneg hγ _)

/-- Abel summation for bounded nonnegative prefix values. -/
theorem value_eq (γ C : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ<1)
    (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n ∧ v n ≤ C) :
    value γ v = (1-γ)*(∑' n, γ^n*v (n+1))-v 0 := by
  have hs := weighted_summable γ C hγ hγ1 v hv
  have ht := weighted_summable γ C hγ hγ1 (fun n => v (n+1)) (fun n => hv (n+1))
  have he := hs.sum_add_tsum_nat_add 1
  simp only [sum_range_one, pow_zero, one_mul, pow_succ] at he
  have hh : (∑' n, γ^n*γ*v (n+1)) = γ*(∑' n, γ^n*v (n+1)) := by
    rw [← tsum_mul_left]; apply tsum_congr; intro n; ring
  rw [hh] at he
  unfold value
  simp only [mul_sub]
  rw [ht.tsum_sub hs]
  linarith

theorem value_strict (γ C : ℝ) (hγ : 0<γ) (hγ1 : γ<1)
    (v w : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n ∧ v n ≤ C)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ C)
    (h0 : v 0=w 0) (hle : ∀ n, v (n+1) ≤ w (n+1)) (hlt : v 1<w 1) :
    value γ v < value γ w := by
  rw [value_eq γ C hγ.le hγ1 v hv, value_eq γ C hγ.le hγ1 w hw, h0]
  apply sub_lt_sub_right
  apply mul_lt_mul_of_pos_left _ (by linarith)
  apply Summable.tsum_lt_tsum (fun n => mul_le_mul_of_nonneg_left (hle n) (pow_nonneg hγ.le _))
    (i := 0)
  · simpa using hlt
  · exact weighted_summable γ C hγ.le hγ1 _ (fun n => hv (n+1))
  · exact weighted_summable γ C hγ.le hγ1 _ (fun n => hw (n+1))

end IdExp.PrefixDiscount

namespace IdExp.AlarmPanelPosterior
open AlarmPanel MeasureTheory
local instance : TopologicalSpace World := ⊥
local instance : DiscreteTopology World := ⟨rfl⟩
local instance : OpensMeasurableSpace World := ⟨fun s _ => Set.Countable.measurableSet (Set.to_countable s)⟩

def discountedInformation (γ : ℝ) (π : ValidCausalPolicy Action Observation) :=
  PrefixDiscount.value γ (prefixInformation π)
def discountedBrier (γ : ℝ) (π : ValidCausalPolicy Action Observation) :=
  ∑' n, γ^n*expectedMovement π n

theorem discountedBrier_eq (γ : ℝ) (π : ValidCausalPolicy Action Observation) :
    discountedBrier γ π = PrefixDiscount.value γ (prefixPotential π) := by
  simp only [discountedBrier, PrefixDiscount.value, expectedMovement_eq]

theorem information_bounds (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ prefixInformation π n ∧ prefixInformation π n ≤ 2*Real.log 2 := by
  refine ⟨?_,prefixInformation_le π n⟩
  exact infinitePriorInformation_nonneg PulseBrierScore.prior _ (record_valid π n)
    (fun _ => continuous_of_discreteTopology)

theorem potential_bounds (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ prefixPotential π n ∧ prefixPotential π n ≤ 1 := by
  refine ⟨?_,prefixPotential_le_one π n⟩
  have h := prefixPotential_monotone π (Nat.zero_le n)
  rw [prefixPotential_zero, PulseBrierScore.priorPotential_eq_third] at h
  linarith

theorem discountedInformation_strict (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) (hs : inspectionProbability π.1<1) :
    discountedInformation γ π < discountedInformation γ ⟨inspectPolicy,inspectPolicy_valid⟩ := by
  apply PrefixDiscount.value_strict γ (2*Real.log 2) hγ hγ1 _ _ (information_bounds π)
    (information_bounds ⟨inspectPolicy,inspectPolicy_valid⟩)
  · simp [AlarmPanelBayes.information_zero]
  · exact finiteInformation_le π.1 π.2
  · exact finiteInformation_strict π.1 π.2 0 hs

theorem discountedBrier_strict (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) (hs : inspectionProbability π.1<1) :
    discountedBrier γ π < discountedBrier γ ⟨inspectPolicy,inspectPolicy_valid⟩ := by
  rw [discountedBrier_eq, discountedBrier_eq]
  apply PrefixDiscount.value_strict γ 1 hγ hγ1 _ _ (potential_bounds π)
    (potential_bounds ⟨inspectPolicy,inspectPolicy_valid⟩)
  · simp [prefixPotential_zero]
  · exact finiteBrier_le π.1 π.2
  · exact finiteBrier_strict π.1 π.2 0 hs

theorem discountedInformation_eq_iff (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) :
    discountedInformation γ π = discountedInformation γ ⟨inspectPolicy,inspectPolicy_valid⟩ ↔
      inspectionProbability π.1=1 := by
  constructor
  · intro he; by_contra hs
    exact (ne_of_lt (discountedInformation_strict γ hγ hγ1 π
      (lt_of_le_of_ne (inspectionProbability_le_one π.1 π.2) hs))) he
  · intro hs
    have he : prefixInformation π = prefixInformation ⟨inspectPolicy,inspectPolicy_valid⟩ := by
      funext n; cases n with
      | zero => simp [AlarmPanelBayes.information_zero]
      | succ n => exact (finiteInformation_eq_iff π.1 π.2 n).mpr hs
    simp only [discountedInformation, he]

theorem discountedBrier_eq_iff (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) :
    discountedBrier γ π = discountedBrier γ ⟨inspectPolicy,inspectPolicy_valid⟩ ↔
      inspectionProbability π.1=1 := by
  constructor
  · intro he; by_contra hs
    exact (ne_of_lt (discountedBrier_strict γ hγ hγ1 π
      (lt_of_le_of_ne (inspectionProbability_le_one π.1 π.2) hs))) he
  · intro hs
    have he : prefixPotential π = prefixPotential ⟨inspectPolicy,inspectPolicy_valid⟩ := by
      funext n; cases n with
      | zero => simp [prefixPotential_zero]
      | succ n => exact (finiteBrier_eq_iff π.1 π.2 n).mpr hs
    simp only [discountedBrier_eq, he]

end IdExp.AlarmPanelPosterior
