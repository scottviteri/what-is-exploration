import Formal.AlarmPanelMultiStepEmpowerment

/-! Discounted terminal-sensor empowerment on the unchanged alarm/panel.
The return pairs consecutive visited times with their original discount weights.
The capacity and causal experiment definitions are the existing literal ones. -/
namespace IdExp.AlarmPanel.Control
open Finset Filter Topology
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Complete discounted visited-capacity return, preserving the time weights. -/
def multiStepDiscounted (n : ℕ) (γ : ℝ)
    (π : ValidCausalPolicy Action Observation) (θ : World) : ℝ :=
  multiStepStage n π θ 0 + ∑' k : ℕ,
    (γ^(2*k+1) * multiStepStage n π θ (2*k+1) +
     γ^(2*k+2) * multiStepStage n π θ (2*k+2))

/-- Discounted frequency of the panel endpoints, with extra = probe length - 1. -/
def panelDiscountFactor (extra : ℕ) (γ : ℝ) : ℝ :=
  (if extra % 2 = 0 then γ else γ^2) / (1 - γ^2)

theorem panelDiscountFactor_pos (extra : ℕ) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : 0 < panelDiscountFactor extra γ := by
  have hγ2 : γ^2 < 1 := by nlinarith
  unfold panelDiscountFactor
  split_ifs <;> exact div_pos (by positivity) (by linarith)

theorem multiStepDiscounted_pair (n k : ℕ) (γ : ℝ)
    (π : ValidCausalPolicy Action Observation) (θ : World) :
    γ^(2*k+1) * multiStepStage (n+1) π θ (2*k+1) +
      γ^(2*k+2) * multiStepStage (n+1) π θ (2*k+2) =
      (γ^2)^k * ((if n % 2 = 0 then γ else γ^2) *
        (1 - inspectionProbability π.1) * Real.log 2) := by
  rw [multiStepStage_succ n π θ (2*k),
    show 2*k+2 = (2*k+1)+1 by omega, multiStepStage_succ n π θ (2*k+1)]
  by_cases hn : n % 2 = 0
  · have ho : (2*k+1+n)%2 = 1 := by omega
    have hz : (2*k+1+1+n)%2 ≠ 1 := by omega
    simp only [hn, ho, hz, if_true, if_false, mul_zero, add_zero, pow_succ, pow_mul]
    ring
  · have hz : (2*k+1+n)%2 ≠ 1 := by omega
    have ho : (2*k+1+1+n)%2 = 1 := by omega
    simp only [hn, ho, hz, if_true, if_false, mul_zero, zero_add, pow_succ, pow_mul]
    ring

theorem multiStepDiscounted_pair_summable (n : ℕ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) (θ : World) :
    Summable (fun k : ℕ =>
      γ^(2*k+1) * multiStepStage (n+1) π θ (2*k+1) +
      γ^(2*k+2) * multiStepStage (n+1) π θ (2*k+2)) := by
  simp_rw [multiStepDiscounted_pair]
  apply Summable.mul_right
  apply summable_geometric_of_lt_one (sq_nonneg γ)
  nlinarith

/-- The grouped definition equals the ordinary chronological infinite sum. -/
theorem multiStepDiscounted_eq_tsum (n : ℕ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) (θ : World) :
    multiStepDiscounted (n+1) γ π θ =
      ∑' t : ℕ, γ^t * multiStepStage (n+1) π θ t := by
  let f : ℕ → ℝ := fun t => γ^t * multiStepStage (n+1) π θ t
  have hn (t : ℕ) : 0 ≤ f (t+1) := by
    dsimp [f]
    rw [multiStepStage_succ]
    have hs : 0 ≤ 1 - inspectionProbability π.1 :=
      sub_nonneg.mpr (inspectionProbability_le_one π.1 π.2)
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    split_ifs <;> positivity
  have hp : Summable (fun k => f (2*k+1) + f (2*k+2)) :=
    multiStepDiscounted_pair_summable n γ hγ0 hγ1 π θ
  have he : Summable (fun k => f (2*k+1)) :=
    Summable.of_nonneg_of_le (fun k => hn (2*k))
      (fun k => le_add_of_nonneg_right (hn (2*k+1))) hp
  have ho : Summable (fun k => f (2*k+2)) :=
    Summable.of_nonneg_of_le (fun k => hn (2*k+1))
      (fun k => le_add_of_nonneg_left (hn (2*k))) hp
  have he' : Summable (fun k => f (2*k+1)) := he
  have ho' : Summable (fun k => f (2*k+1+1)) := by simpa [Nat.add_assoc] using ho
  have ht : Summable (fun k => f (k+1)) := Summable.even_add_odd (f := fun k => f (k+1)) he' ho'
  have hf : Summable f := (summable_nat_add_iff 1).1 ht
  have hsum := tsum_even_add_odd (f := fun k => f (k+1)) he' ho'
  rw [hf.tsum_eq_zero_add]
  change multiStepStage (n+1) π θ 0 + ∑' k : ℕ, (f (2*k+1) + f (2*k+2)) =
    f 0 + ∑' k : ℕ, f (k+1)
  rw [he.tsum_add ho]
  simpa only [Nat.add_assoc, f, pow_zero, one_mul] using congrArg (fun x => f 0 + x) hsum

/-- A positive average rate makes the actual unnormalized finite returns diverge. -/
theorem multiStepPriorFinite_tendsto_atTop (n : ℕ)
    (π : ValidCausalPolicy Action Observation) (hs : inspectionProbability π.1 < 1) :
    Tendsto (multiStepPriorFinite (n+1) π) atTop atTop := by
  have hc : 0 < (1 - inspectionProbability π.1) * Real.log 2 / 2 := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have h := (multiStepPriorAverage_tendsto n π).pos_mul_atTop hc
    (tendsto_natCast_atTop_atTop : Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with H hH
  dsimp [multiStepPriorAverage]
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  exact div_mul_cancel₀ _ hH0

theorem multiStepDiscounted_eq (n : ℕ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) (θ : World) :
    multiStepDiscounted (n+1) γ π θ = multiStepCapacity θ [] (n+1) +
      panelDiscountFactor n γ * (1 - inspectionProbability π.1) * Real.log 2 := by
  have hγ2 : γ^2 < 1 := by nlinarith
  simp only [multiStepDiscounted, multiStepDiscounted_pair, multiStepStage_zero,
    tsum_mul_right, tsum_geometric_of_lt_one (sq_nonneg γ) hγ2, panelDiscountFactor]
  ring

/-- Average the scalar fixed-world return under the paper's world prior. -/
def multiStepPriorDiscounted (n : ℕ) (γ : ℝ)
    (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∫ θ, multiStepDiscounted n γ π θ ∂AlarmPanelPrior.prior

theorem multiStepPriorDiscounted_eq (n : ℕ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    multiStepPriorDiscounted (n+1) γ π =
      (multiStepCapacity none [] (n+1) + multiStepCapacity (some 0) [] (n+1)) / 2 +
      panelDiscountFactor n γ * (1 - inspectionProbability π.1) * Real.log 2 := by
  unfold multiStepPriorDiscounted
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    rw [multiStepDiscounted_eq n γ hγ0 hγ1,
      multiStepDiscounted_eq n γ hγ0 hγ1, multiStepCapacity_root_some])]
  rw [multiStepDiscounted_eq n γ hγ0 hγ1, multiStepDiscounted_eq n γ hγ0 hγ1]
  ring

theorem multiStepPriorDiscounted_maximizer_iff (n : ℕ) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, multiStepPriorDiscounted (n+1) γ ρ ≤ multiStepPriorDiscounted (n+1) γ π) ↔
      inspectionProbability π.1 = 0 := by
  have hp := panelDiscountFactor_pos n γ hγ0 hγ1
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have hh := h noveltyPolicy
    have hz : inspectionProbability noveltyPolicy.1 = 0 := noveltyPolicy_root
    rw [multiStepPriorDiscounted_eq n γ hγ0.le hγ1,
      multiStepPriorDiscounted_eq n γ hγ0.le hγ1, hz] at hh
    have hr : 0 ≤ inspectionProbability π.1 := (π.2 []).1 0
    nlinarith [mul_pos hp hl]
  · intro h ρ
    rw [multiStepPriorDiscounted_eq n γ hγ0.le hγ1,
      multiStepPriorDiscounted_eq n γ hγ0.le hγ1, h]
    have hr : 0 ≤ inspectionProbability ρ.1 := (ρ.2 []).1 0
    nlinarith [mul_pos hp hl]

/-- Actual native failure for every positive probe length and proper discount. -/
theorem multiStepDiscounted_all_positive_horizons (n : ℕ) (hn : 1 ≤ n)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∃ π, ∀ ρ, multiStepPriorDiscounted n γ ρ ≤ multiStepPriorDiscounted n γ π) ∧
      ∀ π : ValidCausalPolicy Action Observation,
        (∀ ρ, multiStepPriorDiscounted n γ ρ ≤ multiStepPriorDiscounted n γ π) →
          (∀ t : ℕ, 1 ≤ t →
            finiteDeficiency (experiment π.1 t) (experiment inspectPolicy 1) = 1 / 2) ∧
          eventualInspectionDeficiency π = 1 / 2 ∧
          CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
          ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine ⟨⟨noveltyPolicy, (multiStepPriorDiscounted_maximizer_iff m γ hγ0 hγ1
    noveltyPolicy).2 noveltyPolicy_root⟩, ?_⟩
  intro π hopt
  apply longRunEmpowermentAverage_all_optima_failure.2 π
  exact (longRunEmpowermentAverage_maximizer_iff π).2
    ((multiStepPriorDiscounted_maximizer_iff m γ hγ0 hγ1 π).1 hopt)

end
end IdExp.AlarmPanel.Control
