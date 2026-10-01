import Formal.PulseBrierMovement
import Formal.CountableInformationCeiling

/-! The full-support countable pulse prior has finite entropy exactly two bits.
Both integrability and the value use its actual singleton masses. -/
namespace IdExp.PulseInformation
open MeasureTheory Finset Set Filter Topology
open PulseBrierScore (World prior geometricWorldEquiv geometric_index_mass)
noncomputable section

def surprisal (θ : World) : ℝ := -Real.log (prior.real {θ})

theorem mass_pos (θ : World) : 0 < prior.real {θ} := by
  cases θ with
  | none => rw [waitingQueryGeometricPrior_none]; norm_num
  | some k => rw [waitingQueryGeometricPrior_some]; positivity

theorem surprisal_nonneg (θ : World) : 0 ≤ surprisal θ := by
  exact neg_nonneg.mpr (Real.log_nonpos (mass_pos θ).le measureReal_le_one)

theorem surprisal_index (n : ℕ) :
    surprisal (geometricWorldEquiv n) = (n+1 : ℝ) * Real.log 2 := by
  rw [surprisal, geometric_index_mass, Real.log_pow]
  norm_num [Real.log_div]

theorem entropy_hasSum :
    HasSum (fun θ : World => prior.real {θ} * surprisal θ) (2 * Real.log 2) := by
  rw [← geometricWorldEquiv.hasSum_iff]
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have hg := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)<1)
  have h := ((hn.add hg).mul_right (1/2:ℝ)).mul_right (Real.log 2)
  convert! h using 1
  · funext n
    simp only [Function.comp_apply]
    rw [geometric_index_mass, surprisal_index, pow_succ]
    ring
  · norm_num

theorem surprisal_integrable : Integrable surprisal prior := by
  have hs : Summable (fun θ : World => (prior {θ}).toReal * ‖surprisal θ‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (surprisal_nonneg _), ← measureReal_def]
      using entropy_hasSum.summable
  have hi := integrable_sum_dirac (c := fun θ => prior {θ}) (x := id) (f := surprisal)
    (fun θ => measure_ne_top prior {θ}) hs
  simpa using hi

theorem prior_entropy : (∫ θ, surprisal θ ∂prior) = 2 * Real.log 2 := by
  rw [integral_countable surprisal_integrable]
  simpa only [smul_eq_mul] using entropy_hasSum.tsum_eq

end
end IdExp.PulseInformation
