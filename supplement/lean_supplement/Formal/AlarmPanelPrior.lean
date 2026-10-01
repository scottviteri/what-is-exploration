import Formal.PulsePriorEntropy

/-! The fixed countable full-support prior for the alarm/panel study. -/
namespace IdExp.AlarmPanelPrior
open MeasureTheory Set
noncomputable section

abbrev World := WaitingQueryWorld
abbrev prior := waitingQueryGeometricPrior

/-- Any integrand constant on finite alarm times reduces to the fair bit prior. -/
theorem integral_none_some (f : World → ℝ)
    (hf : ∀ k : ℕ, f (some k) = f (some 0)) :
    (∫ θ, f θ ∂prior) = (1/2 : ℝ) * f none + (1/2 : ℝ) * f (some 0) := by
  have he : f = fun θ => f (some 0) +
      ({none} : Set World).indicator (fun _ => f none - f (some 0)) θ := by
    funext θ
    cases θ with
    | none => simp
    | some k => simp [hf k]
  conv_lhs => rw [he]
  rw [integral_add (integrable_const _)
    ((integrable_const _).indicator (measurableSet_singleton _)),
    integral_indicator_const _ (measurableSet_singleton _)]
  simp only [integral_const, smul_eq_mul]
  have hu : prior.real Set.univ = 1 := by simp [prior]
  rw [hu]
  rw [waitingQueryGeometricPrior_none]
  ring

/-- The indicator of a finite alarm has probability one half. -/
theorem integral_isSome :
    (∫ θ : World, (if θ.isSome then (1 : ℝ) else 0) ∂prior) = 1/2 := by
  rw [integral_none_some _ (by intro k; rfl)]
  norm_num

end
end IdExp.AlarmPanelPrior
