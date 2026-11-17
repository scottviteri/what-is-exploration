import Formal.CausalBayesianPredictionGain
import Formal.PairedAlarm

/-! # Bayesian prediction gain on the literal coinless paired alarm
Every response likelihood is a constant on one answer cell and zero elsewhere.
This includes startup, every later alarm tick, arbitrary legal actions and
arbitrary off-support histories. PLAY display randomness is world independent.
-/
namespace IdExp.PairedAlarm
noncomputable section
open BayesianPredictionGain

/-- The actual response kernel has the deterministic-cell likelihood shape. -/
theorem response_likelihood_cell (h : History) (a : Action) (o : Observation) :
    ∃ (s : Set World) (c : ℝ), (fun θ => response θ h a o) = cellLikelihood s c := by
  classical
  by_cases hh : h = []
  · subst h
    by_cases ha : a = inspect
    · refine ⟨{θ | o.1 = if θ.isSome then 2 else 0}, pointMonitor 0 o.2, ?_⟩
      funext θ
      simp only [response_root, rootDisplay, ha, ↓reduceIte, pointDisplay,
        cellLikelihood, Set.mem_setOf_eq]
      split_ifs <;> ring
    · refine ⟨Set.univ, pointDisplay 0 o.1 * pointMonitor 0 o.2, ?_⟩
      funext θ
      simp [response_root, rootDisplay, ha, cellLikelihood]
  · refine ⟨{θ | o.2 = monitorLabel θ (h.length - 1)}, panelDisplay h a o.1, ?_⟩
    funext θ
    rw [response_tick θ h a o hh]
    simp only [pointMonitor, cellLikelihood, Set.mem_setOf_eq]
    split_ifs <;> ring

/-- PG and posterior KL agree on each actual positive-probability update, for
any prior on the countable alarm class. -/
theorem replayGain_eq_informationGain (prior : World → ℝ) (h : History)
    (a : Action) (o : Observation)
    (hz : predictive (historyPosterior prior response h) (fun θ => response θ h a o) ≠ 0) :
    historyReplayGain prior response h a o =
      ∑' θ, historyPosterior prior response (h ++ [(a,o)]) θ *
        Real.logb 2 (historyPosterior prior response (h ++ [(a,o)]) θ /
          historyPosterior prior response h θ) := by
  obtain ⟨s,c,hL⟩ := response_likelihood_cell h a o
  exact historyReplayGain_eq_informationGain_of_cell prior response h a o s c hL hz

/-- A posterior supplied by the preceding history gives the same equality even
on zero-probability responses, using the shared zero-reward convention. -/
theorem oneStepGain_eq_informationGain (q : World → ℝ) (h : History)
    (a : Action) (o : Observation) :
    gain q (fun θ => response θ h a o) = informationGain q (fun θ => response θ h a o) := by
  obtain ⟨s,c,hL⟩ := response_likelihood_cell h a o
  rw [hL]
  exact gain_eq_informationGain_cell_total q s c

end
end IdExp.PairedAlarm
