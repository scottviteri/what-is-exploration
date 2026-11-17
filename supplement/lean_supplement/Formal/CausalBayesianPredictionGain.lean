import Formal.BayesianPredictionGain
import Formal.CausalExperiment

/-! # Bayesian replay rewards on actual controlled histories
The posterior uses the likelihood of the full controlled action-observation
history. A policy's world-independent factor cancels on reachable histories.
The context and observed response are held fixed when the new posterior rescores
that response; this is not a prediction at the next interaction.
-/
namespace IdExp.BayesianPredictionGain
noncomputable section
variable {Θ A O : Type*} [Fintype A] [Fintype O]

def historyPosterior (prior : Θ → ℝ) (Q : Θ → CausalResponse A O)
    (h : CausalHistory A O) : Θ → ℝ :=
  posterior prior (fun θ => causalResponseProb (Q θ) h)

def historyReplayGain (prior : Θ → ℝ) (Q : Θ → CausalResponse A O)
    (h : CausalHistory A O) (a : A) (o : O) : ℝ :=
  Real.logb 2 ((∑' θ, historyPosterior prior Q (h ++ [(a,o)]) θ * Q θ h a o) /
    predictive (historyPosterior prior Q h) (fun θ => Q θ h a o))

theorem historyPosterior_append (prior : Θ → ℝ) (Q : Θ → CausalResponse A O)
    (h : CausalHistory A O) (a : A) (o : O)
    (hz : predictive (historyPosterior prior Q h) (fun θ => Q θ h a o) ≠ 0) :
    historyPosterior prior Q (h ++ [(a,o)]) =
      posterior (historyPosterior prior Q h) (fun θ => Q θ h a o) := by
  have hN : predictive prior (fun θ => causalResponseProb (Q θ) h) ≠ 0 := by
    intro hN
    apply hz
    have hp : historyPosterior prior Q h = fun _ => 0 := by
      funext θ
      simp only [historyPosterior, posterior, hN, div_zero]
    simp only [hp, predictive, zero_mul, tsum_zero]
  simp only [historyPosterior]
  rw [posterior_update _ _ _ hN]
  congr 1
  funext θ
  exact causalResponseProb_append_singleton (Q θ) h (a,o)

theorem historyReplayGain_eq (prior : Θ → ℝ) (Q : Θ → CausalResponse A O)
    (h : CausalHistory A O) (a : A) (o : O)
    (hz : predictive (historyPosterior prior Q h) (fun θ => Q θ h a o) ≠ 0) :
    historyReplayGain prior Q h a o =
      gain (historyPosterior prior Q h) (fun θ => Q θ h a o) := by
  rw [historyReplayGain, historyPosterior_append prior Q h a o hz]
  rfl

/-- Retaining the policy's action probabilities gives the same posterior. -/
theorem historyPosterior_eq_pathPosterior (prior : Θ → ℝ)
    (Q : Θ → CausalResponse A O) (π : CausalPolicy A O) (h : CausalHistory A O)
    (hπ : causalPolicyProb π h ≠ 0) :
    posterior prior (fun θ => causalTraceProb π (Q θ) h) = historyPosterior prior Q h := by
  have hfactor : (fun θ => causalTraceProb π (Q θ) h) =
      (fun θ => causalResponseProb (Q θ) h * causalPolicyProb π h) := by
    funext θ
    rw [causalTraceProb_factor, mul_comm]
  rw [hfactor]
  exact posterior_scale _ _ _ hπ

/-- A deterministic answer cell, possibly accompanied by independent noise,
gives exactly the posterior-KL reward on the actual retained history. -/
theorem historyReplayGain_eq_informationGain_of_cell (prior : Θ → ℝ)
    (Q : Θ → CausalResponse A O) (h : CausalHistory A O) (a : A) (o : O)
    (s : Set Θ) (c : ℝ)
    (hL : (fun θ => Q θ h a o) = cellLikelihood s c)
    (hz : predictive (historyPosterior prior Q h) (fun θ => Q θ h a o) ≠ 0) :
    historyReplayGain prior Q h a o =
      ∑' θ, historyPosterior prior Q (h ++ [(a,o)]) θ *
        Real.logb 2 (historyPosterior prior Q (h ++ [(a,o)]) θ /
          historyPosterior prior Q h θ) := by
  rw [historyReplayGain_eq prior Q h a o hz,
    historyPosterior_append prior Q h a o hz]
  change gain _ _ = informationGain _ _
  rw [hL]
  exact gain_eq_informationGain_cell_total _ s c

end
end IdExp.BayesianPredictionGain
