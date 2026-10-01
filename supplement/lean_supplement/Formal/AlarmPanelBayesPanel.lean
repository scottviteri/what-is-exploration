import Formal.AlarmPanelBayesEntropy

/-! Every active panel contributes irreducible Bayesian prediction error,
uniformly over all adaptive randomized continuations. -/
namespace IdExp.AlarmPanelBayes
open MeasureTheory Finset
open AlarmPanel
noncomputable section

theorem response_panel_independent (n : ℕ) (hn : n%2=1) (u : Trace n)
    (θ : World) (a : Action) :
    response θ (List.ofFn u) a = response none (List.ofFn u) a := by
  have he : List.ofFn u ≠ [] := by intro h; have := congrArg List.length h; simp at this; omega
  funext o
  simp [response, he, hn]

theorem predictive_panel (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (hn : n%2=1) (u : Trace n) (hm : mass π n u ≠ 0) (a : Action) :
    predictive π n u a = response none (List.ofFn u) a := by
  funext o
  have hj : joint π n u a o = mass π n u * response none (List.ofFn u) a o := by
    unfold joint mass priorSignalMass
    simp_rw [response_panel_independent n hn u]
    exact integral_mul_const _ _
  simp only [predictive, hm, if_false, hj]
  field_simp

theorem noiseStage_panel (π : ValidCausalPolicy Action Observation) (n : ℕ) (hn : n%2=1) :
    noiseStage π n = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a *
      ent (response none (List.ofFn u) a) := by
  unfold noiseStage worldNoise
  simp_rw [response_panel_independent n hn]
  rw [integral_finsetSum _ (fun u _ => (record_integrable π n u).mul_const _)]
  simp only [integral_mul_const, mass, priorSignalMass]

theorem panel_squared_entropy (n : ℕ) (hn : n%2=1) (u : Trace n) (a : Action) :
    (1-∑ o, response none (List.ofFn u) a o ^ 2) * (2 * Real.log 2) =
      ent (response none (List.ofFn u) a) := by
  have he : List.ofFn u ≠ [] := by intro h; have := congrArg List.length h; simp at this; omega
  by_cases hi : inspected (List.ofFn u)
  · have hr : response none (List.ofFn u) a = pointDist 0 := by
      funext o; simp [response, he, hn, hi]
    rw [hr, MOP.pointDist_entropy]
    norm_num [pointDist, Fin.sum_univ_succ]
  · have hr : response none (List.ofFn u) a = pairDist (a == play1) := by
      funext o; simp [response, he, hn, hi]
    rw [hr, Control.pairDist_entropy]
    cases h : (a == play1) <;> norm_num [pairDist, Fin.sum_univ_succ] <;> ring

theorem squaredStage_panel (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    squaredStage π (2*k+1) = (1-inspectionProbability π.1)/2 := by
  have hn : (2*k+1)%2=1 := by omega
  have he : squaredStage π (2*k+1) * (2*Real.log 2) = noiseStage π (2*k+1) := by
    rw [squaredStage_eq, noiseStage_panel π _ hn]
    simp only [sum_mul, mul_assoc]
    apply sum_congr rfl; intro u _
    by_cases hm : mass π (2*k+1) u = 0
    · simp [hm]
    · congr 1
      apply sum_congr rfl; intro a _
      rw [predictive_panel π _ hn u hm a, panel_squared_entropy _ hn]
  rw [noiseStage_succ π (2*k), if_pos hn] at he
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_right_cancel₀ (ne_of_gt hl))
  nlinarith


/-- Each active panel tick contributes one bit of predictive surprisal. -/
theorem logStage_panel (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    logStage π (2*k+1) = (1-inspectionProbability π.1) * Real.log 2 := by
  have hn : (2*k+1)%2=1 := by omega
  have he : logStage π (2*k+1) = noiseStage π (2*k+1) := by
    rw [logStage_eq, noiseStage_panel π _ hn]
    apply sum_congr rfl; intro u _
    by_cases hm : mass π (2*k+1) u = 0
    · simp [hm]
    · congr 1
      apply sum_congr rfl; intro a _
      rw [predictive_panel π _ hn u hm a]
  rw [he, noiseStage_succ π (2*k), if_pos hn]

end
end IdExp.AlarmPanelBayes
