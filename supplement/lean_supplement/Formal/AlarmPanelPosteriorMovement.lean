import Formal.PosteriorMovement

/-! Literal expected Hellinger/Absolute rewards on the original alarm/panel
interface, for every randomized history-dependent continuation policy. -/
noncomputable section
namespace IdExp.AlarmPanelMovement
open AlarmPanel AlarmPanelVariance PosteriorMovement MeasureTheory Finset Set

def localReward (kind : Kind) (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) : ℝ :=
  reward kind (posteriorMeasure π t h) (fun θ => response θ (List.ofFn h) a)

def stage (kind : Kind) (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation t,
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 t) h *
      ∑ a : Action, π.1 (List.ofFn h) a * localReward kind π t h a

def discounted (kind : Kind) (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, γ^t * stage kind π t

def inspectTerm (kind : Kind) (k : ℕ) : ℝ := 2 * alarmMass k * fairReward kind

def playTerm (kind : Kind) (k : ℕ) : ℝ :=
  silentMass k * binaryReward kind (alarmMass k / silentMass k)

theorem reward_monitor (kind : Kind) (μ : Measure World) [IsProbabilityMeasure μ] (k : ℕ) :
    reward kind μ (fun θ => pointDist (monitorLabel θ k)) =
      binaryReward kind (μ.real {some k}) := by
  have h0 : (fun θ : World => pointDist (monitorLabel θ k) 0) =
      ({some k}ᶜ : Set World).indicator (fun _ => (1:ℝ)) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (0:Observation) ≠ 1 by decide]
  have h1 : (fun θ : World => pointDist (monitorLabel θ k) 1) =
      ({some k} : Set World).indicator (fun _ => (1:ℝ)) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (1:Observation) ≠ 0 by decide]
  have h2 : (fun θ : World => pointDist (monitorLabel θ k) 2) = fun _ => (0:ℝ) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (2:Observation) ≠ 1 by decide,
        show (2:Observation) ≠ 0 by decide]
  have h3 : (fun θ : World => pointDist (monitorLabel θ k) 3) = fun _ => (0:ℝ) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (3:Observation) ≠ 1 by decide,
        show (3:Observation) ≠ 0 by decide]
  rw [reward, sum_observation, h0, h1, h2, h3,
    coordinate_indicator kind μ _ (measurableSet_singleton _).compl,
    coordinate_indicator kind μ _ (measurableSet_singleton _),
    measureReal_compl (measurableSet_singleton _)]
  cases kind <;> simp [coordinate, loss, binaryReward] <;> ring

theorem local_panel (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+1)) (a : Action) :
    localReward kind π (2*k+1) h a = 0 := by
  have hp : (List.ofFn h).length % 2 = 1 := by simp only [List.length_ofFn]; omega
  have he : (fun θ => response θ (List.ofFn h) a) = (fun _ =>
      if inspected (List.ofFn h) then pointDist 0 else pairDist (a == play1)) := by
    funext θ o; simpa only [ite_apply] using response_panel θ _ a o hp
  rw [localReward, he]
  exact reward_constant _ _ _

theorem local_monitor (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2)) (a : Action) :
    localReward kind π (2*k+2) h a =
      binaryReward kind ((posteriorMeasure π (2*k+2) h).real {some k}) := by
  have hn : List.ofFn h ≠ [] := by simp
  have hp : (List.ofFn h).length % 2 ≠ 1 := by simp only [List.length_ofFn]; omega
  have hk : ((List.ofFn h).length - 2)/2 = k := by simp only [List.length_ofFn]; omega
  have he : (fun θ => response θ (List.ofFn h) a) =
      fun θ => pointDist (monitorLabel θ k) := by
    funext θ o; rw [response_monitor θ _ a o hn hp, hk]
  rw [localReward, he, reward_monitor]

theorem stage_panel (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    stage kind π (2*k+1) = 0 := by simp [stage, local_panel]

theorem reward_root (kind : Kind) (a : Action) :
    reward kind AlarmPanelPrior.prior (fun θ => response θ [] a) =
      if a = inspect then fairReward kind else 0 := by
  have hm (o : Observation) : (∫ θ, response θ [] a o ∂AlarmPanelPrior.prior) =
      (1/2:ℝ) * response none [] a o + (1/2:ℝ) * response (some 0) [] a o :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [response_root])
  have he (o : Observation) (m : ℝ) :
      (∫ θ, loss kind (response θ [] a o) m ∂AlarmPanelPrior.prior) =
      (1/2:ℝ)*loss kind (response none [] a o) m +
      (1/2:ℝ)*loss kind (response (some 0) [] a o) m :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [response_root])
  simp only [reward, coordinate, hm, he, sum_observation]
  by_cases hi : a = inspect
  · subst a
    have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      apply inv_eq_of_mul_eq_one_right
      nlinarith
    cases kind <;> norm_num [response_root, pairDist, loss, fairReward,
      Real.sqrt_div, hinv] <;> nlinarith
  · cases kind <;> norm_num [response_root, hi, uniformDist, loss]

theorem stage_root (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    stage kind π 0 = inspectionProbability π.1 * fairReward kind := by
  have hm (h : CausalFiniteTrace Action Observation 0) :
      priorSignalMass AlarmPanelPrior.prior (experiment π.1 0) h = 1 := by
    simp [priorSignalMass, experiment, causalFiniteExperiment, causalTraceProb,
      causalTraceProbFrom, List.ofFn_zero]
  simp [stage, hm, localReward, List.ofFn_zero, posteriorMeasure_root,
    reward_root, mul_ite, inspectionProbability]

theorem monitor_weighted (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2)) (a : Action) :
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h *
      localReward kind π (2*k+2) h a =
      experiment π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then inspectTerm kind k else playTerm kind k) := by
  rw [local_monitor]
  by_cases hr : experiment π.1 (2*k+2) (some k) h = 0
  · rw [hr, zero_mul]
    by_cases hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h = 0
    · rw [hm, zero_mul]
    · rw [posterior_monitor_atom π k h hm, hr]
      simp
  · have hmass := monitor_predictive_mass π k h hr
    have ha := alarmMass_pos k
    have hs := silentMass_pos k
    have hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h ≠ 0 := by
      rw [hmass]; apply mul_ne_zero hr; split <;> positivity
    rw [posterior_monitor_atom π k h hm, hmass]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi, if_pos hi]
      have he : alarmMass k * experiment π.1 (2*k+2) (some k) h /
          (experiment π.1 (2*k+2) (some k) h * (2*alarmMass k)) = (1/2:ℝ) := by
        field_simp
      rw [he, binaryReward_half]
      simp [inspectTerm]; ring
    · rw [if_neg hi, if_neg hi]
      have he : alarmMass k * experiment π.1 (2*k+2) (some k) h /
          (experiment π.1 (2*k+2) (some k) h * silentMass k) = alarmMass k / silentMass k := by
        field_simp
      rw [he]; simp [playTerm]; ring

/-- Actual reward at every monitor, with all later actions integrated out. -/
theorem stage_monitor (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    stage kind π (2*k+2) = inspectionProbability π.1 * inspectTerm kind k +
      (1-inspectionProbability π.1) * playTerm kind k := by
  have he (h : CausalFiniteTrace Action Observation (2*k+2)) :
      priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h *
        (∑ a : Action, π.1 (List.ofFn h) a * localReward kind π (2*k+2) h a) =
      experiment π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then inspectTerm kind k else playTerm kind k) := by
    simp only [mul_sum, mul_left_comm _ (π.1 (List.ofFn h) _), monitor_weighted,
      ← sum_mul, (π.2 (List.ofFn h)).2, one_mul]
  simp only [stage, he]
  have hd (h : CausalFiniteTrace Action Observation (2*k+2)) :
      experiment π.1 (2*k+2) (some k) h *
          (if (h 0).1 = inspect then inspectTerm kind k else playTerm kind k) =
      (if (h 0).1 = inspect then experiment π.1 (2*k+2) (some k) h else 0) *
          (inspectTerm kind k - playTerm kind k) +
        experiment π.1 (2*k+2) (some k) h * playTerm kind k := by split <;> ring
  simp_rw [hd]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul,
    rootInspection_mass π.1 π.2 (some k) (2*k+1), (experiment_valid π.1 π.2 _ (some k)).2]
  ring

end IdExp.AlarmPanelMovement
