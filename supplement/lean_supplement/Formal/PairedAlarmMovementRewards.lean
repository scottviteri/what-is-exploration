import Formal.PairedAlarmMovementPosterior
import Formal.PosteriorMovementBayes

/-!
# Published Hellinger and Absolute rewards on the paired alarm

The literal expected Hellinger `Σ(√p-√q)²` and Absolute `Σ|p-q|` rewards of
Orseau, Lattimore and Hutter (2013, equations 3--5), on the Bayesian posterior
over worlds given the entire retained action-observation record, for every
randomized history-dependent policy. As in `Formal.AlarmPanelPosteriorMovement`,
the local reward is the source's conditional expected reward
`Σ_θ β_h(θ) Σ_o d(Q_θ(o|h,a), q̄(o))` (generic `PosteriorMovement.reward`);
`localReward_eq_expected_movement` restates the generic Bayes identity
equating it with the expected movement of that posterior under one Bayes update
by the next raw observation, null observations included.

The scored variable is the raw observation pair (display, monitor). Because
the display factor is world-independent, positive homogeneity of both losses
removes it exactly (`reward_prod_const_right`, `reward_prod_const_left`). The
startup observation pays `fairReward` on INSPECT and zero on PLAY; the
observation after a history of length `k+1` is the deterministic yes/no query
`θ = some k` on the current posterior. Its expected value is
`s·inspectTerm k + (1-s)·playTerm k`, with all later actions integrated out.
-/

noncomputable section
namespace IdExp.PairedAlarm.Movement
open PosteriorMovement MeasureTheory Finset Set
open AlarmPanelVariance (alarmMass silentMass alarmMass_pos silentMass_pos silentMass_eq)

/-- The published expected reward for proposing action `a` after the retained
record `h`, scored on the posterior of the whole record. -/
def localReward (kind : Kind) (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) : ℝ :=
  reward kind (posteriorMeasure π t h) (fun θ => response θ (List.ofFn h) a)

/-- Expected reward of the observation made after a history of length `t`
(step `t+1`), under the prior-predictive law of the policy's record. -/
def stage (kind : Kind) (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation t,
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 t) h *
      ∑ a : Action, π.1 (List.ofFn h) a * localReward kind π t h a

/-- Geometric weights `γ^(t-1)` on step `t`; the startup step has weight one.
At `γ = 1` this is the complete undiscounted return. -/
def discounted (kind : Kind) (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, γ^t * stage kind π t

/-- The complete undiscounted return (the source's all-ones weight vector). -/
def complete (kind : Kind) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, stage kind π t

theorem complete_eq_discounted_one (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    complete kind π = discounted kind 1 π := by
  simp [complete, discounted]

/-- The local reward is the source's conditional expectation of the posterior
movement `r_d(β_h, β')`, where `β'` is the Bayes update of the current
full-history posterior by the next raw observation; null observations
contribute zero. This is the generic `PosteriorMovementBayes` identity. -/
theorem localReward_eq_expected_movement (kind : Kind)
    (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) :
    (∑ o, priorSignalMass (posteriorMeasure π t h) (fun θ => response θ (List.ofFn h) a) o *
      ∑' θ, loss kind (CountableBrier.posterior (posteriorMeasure π t h)
        (fun θ => response θ (List.ofFn h) a) (fun θ => response_valid θ (List.ofFn h) a) o θ)
        ((posteriorMeasure π t h).real {θ})) =
    localReward kind π t h a :=
  expected_posterior_movement_eq_reward kind (posteriorMeasure π t h)
    (fun θ => response θ (List.ofFn h) a) (fun θ => response_valid θ (List.ofFn h) a)

/-- Positive homogeneity of both losses moves a known nonnegative factor out
of a predictive coordinate. -/
theorem coordinate_const_mul {Θ : Type*} [MeasurableSpace Θ] (kind : Kind) (μ : Measure Θ)
    (c : ℝ) (hc : 0 ≤ c) (f : Θ → ℝ) (hf : ∀ θ, 0 ≤ f θ) :
    coordinate kind μ (fun θ => c * f θ) = c * coordinate kind μ f := by
  unfold coordinate
  have hI : 0 ≤ ∫ η, f η ∂μ := integral_nonneg hf
  rw [integral_const_mul]
  simp_rw [loss_scale kind c _ _ hc (hf _) hI]
  rw [integral_const_mul]

/-- A world-independent first observation coordinate is removed exactly:
only its total mass remains. -/
theorem reward_prod_const_right {Θ D M : Type*} [MeasurableSpace Θ] [Fintype D] [Fintype M]
    (kind : Kind) (μ : Measure Θ) (c : D → ℝ) (hc : ∀ d, 0 ≤ c d)
    (q : Θ → M → ℝ) (hq : ∀ θ m, 0 ≤ q θ m) :
    reward kind μ (fun θ (o : D × M) => c o.1 * q θ o.2) = (∑ d, c d) * reward kind μ q := by
  unfold reward
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact coordinate_const_mul kind μ (c d) (hc d) (fun θ => q θ m) (fun θ => hq θ m)

/-- A world-independent second observation coordinate is removed exactly. -/
theorem reward_prod_const_left {Θ D M : Type*} [MeasurableSpace Θ] [Fintype D] [Fintype M]
    (kind : Kind) (μ : Measure Θ) (q : Θ → D → ℝ) (hq : ∀ θ d, 0 ≤ q θ d)
    (c : M → ℝ) (hc : ∀ m, 0 ≤ c m) :
    reward kind μ (fun θ (o : D × M) => q θ o.1 * c o.2) = (∑ m, c m) * reward kind μ q := by
  unfold reward
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  show coordinate kind μ (fun θ => q θ d * c m) = c m * coordinate kind μ (fun θ => q θ d)
  simp_rw [mul_comm (q _ d) (c m)]
  exact coordinate_const_mul kind μ (c m) (hc m) (fun θ => q θ d) (fun θ => hq θ d)

/-- The monitor coordinate is the deterministic yes/no query `θ = some k`. -/
theorem reward_monitor (kind : Kind) (μ : Measure World) [IsProbabilityMeasure μ] (k : ℕ) :
    reward kind μ (fun θ => pointMonitor (monitorLabel θ k)) =
      binaryReward kind (μ.real {some k}) := by
  have h0 : (fun θ : World => pointMonitor (monitorLabel θ k) 0) =
      ({some k}ᶜ : Set World).indicator (fun _ => (1:ℝ)) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointMonitor, monitorLabel, h, show (0:Monitor) ≠ 1 by decide]
  have h1 : (fun θ : World => pointMonitor (monitorLabel θ k) 1) =
      ({some k} : Set World).indicator (fun _ => (1:ℝ)) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointMonitor, monitorLabel, h, show (1:Monitor) ≠ 0 by decide]
  rw [reward, Fin.sum_univ_two, h0, h1,
    coordinate_indicator kind μ _ (measurableSet_singleton _).compl,
    coordinate_indicator kind μ _ (measurableSet_singleton _),
    measureReal_compl (measurableSet_singleton _)]
  cases kind <;> simp [binaryReward] <;> ring

/-- After a history of length `k+1`, the published reward is the binary query
reward of the current posterior probability that the alarm rings at tick `k`;
the display carries no world information. -/
theorem local_tick (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (k+1)) (a : Action) :
    localReward kind π (k+1) h a =
      binaryReward kind ((posteriorMeasure π (k+1) h).real {some k}) := by
  have hn : List.ofFn h ≠ [] := by simp
  have hk : (List.ofFn h).length - 1 = k := by simp
  have he : (fun θ => response θ (List.ofFn h) a) =
      fun θ (o : Observation) =>
        panelDisplay (List.ofFn h) a o.1 * pointMonitor (monitorLabel θ k) o.2 := by
    funext θ o; rw [response_tick θ _ a o hn, hk]
  rw [localReward, he, reward_prod_const_right kind _ _ (panelDisplay_valid _ a).1 _
    (fun θ => (pointMonitor_valid _).1), (panelDisplay_valid _ a).2, one_mul, reward_monitor]

/-- The startup display reward under the prior. -/
theorem reward_rootDisplay (kind : Kind) (a : Action) :
    reward kind AlarmPanelPrior.prior (fun θ => rootDisplay θ a) =
      if a = inspect then fairReward kind else 0 := by
  have hm (d : Display) : (∫ θ, rootDisplay θ a d ∂AlarmPanelPrior.prior) =
      (1/2:ℝ) * rootDisplay none a d + (1/2:ℝ) * rootDisplay (some 0) a d :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [rootDisplay])
  have he (d : Display) (m : ℝ) :
      (∫ θ, loss kind (rootDisplay θ a d) m ∂AlarmPanelPrior.prior) =
      (1/2:ℝ)*loss kind (rootDisplay none a d) m +
      (1/2:ℝ)*loss kind (rootDisplay (some 0) a d) m :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [rootDisplay])
  simp only [reward, coordinate, hm, he, Fin.sum_univ_four]
  by_cases hi : a = inspect
  · subst a
    have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      apply inv_eq_of_mul_eq_one_right
      nlinarith
    cases kind
    · norm_num [rootDisplay, pointDisplay, Fin.ext_iff, loss, fairReward, Real.sqrt_div, hinv]
      nlinarith
    · norm_num [rootDisplay, pointDisplay, Fin.ext_iff, loss, fairReward]
  · cases kind <;> norm_num [rootDisplay, hi, pointDisplay, loss, Fin.ext_iff]

/-- The startup observation pays the fair-query reward on INSPECT, zero on PLAY. -/
theorem reward_root (kind : Kind) (a : Action) :
    reward kind AlarmPanelPrior.prior (fun θ => response θ [] a) =
      if a = inspect then fairReward kind else 0 := by
  have he : (fun θ => response θ [] a) =
      fun θ (o : Observation) => rootDisplay θ a o.1 * pointMonitor 0 o.2 := by
    funext θ o; exact response_root θ a o
  rw [he, reward_prod_const_left kind _ _ (fun θ => (rootDisplay_valid θ a).1) _
    (pointMonitor_valid 0).1, (pointMonitor_valid 0).2, one_mul, reward_rootDisplay]

theorem stage_root (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    stage kind π 0 = inspectionProbability π.1 * fairReward kind := by
  simp [stage, priorSignalMass_zero, localReward, List.ofFn_zero, posteriorMeasure_root,
    reward_root, mul_ite, inspectionProbability]

/-- INSPECT's expected payment at alarm tick `k`: given a positive inspection
answer and no earlier pulse, the unresolved finite worlds have prior mass
`T_k = 2a_k` and the tick is a fair query. -/
def inspectTerm (kind : Kind) (k : ℕ) : ℝ := 2 * alarmMass k * fairReward kind

/-- PLAY's expected payment at alarm tick `k`: the unresolved event, including
the never-alarm world, has prior mass `S_k`, and the tick is a yes/no query with
posterior probability `p_k = a_k/S_k`. -/
def playTerm (kind : Kind) (k : ℕ) : ℝ :=
  silentMass k * binaryReward kind (alarmMass k / silentMass k)

/-- Bayes weighting cancels the known action and display likelihoods,
including every null-record case. -/
theorem tick_weighted (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (k+1)) (a : Action) :
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 (k+1)) h *
      localReward kind π (k+1) h a =
      experiment π.1 (k+1) (some k) h *
        (if (h 0).1 = inspect then inspectTerm kind k else playTerm kind k) := by
  rw [local_tick]
  by_cases hr : experiment π.1 (k+1) (some k) h = 0
  · rw [hr, zero_mul]
    by_cases hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (k+1)) h = 0
    · rw [hm, zero_mul]
    · rw [posterior_tick_atom π k h hm, hr]
      simp
  · have hmass := tick_predictive_mass π k h hr
    have ha := alarmMass_pos k
    have hs := silentMass_pos k
    have hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (k+1)) h ≠ 0 := by
      rw [hmass]; apply mul_ne_zero hr; split <;> positivity
    rw [posterior_tick_atom π k h hm, hmass]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi, if_pos hi]
      have he : alarmMass k * experiment π.1 (k+1) (some k) h /
          (experiment π.1 (k+1) (some k) h * (2*alarmMass k)) = (1/2:ℝ) := by
        field_simp
      rw [he, binaryReward_half]
      simp [inspectTerm]; ring
    · rw [if_neg hi, if_neg hi]
      have he : alarmMass k * experiment π.1 (k+1) (some k) h /
          (experiment π.1 (k+1) (some k) h * silentMass k) = alarmMass k / silentMass k := by
        field_simp
      rw [he]; simp [playTerm]; ring

/-- Exact expected reward at alarm tick `k` (step `k+2`) for every randomized
history policy, with all later actions integrated out. -/
theorem stage_tick (kind : Kind) (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    stage kind π (k+1) = inspectionProbability π.1 * inspectTerm kind k +
      (1-inspectionProbability π.1) * playTerm kind k := by
  have he (h : CausalFiniteTrace Action Observation (k+1)) :
      priorSignalMass AlarmPanelPrior.prior (experiment π.1 (k+1)) h *
        (∑ a : Action, π.1 (List.ofFn h) a * localReward kind π (k+1) h a) =
      experiment π.1 (k+1) (some k) h *
        (if (h 0).1 = inspect then inspectTerm kind k else playTerm kind k) := by
    simp only [mul_sum, mul_left_comm _ (π.1 (List.ofFn h) _), tick_weighted,
      ← sum_mul, (π.2 (List.ofFn h)).2, one_mul]
  simp only [stage, he]
  have hd (h : CausalFiniteTrace Action Observation (k+1)) :
      experiment π.1 (k+1) (some k) h *
          (if (h 0).1 = inspect then inspectTerm kind k else playTerm kind k) =
      (if (h 0).1 = inspect then experiment π.1 (k+1) (some k) h else 0) *
          (inspectTerm kind k - playTerm kind k) +
        experiment π.1 (k+1) (some k) h * playTerm kind k := by split <;> ring
  simp_rw [hd]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul,
    rootInspection_mass π.1 π.2 (some k) k, (experiment_valid π.1 π.2 _ (some k)).2]
  ring

end IdExp.PairedAlarm.Movement
