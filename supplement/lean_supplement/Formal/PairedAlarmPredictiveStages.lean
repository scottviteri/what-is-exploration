import Formal.PairedAlarmPredictiveLikelihood

/-!
# Expected Shannon and Square stages on the paired alarm

Exact expected per-step utilities of the Bayesian next-observation forecast, for
every valid randomized history policy.

* Startup (`t = 0`): the forecast is fair on display labels `0,2`, with monitor bit
  `0` on INSPECT; PLAY is deterministic. Shannon gives `s` bits and Square
  gives `-1 + s/2` for startup inspection probability `s`.
* After a record of length `k+1` (alarm tick `k`), the forecast factorizes as
  (display law) × (monitor law): the display carries no world information and
  the monitor is deterministic in a fixed world, so the posterior only enters
  through the pulse probability of tick `k`. Shannon adds the two entropies and
  Square multiplies the two collision probabilities.

With `a_k = 2^{-(k+2)}`, `T_k = 2 a_k`, `S_k = 1/2 + 2 a_k`, `p_k = a_k / S_k`, and
`h₂` the binary entropy in bits, the expected stage utility of a policy with root
inspection probability `s` is `s · (inspect value) + (1-s) · (play value)`, with

| stage | Shannon inspect | Shannon play | Square inspect | Square play |
|---|---|---|---|---|
| `t = 0` | `1` | `0` | `-1/2` | `-1` |
| `t = k+1` | `T_k` | `1 + S_k h₂(p_k)` | `-1 + a_k` | `-1/2 + a_k (1 - p_k)` |

This holds for every adaptive randomized continuation after startup.
-/

noncomputable section
namespace IdExp.PairedAlarm.Predictive
open MeasureTheory Finset
open AlarmPanelVariance (alarmMass silentMass alarmMass_pos silentMass_pos silentMass_eq
  alarmMass_le_quarter hazard_bounds)

/-! ## Binary entropy in bits and the monitor law -/

/-- Binary entropy in bits, `h₂(p) = -p log₂ p - (1-p) log₂ (1-p)`. -/
def binEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

@[simp] theorem binEntropyBits_zero : binEntropyBits 0 = 0 := by
  simp [binEntropyBits]

@[simp] theorem binEntropyBits_half : binEntropyBits (1/2) = 1 := by
  rw [binEntropyBits, one_div, Real.binEntropy_two_inv, div_self (ne_of_gt log_two_pos)]

theorem binEntropyBits_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binEntropyBits p :=
  div_nonneg (Real.binEntropy_nonneg hp0 hp1) log_two_pos.le

/-- The monitor forecast with pulse probability `q`. -/
def bitLaw (q : ℝ) (m : Monitor) : ℝ := if m = 1 then q else 1 - q

theorem sum_bitLaw (q : ℝ) : ∑ m, bitLaw q m = 1 := by
  simp [bitLaw, Fin.sum_univ_two]

theorem ent_bitLaw (q : ℝ) : ent (bitLaw q) = Real.binEntropy q := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [ent, bitLaw, Fin.sum_univ_two, add_comm]

theorem sum_sq_bitLaw (q : ℝ) : ∑ m, bitLaw q m ^ 2 = 1 - 2 * q * (1 - q) := by
  simp [bitLaw, Fin.sum_univ_two]
  ring

/-! ## Product forecasts -/

/-- Entropy is additive on a product forecast; nonnegativity is not needed. -/
theorem ent_prodLaw {f : Display → ℝ} {g : Monitor → ℝ} (hf : ∑ d, f d = 1)
    (hg : ∑ m, g m = 1) : ent (prodLaw f g) = ent f + ent g := by
  have hrow (d : Display) : ∑ m, Real.negMulLog (f d * g m) =
      Real.negMulLog (f d) + f d * ∑ m, Real.negMulLog (g m) := by
    simp only [Real.negMulLog_mul, sum_add_distrib, ← sum_mul, ← mul_sum, hg, one_mul]
  unfold ent prodLaw
  rw [Fintype.sum_prod_type]
  simp only [hrow, sum_add_distrib, ← sum_mul, hf, one_mul]

/-- Collision probability is multiplicative on a product forecast. -/
theorem sum_sq_prodLaw (f : Display → ℝ) (g : Monitor → ℝ) :
    ∑ o, prodLaw f g o ^ 2 = (∑ d, f d ^ 2) * (∑ m, g m ^ 2) := by
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  simp only [prodLaw, mul_pow]

theorem ent_pairDist (b : Bool) : ent (pairDist b) = Real.log 2 := by
  cases b <;> norm_num [ent, pairDist, Fin.sum_univ_succ, Real.negMulLog, Real.log_div] <;> ring

theorem ent_pointDisplay (x : Display) : ent (pointDisplay x) = 0 := by
  apply sum_eq_zero; intro d _
  unfold pointDisplay
  split_ifs <;> simp

theorem ent_pointMonitor (x : Monitor) : ent (pointMonitor x) = 0 := by
  apply sum_eq_zero; intro m _
  unfold pointMonitor
  split_ifs <;> simp

theorem ent_uniformDist : ent uniformDist = 2 * Real.log 2 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  norm_num [ent, uniformDist, Fin.sum_univ_succ, Real.negMulLog, Real.log_div, h4]
  ring

theorem sum_sq_pairDist (b : Bool) : ∑ d, pairDist b d ^ 2 = 1/2 := by
  cases b <;> norm_num [pairDist, Fin.sum_univ_succ]

theorem sum_sq_pointDisplay (x : Display) : ∑ d, pointDisplay x d ^ 2 = 1 := by
  simp [pointDisplay]

theorem sum_sq_pointMonitor (x : Monitor) : ∑ m, pointMonitor x m ^ 2 = 1 := by
  simp [pointMonitor]

theorem sum_sq_uniformDist : ∑ d, uniformDist d ^ 2 = 1/4 := by
  norm_num [uniformDist, Fin.sum_univ_succ]

theorem inspected_ofFn {n : ℕ} (h : Trace (n+1)) :
    inspected (List.ofFn h) ↔ (h 0).1 = inspect := by
  rw [List.ofFn_succ]
  exact inspected_cons _ _ _

theorem panelDisplay_ofFn {n : ℕ} (h : Trace (n+1)) (a : Action) :
    panelDisplay (List.ofFn h) a =
      if (h 0).1 = inspect then pointDisplay 0 else pairDist (a == play1) := by
  simp only [panelDisplay, inspected_ofFn]

/-- After startup the display forecast has entropy zero after inspection and one bit
after play, whichever later action is proposed. -/
theorem ent_panelDisplay {n : ℕ} (h : Trace (n+1)) (a : Action) :
    ent (panelDisplay (List.ofFn h) a) = if (h 0).1 = inspect then 0 else Real.log 2 := by
  rw [panelDisplay_ofFn]
  split
  · exact ent_pointDisplay 0
  · exact ent_pairDist _

theorem sum_sq_panelDisplay {n : ℕ} (h : Trace (n+1)) (a : Action) :
    ∑ d, panelDisplay (List.ofFn h) a d ^ 2 = if (h 0).1 = inspect then 1 else 1/2 := by
  rw [panelDisplay_ofFn]
  split
  · exact sum_sq_pointDisplay 0
  · exact sum_sq_pairDist _

theorem ent_evenCoin : ent evenCoin = Real.log 2 := by
  norm_num [ent, evenCoin, Fin.sum_univ_succ, Real.negMulLog, Real.log_div]
  ring

theorem sum_sq_evenCoin : ∑ d, evenCoin d ^ 2 = 1/2 := by
  norm_num [evenCoin, Fin.sum_univ_succ]

/-! ## The startup forecast -/

theorem record_zero (π : ValidCausalPolicy Action Observation) (θ : World) (h : Trace 0) :
    record π 0 θ h = 1 := by
  simp [record, experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]

theorem mass_zero (π : ValidCausalPolicy Action Observation) (h : Trace 0) :
    mass π 0 h = 1 := by
  simp [mass, priorSignalMass, record_zero]

/-- At startup INSPECT has a fair prior-predictive answer; PLAY is deterministic. -/
theorem predictive_root (π : ValidCausalPolicy Action Observation) (h : Trace 0) (a : Action) :
    predictive π 0 h a =
      prodLaw (if a = inspect then evenCoin else pointDisplay 0) (pointMonitor 0) := by
  funext o
  simp only [predictive, mass_zero, one_ne_zero, if_false, div_one, joint, record_zero,
    one_mul, List.ofFn_zero]
  rw [AlarmPanelPrior.integral_none_some _ (by intro k; simp [response_root, rootDisplay])]
  rcases o with ⟨d, m⟩
  simp only [response_root, prodLaw]
  by_cases ha : a = inspect
  · subst ha
    fin_cases d <;> norm_num [rootDisplay, pointDisplay, evenCoin, Fin.ext_iff]
  · simp only [rootDisplay, ha, if_false]
    ring

theorem shannonStage_root (π : ValidCausalPolicy Action Observation) :
    shannonStage π 0 = inspectionProbability π.1 := by
  rw [shannonStage_eq]
  have he (a : Action) : ent (prodLaw (if a = inspect then evenCoin else pointDisplay 0)
      (pointMonitor 0)) / Real.log 2 = if a = inspect then 1 else 0 := by
    by_cases ha : a = inspect
    · simp only [ha, if_true]
      rw [ent_prodLaw evenCoin_valid.2 (pointMonitor_valid 0).2, ent_evenCoin,
        ent_pointMonitor, add_zero, div_self (ne_of_gt log_two_pos)]
    · simp only [ha, if_false]
      rw [ent_prodLaw (pointDisplay_valid 0).2 (pointMonitor_valid 0).2,
        ent_pointDisplay, ent_pointMonitor]
      simp
  simp [predictive_root, he, mass_zero, inspectionProbability]

theorem squareStage_root (π : ValidCausalPolicy Action Observation) :
    squareStage π 0 = -1 + inspectionProbability π.1 / 2 := by
  rw [squareStage_eq]
  have he (a : Action) : -(∑ o, prodLaw (if a = inspect then evenCoin else pointDisplay 0)
      (pointMonitor 0) o ^ 2) = -1 + (if a = inspect then 1/2 else 0) := by
    by_cases ha : a = inspect
    · simp only [ha, if_true]
      rw [sum_sq_prodLaw, sum_sq_evenCoin, sum_sq_pointMonitor]
      norm_num
    · simp only [ha, if_false]
      rw [sum_sq_prodLaw, sum_sq_pointDisplay, sum_sq_pointMonitor]
      norm_num
  simp only [predictive_root, he, mul_add, sum_add_distrib, ← sum_mul, (π.2 _).2, one_mul]
  simp [mass_zero, inspectionProbability, mul_ite, div_eq_mul_inv]

/-! ## The forecast after startup factorizes -/

/-- Joint prior mass of a record of length `k+1` and the next monitor bit. -/
def monitorJoint (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1))
    (m : Monitor) : ℝ :=
  ∫ θ, record π (k+1) θ h * pointMonitor (monitorLabel θ k) m ∂prior

theorem joint_tick (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1))
    (a : Action) (o : Observation) :
    joint π (k+1) h a o = panelDisplay (List.ofFn h) a o.1 * monitorJoint π k h o.2 := by
  unfold joint monitorJoint
  rw [← integral_const_mul]
  congr 1
  funext θ
  rw [response_tick θ _ a o (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel]
  ring

/-- Bayes mass of a pulse at tick `k`: only the world `some k` reports it. -/
theorem monitorJoint_one (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1)) :
    monitorJoint π k h 1 = alarmMass k * record π (k+1) (some k) h := by
  have hx : (fun θ => record π (k+1) θ h * pointMonitor (monitorLabel θ k) 1) =
      ({some k} : Set World).indicator (fun _ => record π (k+1) (some k) h) := by
    funext θ
    by_cases hθ : θ = some k
    · subst hθ; simp [pointMonitor, monitorLabel]
    · simp [pointMonitor, monitorLabel, hθ]
  rw [monitorJoint, hx, integral_indicator_const _ (measurableSet_singleton _)]
  simp only [smul_eq_mul, waitingQueryGeometricPrior_some]
  rfl

theorem monitorJoint_sum (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1)) :
    monitorJoint π k h 0 + monitorJoint π k h 1 = mass π (k+1) h := by
  have hs := joint_sum π (k+1) h inspect
  rw [Fintype.sum_prod_type] at hs
  simp only [joint_tick] at hs
  rw [← hs]
  simp_rw [← mul_sum]
  rw [← sum_mul, (panelDisplay_valid _ inspect).2, one_mul, Fin.sum_univ_two]

/-- The exact Bayes posterior probability that the alarm pulses at tick `k`, after a
retained record of length `k+1`. -/
def pulseForecast (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1)) : ℝ :=
  alarmMass k * record π (k+1) (some k) h / mass π (k+1) h

/-- **Factorization.** After startup, the Bayes forecast of the next raw observation is
the known display law times the Bernoulli forecast of the alarm tick. -/
theorem predictive_tick (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1))
    (hm : mass π (k+1) h ≠ 0) (a : Action) :
    predictive π (k+1) h a =
      prodLaw (panelDisplay (List.ofFn h) a) (bitLaw (pulseForecast π k h)) := by
  funext o
  rcases o with ⟨d, m⟩
  simp only [predictive, hm, if_false, joint_tick, prodLaw, bitLaw, pulseForecast]
  have hs := monitorJoint_sum π k h
  rw [monitorJoint_one] at hs
  fin_cases m
  · simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, if_false]
    have h0 : monitorJoint π k h 0 = mass π (k+1) h - alarmMass k * record π (k+1) (some k) h := by
      linarith
    rw [h0]
    field_simp
  · simp only [Fin.mk_one, Fin.isValue, if_true]
    rw [monitorJoint_one]
    ring

/-- On a record compatible with a pulse at tick `k`, the pulse forecast is `1/2` after
inspection and `p_k = a_k / S_k` after play; otherwise it is zero. -/
theorem pulseForecast_eq (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1)) :
    pulseForecast π k h =
      if record π (k+1) (some k) h = 0 then 0
      else if (h 0).1 = inspect then 1/2 else alarmMass k / silentMass k := by
  by_cases hr : record π (k+1) (some k) h = 0
  · simp [pulseForecast, hr]
  · rw [if_neg hr, pulseForecast, monitor_predictive_mass π k h hr]
    have ha := ne_of_gt (alarmMass_pos k)
    have hs := ne_of_gt (silentMass_pos k)
    split
    · field_simp
    · field_simp

/-- Away from null records, `pulseForecast` is the actual countable-prior posterior
probability of the world `some k` given the full retained record. -/
theorem pulseForecast_eq_posterior (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : Trace (k+1)) (hm : mass π (k+1) h ≠ 0) :
    pulseForecast π k h = (priorPosteriorMeasure prior (record π (k+1)) h).real {some k} := by
  rw [measureReal_def, priorPosteriorMeasure, withDensity_apply _ (measurableSet_singleton _),
    lintegral_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (priorSignalDensity_nonneg prior _ (record_valid π (k+1)) h (some k)),
    ← measureReal_def, waitingQueryGeometricPrior_some]
  have hm' : priorSignalMass prior (record π (k+1)) h ≠ 0 := hm
  simp only [priorSignalDensity, if_neg hm', pulseForecast, mass, alarmMass]
  ring

/-- Bayes weighting cancels the known startup and panel likelihood, including at
null records. -/
theorem monitor_weighted (fI fP : ℝ → ℝ) (hI : fI 0 = 0) (hP : fP 0 = 0)
    (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1)) :
    mass π (k+1) h * (if (h 0).1 = inspect then fI (pulseForecast π k h)
      else fP (pulseForecast π k h)) =
    record π (k+1) (some k) h * (if (h 0).1 = inspect then 2 * alarmMass k * fI (1/2)
      else silentMass k * fP (alarmMass k / silentMass k)) := by
  have hq := pulseForecast_eq π k h
  by_cases hr : record π (k+1) (some k) h = 0
  · rw [if_pos hr] at hq
    rw [hr, zero_mul, hq, hI, hP, ite_self, mul_zero]
  · rw [if_neg hr] at hq
    rw [monitor_predictive_mass π k h hr, hq]
    split <;> ring

/-- The posterior-weighted monitor payoff of every policy is the root mixture. -/
theorem monitorSum_eq (fI fP : ℝ → ℝ) (hI : fI 0 = 0) (hP : fP 0 = 0)
    (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    ∑ h : Trace (k+1), mass π (k+1) h * (if (h 0).1 = inspect then fI (pulseForecast π k h)
      else fP (pulseForecast π k h)) =
    inspectionProbability π.1 * (2 * alarmMass k * fI (1/2)) +
      (1 - inspectionProbability π.1) * (silentMass k * fP (alarmMass k / silentMass k)) := by
  simp only [monitor_weighted fI fP hI hP]
  exact record_inspection_sum π (some k) k _ _

/-! ## Expected stage utilities after startup -/

theorem shannon_history (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1)) :
    mass π (k+1) h * ∑ a, π.1 (List.ofFn h) a * (ent (predictive π (k+1) h a) / Real.log 2) =
      mass π (k+1) h * (if (h 0).1 = inspect then 0 else 1) +
      mass π (k+1) h * (if (h 0).1 = inspect then binEntropyBits (pulseForecast π k h)
        else binEntropyBits (pulseForecast π k h)) := by
  by_cases hm : mass π (k+1) h = 0
  · simp [hm]
  · have he (a : Action) : ent (predictive π (k+1) h a) / Real.log 2 =
        (if (h 0).1 = inspect then 0 else 1) + binEntropyBits (pulseForecast π k h) := by
      rw [predictive_tick π k h hm a, ent_prodLaw (panelDisplay_valid _ a).2 (sum_bitLaw _),
        ent_panelDisplay, ent_bitLaw, add_div, binEntropyBits]
      congr 1
      split
      · simp
      · exact div_self (ne_of_gt log_two_pos)
    simp only [he, ← sum_mul, (π.2 _).2, one_mul, ite_self]
    ring

theorem square_history (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (k+1)) :
    mass π (k+1) h * ∑ a, π.1 (List.ofFn h) a * (-∑ o, predictive π (k+1) h a o ^ 2) =
      mass π (k+1) h * (if (h 0).1 = inspect then -1 else -1/2) +
      mass π (k+1) h * (if (h 0).1 = inspect
        then 2 * pulseForecast π k h * (1 - pulseForecast π k h)
        else pulseForecast π k h * (1 - pulseForecast π k h)) := by
  by_cases hm : mass π (k+1) h = 0
  · simp [hm]
  · have he (a : Action) : -∑ o, predictive π (k+1) h a o ^ 2 =
        (if (h 0).1 = inspect then -1 else -1/2) +
        (if (h 0).1 = inspect then 2 * pulseForecast π k h * (1 - pulseForecast π k h)
          else pulseForecast π k h * (1 - pulseForecast π k h)) := by
      rw [predictive_tick π k h hm a, sum_sq_prodLaw, sum_sq_panelDisplay, sum_sq_bitLaw]
      split <;> ring
    simp only [he, ← sum_mul, (π.2 _).2, one_mul]
    ring

/-- Expected Shannon utility at alarm tick `k` (history length `k+1`), in bits. -/
theorem shannonStage_tick (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    shannonStage π (k+1) = inspectionProbability π.1 * (2 * alarmMass k) +
      (1 - inspectionProbability π.1) *
        (1 + silentMass k * binEntropyBits (alarmMass k / silentMass k)) := by
  rw [shannonStage_eq]
  simp only [shannon_history, sum_add_distrib]
  rw [inspectionMass_sum, monitorSum_eq _ _ binEntropyBits_zero binEntropyBits_zero,
    binEntropyBits_half]
  ring

/-- Expected Square utility at alarm tick `k` (history length `k+1`). -/
theorem squareStage_tick (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    squareStage π (k+1) = inspectionProbability π.1 * (-1 + alarmMass k) +
      (1 - inspectionProbability π.1) *
        (-1/2 + alarmMass k * (1 - alarmMass k / silentMass k)) := by
  rw [squareStage_eq]
  simp only [square_history, sum_add_distrib]
  have hm := monitorSum_eq (fun q => 2 * q * (1 - q)) (fun q => q * (1 - q))
    (by simp) (by simp) π k
  rw [inspectionMass_sum, hm]
  have hs := ne_of_gt (silentMass_pos k)
  field_simp
  ring

/-! ## The inspection and play columns -/

/-- Shannon column after inspection: `1` at startup and `T_k = 2 a_k` at tick `k`. -/
def shannonInspectValue : ℕ → ℝ
  | 0 => 1
  | k+1 => 2 * alarmMass k

/-- Shannon column after play: `0` at startup and `1 + S_k h₂(p_k)` at tick `k`. -/
def shannonPlayValue : ℕ → ℝ
  | 0 => 0
  | k+1 => 1 + silentMass k * binEntropyBits (alarmMass k / silentMass k)

/-- Square column after inspection: `-1/2` at startup and `-1 + a_k` at tick `k`. -/
def squareInspectValue : ℕ → ℝ
  | 0 => -1/2
  | k+1 => -1 + alarmMass k

/-- Square column after play: `-1` at startup and `-1/2 + a_k (1 - p_k)` at tick `k`. -/
def squarePlayValue : ℕ → ℝ
  | 0 => -1
  | k+1 => -1/2 + alarmMass k * (1 - alarmMass k / silentMass k)

/-- Every policy's expected Shannon stage is the root mixture of the two columns,
for every adaptive randomized continuation. -/
theorem shannonStage_mixture (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    shannonStage π t = inspectionProbability π.1 * shannonInspectValue t +
      (1 - inspectionProbability π.1) * shannonPlayValue t := by
  cases t with
  | zero => rw [shannonStage_root, shannonInspectValue, shannonPlayValue]; ring
  | succ k => rw [shannonStage_tick, shannonInspectValue, shannonPlayValue]

/-- Every policy's expected Square stage is the root mixture of the two columns,
for every adaptive randomized continuation. -/
theorem squareStage_mixture (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    squareStage π t = inspectionProbability π.1 * squareInspectValue t +
      (1 - inspectionProbability π.1) * squarePlayValue t := by
  cases t with
  | zero => rw [squareStage_root, squareInspectValue, squarePlayValue]; ring
  | succ k => rw [squareStage_tick, squareInspectValue, squarePlayValue]

theorem hazard_nonneg (k : ℕ) : 0 ≤ alarmMass k / silentMass k := (hazard_bounds k).1

theorem hazard_le_one (k : ℕ) : alarmMass k / silentMass k ≤ 1 :=
  (hazard_bounds k).2.trans (by norm_num)

/-- Concavity along the left half of binary entropy, in nats. -/
theorem binary_entropy_chord (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    2*p*Real.log 2 ≤ Real.binEntropy p := by
  have hc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1/2:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show 0 ≤ 1-2*p by linarith) (show 0 ≤ 2*p by positivity)
    (show 1-2*p+2*p=1 by ring)
  have hh : Real.binEntropy (1/2:ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  have hx : (2*p)*(1/2:ℝ)=p := by ring
  simpa only [smul_eq_mul, Real.binEntropy_zero, hh, mul_zero, zero_add, hx] using hc

/-- PLAY earns at least one extra bit at every post-startup tick. -/
theorem shannon_play_sub_inspect_tick (k : ℕ) :
    1 ≤ shannonPlayValue (k+1) - shannonInspectValue (k+1) := by
  have hp := hazard_bounds k
  have hc := binary_entropy_chord _ hp.1 (by linarith [hp.2])
  have hh := mul_le_mul_of_nonneg_left hc (silentMass_pos k).le
  have hs := ne_of_gt (silentMass_pos k)
  have he : silentMass k * (2*(alarmMass k/silentMass k)*Real.log 2) =
      2*alarmMass k*Real.log 2 := by field_simp
  rw [he] at hh
  have hlog := log_two_pos
  have hdiv : 2 * alarmMass k ≤
      silentMass k * Real.binEntropy (alarmMass k / silentMass k) / Real.log 2 :=
    (le_div_iff₀ hlog).2 hh
  simp only [shannonPlayValue, shannonInspectValue, binEntropyBits]
  rw [← mul_div_assoc]
  linarith

/-- Square's play minus inspect gap at tick `k` is `1/2 - a_k p_k > 0`. -/
theorem square_play_sub_inspect_tick (k : ℕ) :
    squarePlayValue (k+1) - squareInspectValue (k+1) =
      1/2 - alarmMass k * (alarmMass k / silentMass k) := by
  simp only [squarePlayValue, squareInspectValue]
  ring

/-- A uniform lower bound for the literal Square stage advantage. -/
theorem square_play_sub_inspect_tick_lower (k : ℕ) :
    7/16 ≤ squarePlayValue (k+1) - squareInspectValue (k+1) := by
  rw [square_play_sub_inspect_tick]
  have ha := alarmMass_le_quarter k
  have hp := hazard_bounds k
  nlinarith [mul_le_mul ha hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 1/4)]

theorem square_play_sub_inspect_tick_pos (k : ℕ) :
    0 < squarePlayValue (k+1) - squareInspectValue (k+1) := by
  rw [square_play_sub_inspect_tick]
  have ha := alarmMass_le_quarter k
  have ha0 := (alarmMass_pos k).le
  have hp := hazard_bounds k
  nlinarith [mul_le_mul ha hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 1/4)]

/-- After startup, PLAY improves the Shannon stage. -/
theorem shannonInspectValue_le_play (k : ℕ) :
    shannonInspectValue (k+1) ≤ shannonPlayValue (k+1) := by
  linarith [shannon_play_sub_inspect_tick k]

/-- After startup, PLAY improves the Square stage. -/
theorem squareInspectValue_le_play (k : ℕ) :
    squareInspectValue (k+1) ≤ squarePlayValue (k+1) := by
  linarith [square_play_sub_inspect_tick_pos k]

end IdExp.PairedAlarm.Predictive
