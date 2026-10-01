import Formal.AlarmPanelPredictiveStages
import Formal.AlarmPanelPosteriorDiscount
import Formal.AlarmPanelEmpowermentAverage

/-! Proper-discount Shannon and literal per-step Square select the deficient
startup on the unchanged alarm, for every randomized history policy. -/
noncomputable section
namespace IdExp.AlarmPanelPredictive
open AlarmPanel AlarmPanelBayes AlarmPanelVariance MeasureTheory Finset Set
set_option maxRecDepth 10000
set_option maxHeartbeats 600000

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

theorem log_monitor_comparison (k : ℕ) :
    2*alarmMass k*Real.log 2 ≤ silentMass k*Real.binEntropy (alarmMass k/silentMass k) := by
  have hp := hazard_bounds k
  have hc := binary_entropy_chord _ hp.1 (by linarith [hp.2])
  have hh := mul_le_mul_of_nonneg_left hc (silentMass_pos k).le
  have hs := ne_of_gt (silentMass_pos k)
  have he : silentMass k * (2*(alarmMass k/silentMass k)*Real.log 2) =
      2*alarmMass k*Real.log 2 := by field_simp
  simpa only [he] using hh

theorem logStage_le_play (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    logStage π t ≤ logStage noveltyPolicy t := by
  have hs := inspectionProbability_nonneg π.1 π.2
  have hz : inspectionProbability noveltyPolicy.1 = 0 := noveltyPolicy_root
  by_cases ht : t=0
  · subst t; rw [logStage_root, logStage_root]
  · by_cases ho : t%2=1
    · have he : t=2*(t/2)+1 := by omega
      rw [he, logStage_panel, logStage_panel, hz]
      have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    · have he : t=2*((t-2)/2)+2 := by omega
      rw [he, logStage_monitor, logStage_monitor, hz]
      nlinarith [mul_nonneg hs (sub_nonneg.mpr (log_monitor_comparison ((t-2)/2)))]

theorem squaredStage_le_play (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    squaredStage π t ≤ squaredStage noveltyPolicy t := by
  have hs := inspectionProbability_nonneg π.1 π.2
  have hz : inspectionProbability noveltyPolicy.1 = 0 := noveltyPolicy_root
  by_cases ht : t=0
  · subst t; rw [squaredStage_root, squaredStage_root]
  · by_cases ho : t%2=1
    · have he : t=2*(t/2)+1 := by omega
      rw [he, squaredStage_panel, squaredStage_panel, hz]
      linarith
    · have he : t=2*((t-2)/2)+2 := by omega
      rw [he, squaredStage_monitor, squaredStage_monitor, hz]
      have ha := alarmMass_pos ((t-2)/2)
      have hb := (playTerm_bounds ((t-2)/2)).1
      nlinarith [mul_nonneg hs (show 0 ≤ playTerm ((t-2)/2)-alarmMass ((t-2)/2) by linarith)]

theorem logStage_eq_of_root_zero (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1=0) (t : ℕ) : logStage π t = logStage noveltyPolicy t := by
  have hz : inspectionProbability noveltyPolicy.1=0 := noveltyPolicy_root
  by_cases ht : t=0
  · subst t; rw [logStage_root, logStage_root]
  · by_cases ho : t%2=1
    · have he : t=2*(t/2)+1 := by omega
      rw [he, logStage_panel, logStage_panel, hs, hz]
    · have he : t=2*((t-2)/2)+2 := by omega
      rw [he, logStage_monitor, logStage_monitor, hs, hz]

theorem squaredStage_eq_of_root_zero (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1=0) (t : ℕ) : squaredStage π t = squaredStage noveltyPolicy t := by
  have hz : inspectionProbability noveltyPolicy.1=0 := noveltyPolicy_root
  by_cases ht : t=0
  · subst t; rw [squaredStage_root, squaredStage_root]
  · by_cases ho : t%2=1
    · have he : t=2*(t/2)+1 := by omega
      rw [he, squaredStage_panel, squaredStage_panel, hs, hz]
    · have he : t=2*((t-2)/2)+2 := by omega
      rw [he, squaredStage_monitor, squaredStage_monitor, hs, hz]

theorem logStage_le_bound (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    logStage π t ≤ Real.log 4 := by
  rw [logStage_eq]
  have hb (h : Trace t) (a : Action) : ent (predictive π t h a) ≤ Real.log 4 := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using ent_le_log_card _ (predictive_valid π t h a)
  calc
    _ ≤ ∑ h : Trace t, mass π t h * ∑ a, π.1 (List.ofFn h) a * Real.log 4 := by
      apply sum_le_sum; intro h _
      apply mul_le_mul_of_nonneg_left _ ((mass_valid π t).1 h)
      apply sum_le_sum; intro a _
      exact mul_le_mul_of_nonneg_left (hb h a) ((π.2 _).1 a)
    _ = _ := by simp only [← sum_mul, (π.2 _).2, one_mul, (mass_valid π t).2]

def shannonDiscounted (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, γ^t * logStage π t

def quadraticDiscounted (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, γ^t * squaredStage π t

/-- Literal source reward −q(observation), with the same chronological discount. -/
def squareDiscounted (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, γ^t * squareStage π t

theorem shannon_summable (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) : Summable (fun t => γ^t*logStage π t) :=
  PrefixDiscount.weighted_summable γ (Real.log 4) hγ0 hγ1 _
    (fun t => ⟨logStage_nonneg π t,logStage_le_bound π t⟩)

theorem quadratic_summable (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) : Summable (fun t => γ^t*squaredStage π t) :=
  PrefixDiscount.weighted_summable γ (Real.log 4) hγ0 hγ1 _
    (fun t => ⟨squaredStage_nonneg π t,(squaredStage_le_logStage π t).trans (logStage_le_bound π t)⟩)

theorem square_summable (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) : Summable (fun t => γ^t*squareStage π t) := by
  simp_rw [squareStage_eq, mul_sub, mul_one]
  exact (quadratic_summable γ hγ0 hγ1 π).sub (summable_geometric_of_lt_one hγ0 hγ1)

theorem squareDiscounted_eq (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) :
    squareDiscounted γ π = quadraticDiscounted γ π - 1/(1-γ) := by
  simp only [squareDiscounted, squareStage_eq, mul_sub, mul_one]
  rw [(quadratic_summable γ hγ0 hγ1 π).tsum_sub (summable_geometric_of_lt_one hγ0 hγ1),
    tsum_geometric_of_lt_one hγ0 hγ1]
  simp only [quadraticDiscounted, one_div]

theorem shannonDiscounted_le_play (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) : shannonDiscounted γ π ≤ shannonDiscounted γ noveltyPolicy :=
  Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (logStage_le_play π t) (pow_nonneg hγ0 _))
    (shannon_summable γ hγ0 hγ1 π) (shannon_summable γ hγ0 hγ1 noveltyPolicy)

theorem quadraticDiscounted_le_play (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) : quadraticDiscounted γ π ≤ quadraticDiscounted γ noveltyPolicy :=
  Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (squaredStage_le_play π t) (pow_nonneg hγ0 _))
    (quadratic_summable γ hγ0 hγ1 π) (quadratic_summable γ hγ0 hγ1 noveltyPolicy)

theorem shannonDiscounted_strict (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) (hs : 0 < inspectionProbability π.1) :
    shannonDiscounted γ π < shannonDiscounted γ noveltyPolicy := by
  apply Summable.tsum_lt_tsum
    (fun t => mul_le_mul_of_nonneg_left (logStage_le_play π t) (pow_nonneg hγ0.le _)) (i:=1)
  · apply mul_lt_mul_of_pos_left _ (by simpa)
    have he : (1:ℕ)=2*0+1 := by omega
    rw [he, logStage_panel, logStage_panel]
    have hz : inspectionProbability noveltyPolicy.1=0 := noveltyPolicy_root
    rw [hz]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  · exact shannon_summable γ hγ0.le hγ1 π
  · exact shannon_summable γ hγ0.le hγ1 noveltyPolicy

theorem quadraticDiscounted_strict (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) (hs : 0 < inspectionProbability π.1) :
    quadraticDiscounted γ π < quadraticDiscounted γ noveltyPolicy := by
  apply Summable.tsum_lt_tsum
    (fun t => mul_le_mul_of_nonneg_left (squaredStage_le_play π t) (pow_nonneg hγ0.le _)) (i:=1)
  · apply mul_lt_mul_of_pos_left _ (by simpa)
    have he : (1:ℕ)=2*0+1 := by omega
    rw [he, squaredStage_panel, squaredStage_panel]
    have hz : inspectionProbability noveltyPolicy.1=0 := noveltyPolicy_root
    rw [hz]
    linarith
  · exact quadratic_summable γ hγ0.le hγ1 π
  · exact quadratic_summable γ hγ0.le hγ1 noveltyPolicy

theorem shannonDiscounted_maximizer_iff (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, shannonDiscounted γ ρ ≤ shannonDiscounted γ π) ↔ inspectionProbability π.1=0 := by
  constructor
  · intro h
    by_contra hs
    have hpos := lt_of_le_of_ne (inspectionProbability_nonneg π.1 π.2) (Ne.symm hs)
    exact (not_lt_of_ge (h noveltyPolicy)) (shannonDiscounted_strict γ hγ0 hγ1 π hpos)
  · intro hs ρ
    have he : shannonDiscounted γ π = shannonDiscounted γ noveltyPolicy := by
      unfold shannonDiscounted
      simp_rw [logStage_eq_of_root_zero π hs]
    rw [he]
    exact shannonDiscounted_le_play γ hγ0.le hγ1 ρ

theorem squareDiscounted_maximizer_iff (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ<1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, squareDiscounted γ ρ ≤ squareDiscounted γ π) ↔ inspectionProbability π.1=0 := by
  simp only [squareDiscounted_eq γ hγ0.le hγ1, sub_le_sub_iff_right]
  constructor
  · intro h
    by_contra hs
    have hpos := lt_of_le_of_ne (inspectionProbability_nonneg π.1 π.2) (Ne.symm hs)
    exact (not_lt_of_ge (h noveltyPolicy)) (quadraticDiscounted_strict γ hγ0 hγ1 π hpos)
  · intro hs ρ
    have he : quadraticDiscounted γ π = quadraticDiscounted γ noveltyPolicy := by
      unfold quadraticDiscounted
      simp_rw [squaredStage_eq_of_root_zero π hs]
    rw [he]
    exact quadraticDiscounted_le_play γ hγ0.le hγ1 ρ

/-- Both exact source objectives have attained global optima with the same native loss. -/
theorem all_discounted_optima_failure (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ<1) :
    (∃ π, (∀ ρ, shannonDiscounted γ ρ ≤ shannonDiscounted γ π) ∧
      (∀ ρ, squareDiscounted γ ρ ≤ squareDiscounted γ π)) ∧
    ∀ π : ValidCausalPolicy Action Observation,
      ((∀ ρ, shannonDiscounted γ ρ ≤ shannonDiscounted γ π) ∨
        (∀ ρ, squareDiscounted γ ρ ≤ squareDiscounted γ π)) →
      inspectionProbability π.1=0 ∧
      (∀ n, finiteDeficiency (experiment π.1 (n+1)) (experiment inspectPolicy 1)=1/2) ∧
      AlarmPanel.Control.eventualInspectionDeficiency π=1/2 ∧
      CausalFinitaryDominates response ⟨inspectPolicy,inspectPolicy_valid⟩ π ∧
      ¬ CausalFinitaryDominates response π ⟨inspectPolicy,inspectPolicy_valid⟩ := by
  have hz : inspectionProbability noveltyPolicy.1=0 := noveltyPolicy_root
  refine ⟨⟨noveltyPolicy, (shannonDiscounted_maximizer_iff γ hγ0 hγ1 _).2 hz,
    (squareDiscounted_maximizer_iff γ hγ0 hγ1 _).2 hz⟩, ?_⟩
  intro π hopt
  have hs : inspectionProbability π.1=0 := hopt.elim
    ((shannonDiscounted_maximizer_iff γ hγ0 hγ1 π).1)
    ((squareDiscounted_maximizer_iff γ hγ0 hγ1 π).1)
  have hfail := AlarmPanel.Control.longRunEmpowermentAverage_all_optima_failure.2 π
    ((AlarmPanel.Control.longRunEmpowermentAverage_maximizer_iff π).2 hs)
  exact ⟨hs, fun n => hfail.1 (n+1) (by omega), hfail.2⟩

end IdExp.AlarmPanelPredictive
