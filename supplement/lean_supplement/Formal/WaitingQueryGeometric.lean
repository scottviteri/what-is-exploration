import Formal.WaitingQueryReadiness
import Mathlib.Probability.Distributions.Geometric

/-!
# Exact geometric-prior regret for the countable waiting experiment

The prior is a pushforward of a geometric probability law: index zero is
infinity, and index `k+1` is finite world `k`.  Thus infinity has mass one
half and finite world `k` has mass `2^(-(k+2))`.  The final theorem computes
the optimized value over every randomized decision rule, not just the
performance of the displayed decoder.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- The geometric index zero denotes infinity. -/
def waitingQueryGeometricWorld : ℕ → WaitingQueryWorld
  | 0 => none
  | n + 1 => some n

/-- Fair geometric law, with success parameter one half. -/
noncomputable def waitingQueryGeometricParameter : unitInterval := ⟨1 / 2, by norm_num⟩

theorem waitingQueryGeometricParameter_ne_zero : waitingQueryGeometricParameter ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [waitingQueryGeometricParameter] at this

/-- The full countable prior used in the separation example. -/
noncomputable def waitingQueryGeometricPrior : Measure WaitingQueryWorld :=
  (geometricMeasure waitingQueryGeometricParameter).map waitingQueryGeometricWorld

instance waitingQueryGeometricPrior_isProbability :
    IsProbabilityMeasure waitingQueryGeometricPrior :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem waitingQueryGeometricPrior_none : waitingQueryGeometricPrior.real {none} = 1 / 2 := by
  have hpre : waitingQueryGeometricWorld ⁻¹' ({none} : Set WaitingQueryWorld) = {0} := by
    ext n
    cases n <;> simp [waitingQueryGeometricWorld]
  rw [measureReal_def, waitingQueryGeometricPrior,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpre]
  change (geometricMeasure waitingQueryGeometricParameter).real {0} = _
  rw [geometricMeasure_real_singleton waitingQueryGeometricParameter_ne_zero]
  norm_num [waitingQueryGeometricParameter]

theorem waitingQueryGeometricPrior_some (k : ℕ) :
    waitingQueryGeometricPrior.real {some k} = (1 / 2 : ℝ) ^ (k + 2) := by
  have hpre : waitingQueryGeometricWorld ⁻¹' ({some k} : Set WaitingQueryWorld) = {k + 1} := by
    ext n
    cases n <;> simp [waitingQueryGeometricWorld]
  rw [measureReal_def, waitingQueryGeometricPrior,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpre]
  change (geometricMeasure waitingQueryGeometricParameter).real {k + 1} = _
  rw [geometricMeasure_real_singleton waitingQueryGeometricParameter_ne_zero]
  norm_num [waitingQueryGeometricParameter, pow_succ]

/-- Exact mass of a geometric tail, proved from its finite prefix mass. -/
theorem waitingQueryGeometric_tail_nat (t : ℕ) :
    (geometricMeasure waitingQueryGeometricParameter).real {n | t ≤ n} = (1 / 2 : ℝ) ^ t := by
  have hprefix : (geometricMeasure waitingQueryGeometricParameter).real
      (Finset.range t : Set ℕ) = 1 - (1 / 2 : ℝ) ^ t := by
    rw [← sum_measureReal_singleton]
    simp_rw [geometricMeasure_real_singleton waitingQueryGeometricParameter_ne_zero]
    norm_num only [waitingQueryGeometricParameter, sub_half]
    rw [← Finset.sum_mul, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    ring
  have heq : {n : ℕ | t ≤ n} = (Finset.range t : Set ℕ)ᶜ := by
    ext n
    simp
  rw [heq, measureReal_compl (Finset.measurableSet _), hprefix]
  simp

/-- The delayed finite-world mass is exactly `2^(-t)` from time one. -/
theorem waitingQueryGeometric_tail (t : ℕ) (ht : 1 ≤ t) :
    waitingQueryTail waitingQueryGeometricPrior t = (1 / 2 : ℝ) ^ t := by
  have hpre : waitingQueryGeometricWorld ⁻¹' waitingQueryTailSet t = {n | t ≤ n} := by
    ext n
    cases n with
    | zero => simp [waitingQueryGeometricWorld, waitingQueryTailSet]; omega
    | succ k => simp [waitingQueryGeometricWorld, waitingQueryTailSet]; omega
  rw [waitingQueryTail, measureReal_def, waitingQueryGeometricPrior,
    Measure.map_apply (measurable_of_countable _) (show MeasurableSet (waitingQueryTailSet t) from trivial), hpre]
  exact waitingQueryGeometric_tail_nat t

/-- Binary reward for deciding whether the world is finite. -/
def waitingQueryBinaryUtility (θ : WaitingQueryWorld) (d : Bool) : ℝ :=
  if d = θ.isSome then 1 else 0

theorem waitingQueryBinaryUtility_unit (θ : WaitingQueryWorld) (d : Bool) :
    waitingQueryBinaryUtility θ d ∈ Icc (0 : ℝ) 1 := by
  unfold waitingQueryBinaryUtility
  split <;> norm_num

/-- The actual immediate-query bit, as a measurable target kernel. -/
noncomputable def waitingQueryBinaryTarget : FiniteMarkovKernel WaitingQueryWorld Bool :=
  ⟨Kernel.deterministic Option.isSome (measurable_of_countable _), inferInstance⟩

/-- The binary target is the first observation of the actual native root
query. This connects the value calculation to canonical causal execution. -/
theorem waitingQueryBinaryTarget_native (θ : WaitingQueryWorld) :
    (kernelExperiment waitingQueryBinaryTarget θ : Measure Bool) =
      (kernelExperiment (waitingQueryNativeKernel waitingQueryRootPlan) θ :
        Measure (CausalObservationTrace Bool 1)).map (fun y => y 0) := by
  change Measure.dirac θ.isSome =
    (Measure.dirac (detPlanObs 1 waitingQueryRootPlan.toCausalPlan (waitingQueryOutput θ))).map
      (fun y => y 0)
  rw [Measure.map_dirac, waitingQueryRootPlan_observation]

/-- Evaluating any rule on a deterministic acquired record. -/
theorem waitingQuery_binary_rulePayoff (t : ℕ)
    (r : FiniteMarkovKernel (CausalFiniteTrace Bool Bool t) Bool) (θ : WaitingQueryWorld) :
    bayesRulePayoff (waitingQueryRecordKernel t) r waitingQueryBinaryUtility θ =
      (r.toKernel (waitingQueryTrace t θ)).real {θ.isSome} := by
  unfold bayesRulePayoff
  have heq : (finiteMarkovDecode r (kernelExperiment (waitingQueryRecordKernel t) θ) : Measure Bool) =
      r.toKernel (waitingQueryTrace t θ) := by
    change r.toKernel ∘ₘ Measure.dirac (waitingQueryTrace t θ) = _
    exact Measure.dirac_bind r.toKernel.measurable _
  rw [heq]
  simp [waitingQueryBinaryUtility, Finset.sum_ite_eq']

/-- The query target has value one for its own binary question under every prior. -/
theorem waitingQueryBinaryTarget_value (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α] :
    bayesExperimentValue α waitingQueryBinaryTarget waitingQueryBinaryUtility = 1 := by
  have hum d : Measurable (fun θ => waitingQueryBinaryUtility θ d) := measurable_of_countable _
  apply le_antisymm (bayesExperimentValue_mem_unitInterval α waitingQueryBinaryTarget
    waitingQueryBinaryUtility hum waitingQueryBinaryUtility_unit).2
  let r : FiniteMarkovKernel Bool Bool :=
    ⟨Kernel.deterministic id measurable_id, inferInstance⟩
  have hv : bayesRuleValue α waitingQueryBinaryTarget r waitingQueryBinaryUtility = 1 := by
    have hp θ : bayesRulePayoff waitingQueryBinaryTarget r waitingQueryBinaryUtility θ = 1 := by
      have heq : (finiteMarkovDecode r (kernelExperiment waitingQueryBinaryTarget θ) : Measure Bool) =
          Measure.dirac θ.isSome := by
        change (Kernel.deterministic id measurable_id) ∘ₘ Measure.dirac θ.isSome = _
        rw [Measure.dirac_bind (Kernel.deterministic id measurable_id).measurable]
        rfl
      unfold bayesRulePayoff
      rw [heq]
      cases hθ : θ.isSome <;> simp [waitingQueryBinaryUtility, hθ, measureReal_def]
    simp [bayesRuleValue, hp]
  rw [← hv]
  exact le_csSup (bayesValue_range_bddAbove α waitingQueryBinaryTarget waitingQueryBinaryUtility hum
    waitingQueryBinaryUtility_unit) (mem_range_self r)

/-- Exact optimized binary value whenever infinity is at least as likely
as all undetected finite worlds together. This condition explains why the
optimal blank-record decision is infinity. -/
theorem waitingQuery_binary_value_eq_one_sub_tail
    (α : Measure WaitingQueryWorld) [IsProbabilityMeasure α] (t : ℕ)
    (hdom : waitingQueryTail α t ≤ α.real {none}) :
    bayesExperimentValue α (waitingQueryRecordKernel t) waitingQueryBinaryUtility =
      1 - waitingQueryTail α t := by
  have hum d : Measurable (fun θ => waitingQueryBinaryUtility θ d) := measurable_of_countable _
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨r, rfl⟩
    have := r.isMarkov
    let b : ℝ := (r.toKernel (waitingQueryTrace t none)).real {true}
    have hb : 0 ≤ b := measureReal_nonneg
    have hnorm : (r.toKernel (waitingQueryTrace t none)).real {false} + b = 1 := by
      have h := (isDist_measureReal_singletons (r.toKernel (waitingQueryTrace t none))).2
      simpa [b, add_comm] using h
    let bound : WaitingQueryWorld → ℝ := fun θ => 1 -
      (waitingQueryTailSet t).indicator (fun _ => 1 - b) θ -
      ({none} : Set WaitingQueryWorld).indicator (fun _ => b) θ
    have hpoint θ : bayesRulePayoff (waitingQueryRecordKernel t) r waitingQueryBinaryUtility θ ≤ bound θ := by
      rw [waitingQuery_binary_rulePayoff]
      cases θ with
      | none =>
        have hnot : none ∉ waitingQueryTailSet t := by simp [waitingQueryTailSet]
        simp only [bound, Set.indicator_of_notMem hnot,
          Set.indicator_of_mem (show none ∈ ({none} : Set WaitingQueryWorld) from rfl),
          Option.isSome_none, sub_zero]
        linarith
      | some k =>
        by_cases htail : t < k + 2
        · have hmem : some k ∈ waitingQueryTailSet t := ⟨k, rfl, htail⟩
          simp only [bound, Set.indicator_of_mem hmem,
            Set.indicator_of_notMem (show some k ∉ ({none} : Set WaitingQueryWorld) from by simp),
            Option.isSome_some, sub_zero]
          rw [waitingQueryTrace_undetected t k htail]
          dsimp [b]
          linarith
        · have hnot : some k ∉ waitingQueryTailSet t := by simpa [waitingQueryTailSet] using htail
          simp only [bound, Set.indicator_of_notMem hnot,
            Set.indicator_of_notMem (show some k ∉ ({none} : Set WaitingQueryWorld) from by simp),
            sub_zero]
          exact measureReal_le_one
    have htset : MeasurableSet (waitingQueryTailSet t) := trivial
    have hnset : MeasurableSet ({none} : Set WaitingQueryWorld) := measurableSet_singleton _
    have hbound : Integrable bound α :=
      ((integrable_const 1).sub ((integrable_const (1 - b)).indicator htset)).sub
        ((integrable_const b).indicator hnset)
    have hv : bayesRuleValue α (waitingQueryRecordKernel t) r waitingQueryBinaryUtility ≤
        1 - waitingQueryTail α t * (1 - b) - α.real {none} * b := by
      unfold bayesRuleValue
      calc
        _ ≤ ∫ θ, bound θ ∂α := integral_mono
          (integrable_bayesRulePayoff α (waitingQueryRecordKernel t) r waitingQueryBinaryUtility
            hum waitingQueryBinaryUtility_unit) hbound hpoint
        _ = _ := by
          dsimp [bound]
          rw [integral_sub (f := fun θ => 1 - (waitingQueryTailSet t).indicator (fun _ => 1 - b) θ)
            (g := ({none} : Set WaitingQueryWorld).indicator (fun _ => b))
            ((integrable_const 1).sub ((integrable_const (1 - b)).indicator htset))
            ((integrable_const b).indicator hnset),
            integral_sub (f := fun _ : WaitingQueryWorld => (1 : ℝ))
              (g := (waitingQueryTailSet t).indicator (fun _ => 1 - b))
              (integrable_const 1) ((integrable_const (1 - b)).indicator htset),
            integral_indicator_const _ htset, integral_indicator_const _ hnset]
          simp [waitingQueryTail, smul_eq_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hdom) hb]
  · have h := waitingQuery_bayesValue_sub_le_tail α t waitingQueryBinaryTarget
      waitingQueryBinaryUtility waitingQueryBinaryUtility_unit
    rw [waitingQueryBinaryTarget_value] at h
    linarith

/-- Literal optimized regret in the geometric example: query value one,
waiting value `1-2^(-t)`, for every positive observation time. -/
theorem waitingQueryGeometric_binary_regret (t : ℕ) (ht : 1 ≤ t) :
    bayesExperimentValue waitingQueryGeometricPrior waitingQueryBinaryTarget waitingQueryBinaryUtility -
      bayesExperimentValue waitingQueryGeometricPrior (waitingQueryRecordKernel t)
        waitingQueryBinaryUtility = (1 / 2 : ℝ) ^ t := by
  have hdom : waitingQueryTail waitingQueryGeometricPrior t ≤ waitingQueryGeometricPrior.real {none} := by
    rw [waitingQueryGeometric_tail t ht, waitingQueryGeometricPrior_none]
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) ht
  rw [waitingQueryBinaryTarget_value,
    waitingQuery_binary_value_eq_one_sub_tail _ t hdom, waitingQueryGeometric_tail t ht]
  ring

/-- A task-dependent evaluation prior that balances infinity against one
specified delayed finite world. Its finite-world index may grow with time. -/
noncomputable def waitingQueryBalancedPrior (k : ℕ) : Measure WaitingQueryWorld :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac none + (1 / 2 : ℝ≥0∞) • Measure.dirac (some k)

instance waitingQueryBalancedPrior_isProbability (k : ℕ) :
    IsProbabilityMeasure (waitingQueryBalancedPrior k) := by
  constructor
  norm_num [waitingQueryBalancedPrior, ENNReal.inv_two_add_inv_two]

theorem waitingQueryBalancedPrior_none (k : ℕ) :
    (waitingQueryBalancedPrior k).real {none} = 1 / 2 := by
  norm_num [waitingQueryBalancedPrior, measureReal_def, Pi.single_apply]
  rw [if_neg (show (some k : WaitingQueryWorld) ≠ none by simp)]
  norm_num

theorem waitingQueryBalancedPrior_some (k : ℕ) :
    (waitingQueryBalancedPrior k).real {some k} = 1 / 2 := by
  norm_num [waitingQueryBalancedPrior, measureReal_def, Pi.single_apply]
  rw [if_neg (show (none : WaitingQueryWorld) ≠ some k by simp)]
  norm_num

theorem waitingQueryBalancedPrior_tail (t k : ℕ) (hk : t < k + 2) :
    waitingQueryTail (waitingQueryBalancedPrior k) t = 1 / 2 := by
  have hn : none ∉ waitingQueryTailSet t := by simp [waitingQueryTailSet]
  have hsome : some k ∈ waitingQueryTailSet t := ⟨k, rfl, hk⟩
  unfold waitingQueryTail waitingQueryBalancedPrior Measure.real
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (show MeasurableSet (waitingQueryTailSet t) from trivial),
    Measure.dirac_apply' _ (show MeasurableSet (waitingQueryTailSet t) from trivial),
    Set.indicator_of_notMem hn, Set.indicator_of_mem hsome]
  norm_num

/-- The same elementary binary task witnesses the full one-half audit at
every time, by choosing the prior on a still-undetected finite world. -/
theorem waitingQueryBalanced_binary_regret (t k : ℕ) (hk : t < k + 2) :
    bayesExperimentValue (waitingQueryBalancedPrior k) waitingQueryBinaryTarget waitingQueryBinaryUtility -
      bayesExperimentValue (waitingQueryBalancedPrior k) (waitingQueryRecordKernel t)
        waitingQueryBinaryUtility = (1 / 2 : ℝ) := by
  have hdom : waitingQueryTail (waitingQueryBalancedPrior k) t ≤
      (waitingQueryBalancedPrior k).real {none} := by
    rw [waitingQueryBalancedPrior_tail t k hk, waitingQueryBalancedPrior_none]
  rw [waitingQueryBinaryTarget_value, waitingQuery_binary_value_eq_one_sub_tail _ t hdom,
    waitingQueryBalancedPrior_tail t k hk]
  norm_num

end IdExp
