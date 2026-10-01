import Formal.FiniteBlackwell

/-!
# The Blackwell value converse, proved

`Decision.lean` states `BlackwellValueConverse`: on finite discrete spaces, if the optimal
downstream value after `E` is at least the optimal value after `F` for every finite action
space, every prior, and every utility, then `F` is a garbling of `E` (a Markov kernel).
`FiniteBlackwell.lean` proves the theorem for stochastic matrices by separation.  This file
supplies the bridge and discharges the statement:

* `matrixOf`, `ruleMatrix`, `kernelOfMatrix`: experiments and Markov kernels on finite discrete
  spaces are stochastic matrices, and every stochastic matrix is a Markov kernel;
* `finiteActionVector_eq_finiteDecisionLaw`: the class-conditional action law of a kernel rule is
  the matrix product;
* `decisionValue_eq_linearPayoff`: the Bayes value of a rule is a linear payoff of that law;
* `exists_optimal_rule`: optimal kernel rules exist (compactness of the stochastic-matrix simplex);
* `strongDual_apply_eq`: every linear functional on the law space is a prior–utility payoff with
  the uniform prior;
* `blackwellValueConverse`: the general interface in `Experiment.lean`, with no hypotheses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option linter.unusedSectionVars false

namespace IdExp

section Bridge

variable {Θ X D : Type*} [Fintype X] [Fintype D]
  [MeasurableSpace X] [MeasurableSpace D] [MeasurableSingletonClass X] [MeasurableSingletonClass D]

/-- The stochastic matrix of an experiment on a finite discrete space. -/
noncomputable def matrixOf (E : Experiment Θ X) : FiniteExperiment Θ X :=
  fun θ x => (E θ).real {x}

/-- The stochastic matrix of a kernel between finite discrete spaces. -/
noncomputable def ruleMatrix (r : Kernel X D) : X → D → ℝ :=
  fun x d => (r x).real {d}

theorem ruleMatrix_mem_stochasticRules (r : Kernel X D) [IsMarkovKernel r] :
    ruleMatrix r ∈ stochasticRules X D := by
  intro x _
  refine ⟨fun d => measureReal_nonneg, ?_⟩
  have h := sum_measureReal_singleton (μ := r x) (Finset.univ : Finset D)
  rw [Finset.coe_univ] at h
  simp only [ruleMatrix]
  rw [h, measureReal_def, measure_univ, ENNReal.toReal_one]

/-- The Markov kernel of a stochastic matrix on finite discrete spaces. -/
noncomputable def kernelOfMatrix (q : X → D → ℝ) : Kernel X D where
  toFun := fun x => ∑ d, ENNReal.ofReal (q x d) • Measure.dirac d
  measurable' := measurable_of_finite _

theorem kernelOfMatrix_apply_singleton (q : X → D → ℝ) (x : X) (d : D) :
    kernelOfMatrix q x {d} = ENNReal.ofReal (q x d) := by
  classical
  show (∑ d', ENNReal.ofReal (q x d') • Measure.dirac d') {d} = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hb
    simp [Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr hb)]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem isMarkovKernel_kernelOfMatrix (q : X → D → ℝ) (hq : q ∈ stochasticRules X D) :
    IsMarkovKernel (kernelOfMatrix q) := by
  refine ⟨fun x => ⟨?_⟩⟩
  show (∑ d, ENNReal.ofReal (q x d) • Measure.dirac d) Set.univ = 1
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  have hx := hq x (Set.mem_univ x)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun d _ => hx.1 d), hx.2, ENNReal.ofReal_one]

theorem ruleMatrix_kernelOfMatrix (q : X → D → ℝ) (hq : q ∈ stochasticRules X D) :
    ruleMatrix (kernelOfMatrix q) = q := by
  funext x d
  simp only [ruleMatrix, measureReal_def, kernelOfMatrix_apply_singleton]
  exact ENNReal.toReal_ofReal ((hq x (Set.mem_univ x)).1 d)

/-- A rule's class-conditional action law on a singleton is a matrix product. -/
theorem actionLaw_singleton (E : Experiment Θ X) (r : Kernel X D) (θ : Θ) (d : D) :
    actionLaw E r θ {d} = ∑ x, (E θ) {x} * r x {d} := by
  unfold actionLaw
  rw [Measure.bind_apply (measurableSet_singleton d) (Kernel.aemeasurable r), lintegral_fintype]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem isProbabilityMeasure_actionLaw (E : Experiment Θ X) (r : Kernel X D) [IsMarkovKernel r]
    (θ : Θ) [IsProbabilityMeasure (E θ)] : IsProbabilityMeasure (actionLaw E r θ) := by
  constructor
  unfold actionLaw
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable r)]
  simp

/-- The class-conditional action vector of a kernel rule is the matrix product of the
experiment's matrix with the rule's matrix. -/
theorem finiteActionVector_eq_finiteDecisionLaw (E : Experiment Θ X)
    (hE : ∀ θ, IsProbabilityMeasure (E θ)) (r : Kernel X D) [IsMarkovKernel r] :
    finiteActionVector E r = finiteDecisionLaw (matrixOf E) (ruleMatrix r) := by
  funext θ d
  have := hE θ
  simp only [finiteActionVector, finiteDecisionLaw, matrixOf, ruleMatrix, measureReal_def]
  rw [actionLaw_singleton, ENNReal.toReal_sum]
  · exact Finset.sum_congr rfl fun x _ => ENNReal.toReal_mul
  · exact fun x _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- The linear payoff of a class-conditional action law under a prior and a utility. -/
def linearPayoff [Fintype Θ] (α : Θ → ℝ) (u : Θ → D → ℝ) (v : Θ → D → ℝ) : ℝ :=
  ∑ θ, α θ * ∑ d, v θ d * u θ d

/-- The Bayes value of a kernel rule is the linear payoff of its action vector. -/
theorem decisionValue_eq_linearPayoff [Fintype Θ] (α : Θ → ℝ) (u : Θ → D → ℝ)
    (E : Experiment Θ X) (hE : ∀ θ, IsProbabilityMeasure (E θ)) (r : Kernel X D)
    [IsMarkovKernel r] :
    decisionValue α u E r = linearPayoff α u (finiteActionVector E r) := by
  unfold decisionValue linearPayoff
  refine Finset.sum_congr rfl fun θ _ => ?_
  have := hE θ
  have := isProbabilityMeasure_actionLaw E r θ
  rw [integral_fintype Integrable.of_finite]
  simp only [finiteActionVector, smul_eq_mul]

theorem continuous_linearPayoff_finiteDecisionLaw [Fintype Θ] (α : Θ → ℝ) (u : Θ → D → ℝ)
    (M : FiniteExperiment Θ X) :
    Continuous fun q : X → D → ℝ => linearPayoff α u (finiteDecisionLaw M q) := by
  unfold linearPayoff finiteDecisionLaw
  fun_prop

theorem stochasticRules_nonempty [Nonempty D] : (stochasticRules X D).Nonempty := by
  classical
  obtain ⟨d₀⟩ := ‹Nonempty D›
  refine ⟨fun _ d => if d = d₀ then 1 else 0, fun x _ => ⟨fun d => ?_, ?_⟩⟩
  · by_cases h : d = d₀ <;> simp [h]
  · simp

/-- **Optimal rules exist** on finite discrete spaces: the payoff is continuous on the compact
simplex of stochastic matrices, and the maximizing matrix is a Markov kernel. -/
theorem exists_optimal_rule [Fintype Θ] [Nonempty D] (α : Θ → ℝ) (u : Θ → D → ℝ)
    (E : Experiment Θ X) (hE : ∀ θ, IsProbabilityMeasure (E θ)) :
    ∃ r : Kernel X D, IsOptimalRule α u E r := by
  obtain ⟨q, hq, hmax⟩ := (isCompact_stochasticRules X D).exists_isMaxOn stochasticRules_nonempty
    (continuous_linearPayoff_finiteDecisionLaw α u (matrixOf E)).continuousOn
  have hM := isMarkovKernel_kernelOfMatrix q hq
  refine ⟨kernelOfMatrix q, hM, fun s hs => ?_⟩
  have := hs
  have := hM
  rw [decisionValue_eq_linearPayoff α u E hE s, decisionValue_eq_linearPayoff α u E hE _,
    finiteActionVector_eq_finiteDecisionLaw E hE s,
    finiteActionVector_eq_finiteDecisionLaw E hE (kernelOfMatrix q), ruleMatrix_kernelOfMatrix q hq]
  exact (isMaxOn_iff.1 hmax) (ruleMatrix s) (ruleMatrix_mem_stochasticRules s)

end Bridge

section Functionals

variable {Θ Y : Type*} [Fintype Θ] [Fintype Y] [DecidableEq Θ] [DecidableEq Y]

theorem pi_eq_sum_single (v : Θ → Y → ℝ) :
    v = ∑ θ, ∑ y, v θ y • (Pi.single θ (Pi.single y (1 : ℝ)) : Θ → Y → ℝ) := by
  funext θ' y'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single θ']
  · rw [Finset.sum_eq_single y']
    · simp
    · intro b _ hb
      simp [Pi.single_eq_same, Pi.single_eq_of_ne hb.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb.symm]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Every continuous linear functional on the law space is a coefficient sum. -/
theorem strongDual_apply_eq (f : StrongDual ℝ (Θ → Y → ℝ)) (v : Θ → Y → ℝ) :
    f v = ∑ θ, ∑ y, v θ y * f (Pi.single θ (Pi.single y (1 : ℝ))) := by
  conv_lhs => rw [pi_eq_sum_single v]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The uniform prior. -/
noncomputable def uniformPrior (Θ : Type*) [Fintype Θ] : Θ → ℝ :=
  fun _ => 1 / (Fintype.card Θ : ℝ)

theorem isDist_uniformPrior [Nonempty Θ] : IsDist (uniformPrior Θ) := by
  have hn : (Fintype.card Θ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun _ => by unfold uniformPrior; positivity, ?_⟩
  simp only [uniformPrior, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A linear functional as a utility under the uniform prior. -/
noncomputable def utilityOf (f : StrongDual ℝ (Θ → Y → ℝ)) : Θ → Y → ℝ :=
  fun θ y => (Fintype.card Θ : ℝ) * f (Pi.single θ (Pi.single y (1 : ℝ)))

theorem linearPayoff_uniform_utilityOf [Nonempty Θ] (f : StrongDual ℝ (Θ → Y → ℝ))
    (v : Θ → Y → ℝ) : linearPayoff (uniformPrior Θ) (utilityOf f) v = f v := by
  have hn : (Fintype.card Θ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [strongDual_apply_eq f v]
  unfold linearPayoff uniformPrior utilityOf
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  field_simp

end Functionals

/-- **Blackwell's value converse** (paper: the deep direction of Blackwell's theorem), in the
exact form stated in `Decision.lean`: on finite discrete spaces, dominance of optimal
downstream value for every finite action space, prior, and utility yields a garbling. -/
theorem blackwellValueConverse : BlackwellValueConverse := by
  intro Θ X Y _ _ _ _ _ _ _ _ E F hE hF hval
  classical
  -- `Y` is nonempty because `F θ` is a probability measure on it
  have hY : Nonempty Y := by
    obtain ⟨θ⟩ := ‹Nonempty Θ›
    by_contra h
    rw [not_nonempty_iff] at h
    have := hF θ
    have h0 : (F θ) Set.univ = 0 := by rw [Set.univ_eq_empty_iff.mpr h, measure_empty]
    rw [measure_univ] at h0
    exact one_ne_zero h0
  -- every linear payoff of `F`'s matrix is matched inside `E`'s matrix menu
  have hdom : DominatesEveryFiniteValue (matrixOf E) (matrixOf F) := by
    intro f
    obtain ⟨rE, hrE⟩ := exists_optimal_rule (uniformPrior Θ) (utilityOf f) E hE
    obtain ⟨rF, hrF⟩ := exists_optimal_rule (uniformPrior Θ) (utilityOf f) F hF
    have h1 := hval Y (uniformPrior Θ) isDist_uniformPrior (utilityOf f) rE rF hrE hrF
    have h2 : decisionValue (uniformPrior Θ) (utilityOf f) F Kernel.id ≤
        decisionValue (uniformPrior Θ) (utilityOf f) F rF := hrF.2 Kernel.id inferInstance
    have := hrE.1
    have := hrF.1
    refine ⟨finiteDecisionLaw (matrixOf E) (ruleMatrix rE),
      ⟨ruleMatrix rE, ruleMatrix_mem_stochasticRules rE, rfl⟩, ?_⟩
    have hid : finiteActionVector F Kernel.id = matrixOf F := by
      funext θ y
      simp [finiteActionVector, matrixOf, actionLaw, Kernel.id, Kernel.deterministic_apply]
    calc f (matrixOf F)
        = linearPayoff (uniformPrior Θ) (utilityOf f) (finiteActionVector F Kernel.id) := by
          rw [hid, linearPayoff_uniform_utilityOf]
      _ = decisionValue (uniformPrior Θ) (utilityOf f) F Kernel.id :=
          (decisionValue_eq_linearPayoff _ _ F hF Kernel.id).symm
      _ ≤ decisionValue (uniformPrior Θ) (utilityOf f) F rF := h2
      _ ≤ decisionValue (uniformPrior Θ) (utilityOf f) E rE := h1
      _ = linearPayoff (uniformPrior Θ) (utilityOf f) (finiteActionVector E rE) :=
          decisionValue_eq_linearPayoff _ _ E hE rE
      _ = f (finiteDecisionLaw (matrixOf E) (ruleMatrix rE)) := by
          rw [finiteActionVector_eq_finiteDecisionLaw E hE rE, linearPayoff_uniform_utilityOf]
  -- separation puts `F`'s matrix in `E`'s menu; the witnessing matrix is the garbling
  obtain ⟨G, hG, hGF⟩ := finiteBlackwellLE_of_dominatesEveryFiniteValue (matrixOf E) (matrixOf F) hdom
  have hM := isMarkovKernel_kernelOfMatrix G hG
  refine ⟨kernelOfMatrix G, hM, fun θ => ?_⟩
  have := hM
  have := hE θ
  have := hF θ
  have : IsProbabilityMeasure ((E θ).bind fun x => kernelOfMatrix G x) :=
    isProbabilityMeasure_actionLaw E (kernelOfMatrix G) θ
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro y
  have hv := congrFun (congrFun (finiteActionVector_eq_finiteDecisionLaw E hE (kernelOfMatrix G)) θ) y
  rw [ruleMatrix_kernelOfMatrix G hG] at hv
  have hF' := congrFun (congrFun hGF θ) y
  have := hv.trans hF'
  simpa [finiteActionVector, actionLaw, matrixOf] using this

end IdExp
