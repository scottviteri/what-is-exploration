import Formal.MeasurableInformationContinuity

/-!
# Prior-average simulation error on arbitrary measurable world classes

The prior averages conditional row-TV errors of one world-independent randomized
matrix. This is not TV between predictive mixtures. Signal alphabets are finite;
no topology, countability, or support condition on the world class is assumed.
-/
namespace IdExp
open MeasureTheory Set Finset Filter Topology
noncomputable section

variable {Θ X Y Z : Type*} [MeasurableSpace Θ]
  [Fintype X] [Fintype Y] [Fintype Z]

/-- Average conditional error of one randomized decoder. -/
def priorAverageDecodeErr (μ : Measure Θ) (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) : ℝ :=
  ∫ θ, decodeErr E F G θ ∂μ

/-- Actual achievable upper bounds on prior-average decoder error. -/
def priorAverageDeficiencyCandidates (μ : Measure Θ)
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) : Set ℝ :=
  {c | ∃ G ∈ stochasticRules X Y, priorAverageDecodeErr μ E F G ≤ c}

/-- Directed deficiency with the supremum over worlds replaced by a prior average. -/
def priorAverageDeficiency (μ : Measure Θ) (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) : ℝ :=
  sInf (priorAverageDeficiencyCandidates μ E F)

theorem priorAverageDecodeErr_nonneg (μ : Measure Θ) (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) :
    0 ≤ priorAverageDecodeErr μ E F G :=
  integral_nonneg (decodeErr_nonneg E F G)

theorem integrable_finiteDecodeErr (μ : Measure Θ) [IsFiniteMeasure μ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ x, Measurable (fun θ => E θ x))
    (hmF : ∀ y, Measurable (fun θ => F θ y))
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    Integrable (decodeErr E F G) μ := by
  apply Integrable.of_bound (measurable_finiteDecodeErr E F hmE hmF G).aestronglyMeasurable 1
  filter_upwards [] with θ
  simpa only [Real.norm_eq_abs, abs_of_nonneg (decodeErr_nonneg E F G θ)] using
    decodeErr_le_one E F hE hF G hG θ

theorem priorAverageDeficiencyCandidates_nonempty [Nonempty Y]
    (μ : Measure Θ) (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    (priorAverageDeficiencyCandidates μ E F).Nonempty := by
  classical
  let G : X → Y → ℝ := fun _ => uniformPrior Y
  have hG : G ∈ stochasticRules X Y := fun _ _ => isDist_uniformPrior
  exact ⟨priorAverageDecodeErr μ E F G, G, hG, le_rfl⟩

theorem priorAverageDeficiencyCandidates_bddBelow
    (μ : Measure Θ) (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    BddBelow (priorAverageDeficiencyCandidates μ E F) :=
  ⟨0, fun _ ⟨G, _, hG⟩ => (priorAverageDecodeErr_nonneg μ E F G).trans hG⟩

theorem priorAverageDeficiency_nonneg [Nonempty Y]
    (μ : Measure Θ) (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    0 ≤ priorAverageDeficiency μ E F := by
  apply le_csInf (priorAverageDeficiencyCandidates_nonempty μ E F)
  rintro c ⟨G, _, hG⟩
  exact (priorAverageDecodeErr_nonneg μ E F G).trans hG

theorem priorAverageDeficiency_le_of_decoder (μ : Measure Θ)
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (c : ℝ)
    (he : priorAverageDecodeErr μ E F G ≤ c) :
    priorAverageDeficiency μ E F ≤ c :=
  csInf_le (priorAverageDeficiencyCandidates_bddBelow μ E F) ⟨G, hG, he⟩

theorem exists_decoder_le_priorAverageDeficiency_add [Nonempty Y]
    (μ : Measure Θ) (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    {η : ℝ} (hη : 0 < η) :
    ∃ G ∈ stochasticRules X Y,
      priorAverageDecodeErr μ E F G ≤ priorAverageDeficiency μ E F + η := by
  obtain ⟨c, ⟨G, hG, he⟩, hc⟩ := exists_lt_of_csInf_lt
    (priorAverageDeficiencyCandidates_nonempty μ E F)
    (show sInf (priorAverageDeficiencyCandidates μ E F) <
      priorAverageDeficiency μ E F + η from lt_add_of_pos_right _ hη)
  exact ⟨G, hG, he.trans hc.le⟩

theorem exists_decoder_lt_of_priorAverageDeficiency_lt [Nonempty Y]
    (μ : Measure Θ) (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    {ε : ℝ} (hε : priorAverageDeficiency μ E F < ε) :
    ∃ G ∈ stochasticRules X Y, priorAverageDecodeErr μ E F G < ε := by
  obtain ⟨c, ⟨G, hG, he⟩, hc⟩ := exists_lt_of_csInf_lt
    (priorAverageDeficiencyCandidates_nonempty μ E F) hε
  exact ⟨G, hG, he.trans_lt hc⟩

theorem priorAverageDeficiency_le_finiteDeficiency [Nonempty Θ] [Nonempty Y]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ x, Measurable (fun θ => E θ x))
    (hmF : ∀ y, Measurable (fun θ => F θ y)) :
    priorAverageDeficiency μ E F ≤ finiteDeficiency E F := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨G, hG, he⟩ := exists_decoder_le_finiteDeficiency_add E F hE hF hη
  apply priorAverageDeficiency_le_of_decoder μ E F G hG _
  have h := integral_mono (integrable_finiteDecodeErr μ E F hE hF hmE hmF G hG)
    (integrable_const (finiteDeficiency E F + η)) he
  simpa [priorAverageDecodeErr] using h

/-- Every valid finite target can be simulated with average TV error at most one. -/
theorem priorAverageDeficiency_le_one [Nonempty Y]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hmE : ∀ x, Measurable (fun θ => E θ x))
    (hmF : ∀ y, Measurable (fun θ => F θ y)) :
    priorAverageDeficiency μ E F ≤ 1 := by
  obtain ⟨_, G, hG, _⟩ := priorAverageDeficiencyCandidates_nonempty μ E F
  apply priorAverageDeficiency_le_of_decoder μ E F G hG 1
  have h := integral_mono (integrable_finiteDecodeErr μ E F hE hF hmE hmF G hG)
    (integrable_const (1 : ℝ)) (decodeErr_le_one E F hE hF G hG)
  simpa [priorAverageDecodeErr] using h

theorem priorAverageDeficiency_triangle [Nonempty Y] [Nonempty Z]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (H : FiniteExperiment Θ Z)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) (hH : IsFiniteExperiment H)
    (hmE : ∀ x, Measurable (fun θ => E θ x))
    (hmF : ∀ y, Measurable (fun θ => F θ y))
    (hmH : ∀ z, Measurable (fun θ => H θ z)) :
    priorAverageDeficiency μ E H ≤ priorAverageDeficiency μ E F + priorAverageDeficiency μ F H := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨G, hG, heG⟩ := exists_decoder_le_priorAverageDeficiency_add μ E F (half_pos hη)
  obtain ⟨R, hR, heR⟩ := exists_decoder_le_priorAverageDeficiency_add μ F H (half_pos hη)
  have hGR := stochasticRuleComp_mem_stochasticRules hG hR
  have hiG := integrable_finiteDecodeErr μ E F hE hF hmE hmF G hG
  have hiR := integrable_finiteDecodeErr μ F H hF hH hmF hmH R hR
  have hiGR := integrable_finiteDecodeErr μ E H hE hH hmE hmH _ hGR
  have he := integral_mono hiGR (hiG.add hiR)
    (decodeErr_stochasticRuleComp_le_add E F H G R hR)
  simp only [Pi.add_apply] at he
  rw [integral_add hiG hiR] at he
  have hb := priorAverageDeficiency_le_of_decoder μ E H _ hGR _ le_rfl
  dsimp [priorAverageDecodeErr] at heG heR hb
  linarith

/-- The average of a square dominates the square of the average under a probability prior. -/
theorem sq_integral_le_integral_sq_probability (μ : Measure Θ) [IsProbabilityMeasure μ]
    (f : Θ → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun θ => (f θ)^2) μ) :
    (∫ θ, f θ ∂μ)^2 ≤ ∫ θ, (f θ)^2 ∂μ := by
  let c := ∫ θ, f θ ∂μ
  have he : (∫ θ, (f θ - c)^2 ∂μ) = (∫ θ, (f θ)^2 ∂μ) - c^2 := by
    calc
      (∫ θ, (f θ - c)^2 ∂μ) =
          ∫ θ, ((f θ)^2 - (2*c) * f θ + c^2) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with θ
        ring
      _ = _ := by
        have ha := integral_add (hf2.sub (hf.const_mul (2*c)))
          (integrable_const (c^2))
        have hs := integral_sub hf2 (hf.const_mul (2*c))
        simp only [Pi.sub_apply] at ha hs
        rw [ha, hs, integral_const_mul]
        simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
        dsimp [c]
        ring
  have hn : 0 ≤ ∫ θ, (f θ - c)^2 ∂μ := integral_nonneg fun θ => sq_nonneg _
  rw [he] at hn
  dsimp [c] at hn
  linarith

/-- The existing explicit Bayes channel also satisfies the mean-TV square-root bound. -/
theorem priorAverageDecodeErr_reverse_le_information_gap [Nonempty X]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hmE : ∀ x, Measurable (fun θ => E θ x))
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    priorAverageDecodeErr μ (finiteDecisionLaw E G) E (measurableBayesReverse μ E G) ≤
      Real.sqrt ((infinitePriorInformation μ E -
        infinitePriorInformation μ (finiteDecisionLaw E G))/2) := by
  have hEG := finiteDecisionLaw_valid E hE G hG
  have hmEG := measurable_finiteDecisionLaw E hmE G
  have hR := measurableBayesReverse_stochastic μ E hE hmE G hG
  have hi := integrable_finiteDecodeErr μ _ E hEG hE hmEG hmE _ hR
  have hi2 := integrable_sq_finiteDecodeErr μ _ E hEG hE hmEG hmE _ hR
  apply Real.le_sqrt_of_sq_le
  exact (sq_integral_le_integral_sq_probability μ _ hi hi2).trans
    (integral_reverse_sq_le_information_gap μ E hE hmE G hG)

/-- The identity decoder bounds deficiency by the average row distance. -/
theorem priorAverageDeficiency_le_integral_rowTV (μ : Measure Θ)
    (E F : FiniteExperiment Θ X) :
    priorAverageDeficiency μ E F ≤ ∫ θ, finiteTV (E θ) (F θ) ∂μ := by
  classical
  let G : X → X → ℝ := fun x y => if x = y then 1 else 0
  apply priorAverageDeficiency_le_of_decoder μ E F G (identity_mem_stochasticRules X)
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [] with θ
  change finiteTV (finiteDecisionLaw E G θ) (F θ) = _
  have he : finiteDecisionLaw E G θ = E θ := by
    funext x
    simp [finiteDecisionLaw, G]
  rw [he]

theorem priorAverageDeficiency_eq_zero_of_blackwell [Nonempty Y]
    (μ : Measure Θ) (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (h : FiniteBlackwellLE F E) : priorAverageDeficiency μ E F = 0 := by
  obtain ⟨G, hG, he⟩ := h
  apply le_antisymm _ (priorAverageDeficiency_nonneg μ E F)
  apply priorAverageDeficiency_le_of_decoder μ E F G hG
  have hz : priorAverageDecodeErr μ E F G = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with θ
    change finiteTV (finiteDecisionLaw E G θ) (F θ) = 0
    rw [he]
    simp [finiteTV]
  exact hz.le

end
end IdExp
