import Formal.FullRevelation
import Formal.RecoveryBridge
import Formal.DecoderRounding

/-!
# Finite causal recovery at an attainable full-revelation top

This module instantiates the measure-level full-revelation theorem on the
actual causal path laws, and connects terminal exact-label deficiency to
the optimized finite-prefix decoding errors. Finiteness of the world class
supplies prefix continuity; full revelation must additionally be attainable
for native sufficiency to imply model identification.

Posterior concentration is proved in `CausalPosterior.lean`, which assembles
all six recovery items. General finite-class exact terminal attainment and
Blackwell greatestness are proved in `CausalTerminalGarbling.lean`.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

/-- The finite matrix and measure-kernel full-label experiments agree
literally, rather than merely up to a comparison of their values. -/
theorem exactLabelExperiment_eq_rowExperiment_finiteLabel :
    exactLabelExperiment Θ = rowExperiment (finiteLabelExperiment Θ) := by
  funext θ
  apply finiteMeasureOfRow_eq_of_forall_singleton
  intro η
  change Measure.dirac θ {η} = ENNReal.ofReal (diracExp id θ η)
  by_cases h : η = θ
  · subst η
    simp [diracExp_apply]
  · simp [diracExp_apply, h, Ne.symm h]

theorem isProbabilityMeasure_exactLabelExperiment (θ : Θ) :
    IsProbabilityMeasure (exactLabelExperiment Θ θ : Measure Θ) := by
  change IsProbabilityMeasure (Measure.dirac θ)
  infer_instance

variable {A O : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- Almost-sure class identification by one measurable decoder of the full
causal trajectory. -/
def CausalExactlyIdentifies (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) : Prop :=
  ∃ D : CausalTraj A O → Θ, MeasurableExactDecoder (causalPathExperiment Qs hQ π) D

/-- Attainable full revelation, with no assumption that native sufficiency
alone identifies a finite class. Reverse Blackwell dominance is automatic. -/
def CausalFullRevelationAttainable (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) : Prop :=
  ∃ π : ValidCausalPolicy A O,
    BlackwellLE (fun θ => Measure.dirac θ)
      (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))

theorem causalExactlyIdentifies_iff_correct_probability_one
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalExactlyIdentifies Qs hQ π ↔
      ∃ D : CausalTraj A O → Θ, Measurable D ∧
        ∀ θ, (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))
          {ω | D ω = θ} = 1 := by
  unfold CausalExactlyIdentifies
  simp_rw [measurableExactDecoder_iff_correct_probability_one
    (causalPathExperiment Qs hQ π) (isProbabilityMeasure_causalPathExperiment' Qs hQ π)]

theorem causalExactlyIdentifies_iff_pairwise_mutuallySingular
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalExactlyIdentifies Qs hQ π ↔
      Pairwise fun θ η =>
        (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)) ⟂ₘ
          (causalPathExperiment Qs hQ π η : Measure (CausalTraj A O)) :=
  exists_measurableExactDecoder_iff_pairwise_mutuallySingular (causalPathExperiment Qs hQ π)

theorem causalExactlyIdentifies_iff_blackwellLE_exactLabel
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalExactlyIdentifies Qs hQ π ↔
      BlackwellLE (fun θ => Measure.dirac θ)
        (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))) :=
  (blackwellLE_exactLabel_iff_decoder (causalPathExperiment Qs hQ π)
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)).symm

theorem causalFullRevelationAttainable_iff_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    CausalFullRevelationAttainable Qs hQ ↔ ∃ π, CausalExactlyIdentifies Qs hQ π := by
  unfold CausalFullRevelationAttainable
  simp_rw [causalExactlyIdentifies_iff_blackwellLE_exactLabel Qs hQ]

theorem causalExactlyIdentifies_iff_terminal_exactLabelDeficiency_eq_zero
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalExactlyIdentifies Qs hQ π ↔
      finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (exactLabelExperiment Θ) = 0 :=
  (finiteMeasureDeficiency_exactLabel_eq_zero_iff_decoder (causalPathExperiment Qs hQ π)
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)).symm

/-! ## The exact prefix/terminal decoding bridge -/

theorem finiteMeasureDeficiency_causalTrace_exactLabel_eq_finiteLabel
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) :
    finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
      (exactLabelExperiment Θ) =
      finiteDeficiency (causalFiniteExperiment π.1 Qs t) (finiteLabelExperiment Θ) := by
  rw [causalTraceMeasureExperiment_eq_rowExperiment,
    exactLabelExperiment_eq_rowExperiment_finiteLabel]
  exact finiteMeasureDeficiency_eq_finiteDeficiency _ _
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) finiteLabelExperiment_valid

/-- Finite-class prefix continuity turns terminal zero label deficiency into
vanishing prefix label deficiency; exact prefix garbling proves the reverse. -/
theorem causalPrefix_labelDeficiency_tendsto_zero_iff_terminal
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    Tendsto (fun t => finiteDeficiency (causalFiniteExperiment π.1 Qs t)
      (finiteLabelExperiment Θ)) atTop (𝓝 0) ↔
      finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (exactLabelExperiment Θ) = 0 := by
  have hP := isProbabilityMeasure_causalPathExperiment' Qs hQ π
  have hL := isProbabilityMeasure_exactLabelExperiment (Θ := Θ)
  constructor
  · intro hlim
    apply le_antisymm ?_ (finiteMeasureDeficiency_nonneg_of_prob _ _ hP hL)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨t, ht⟩ := ((tendsto_order.1 hlim).2 ε hε).exists
    have hle := finiteMeasureDeficiency_path_le_trace Qs hQ π t
      (exactLabelExperiment Θ) hL
    rw [finiteMeasureDeficiency_causalTrace_exactLabel_eq_finiteLabel] at hle
    simpa only [zero_add] using hle.trans ht.le
  · intro hzero
    apply squeeze_zero
      (fun t => finiteDeficiency_nonneg_of_fintype
        (causalFiniteExperiment π.1 Qs t) (finiteLabelExperiment Θ))
      (fun t => ?_) (tendsto_causalPrefixDeficiency Qs hQ π)
    have htri := finiteMeasureDeficiency_triangle_of_prob
      (causalTraceMeasureExperiment Qs hQ π t) (causalPathExperiment Qs hQ π)
      (exactLabelExperiment Θ)
      (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π t) hP hL
    rw [hzero, add_zero,
      finiteMeasureDeficiency_causalTrace_exactLabel_eq_finiteLabel] at htri
    exact htri

theorem causalPrefix_deterministicLabelError_tendsto_zero_iff_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    Tendsto (fun t => deterministicLabelMinimaxError (causalFiniteExperiment π.1 Qs t))
      atTop (𝓝 0) ↔ CausalExactlyIdentifies Qs hQ π := by
  rw [causalPrefix_deterministic_randomized_label_tendsto_zero_iff Qs hQ π.1 π.2,
    causalPrefix_labelDeficiency_tendsto_zero_iff_terminal Qs hQ π,
    causalExactlyIdentifies_iff_terminal_exactLabelDeficiency_eq_zero Qs hQ π]

/-! ## The attained full-revelation specialization -/

theorem causalExactlyIdentifies_iff_fullRevelationBlackwellEquiv
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalExactlyIdentifies Qs hQ π ↔
      BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
          (fun θ => Measure.dirac θ) ∧
        BlackwellLE (fun θ => Measure.dirac θ)
          (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))) := by
  constructor
  · intro h
    exact ⟨blackwellLE_from_exactLabel (causalPathExperiment Qs hQ π)
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π),
      (causalExactlyIdentifies_iff_blackwellLE_exactLabel Qs hQ π).1 h⟩
  · intro h
    exact (causalExactlyIdentifies_iff_blackwellLE_exactLabel Qs hQ π).2 h.2

/-- The attainability hypothesis is exactly existence of a path experiment
Blackwell-equivalent to full revelation, as stated in the paper. -/
theorem causalFullRevelationAttainable_iff_blackwellEquiv
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    CausalFullRevelationAttainable Qs hQ ↔
      ∃ π : ValidCausalPolicy A O,
        BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
            (fun θ => Measure.dirac θ) ∧
          BlackwellLE (fun θ => Measure.dirac θ)
            (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))) := by
  rw [causalFullRevelationAttainable_iff_exactlyIdentifies Qs hQ]
  simp_rw [causalExactlyIdentifies_iff_fullRevelationBlackwellEquiv Qs hQ]

/-- An exactly identifying terminal experiment dominates every attainable
complete experiment by an actual Markov kernel, not only with deficiency zero. -/
theorem causalPath_blackwellLE_of_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (hid : CausalExactlyIdentifies Qs hQ π)
    (σ : ValidCausalPolicy A O) :
    BlackwellLE (fun θ => (causalPathExperiment Qs hQ σ θ : Measure (CausalTraj A O)))
      (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))) :=
  blackwellLE_trans _ (fun θ => Measure.dirac θ) _
    ((causalExactlyIdentifies_iff_blackwellLE_exactLabel Qs hQ π).1 hid)
    (blackwellLE_from_exactLabel (causalPathExperiment Qs hQ σ)
      (isProbabilityMeasure_causalPathExperiment' Qs hQ σ))

theorem causalNativelySufficient_of_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (hid : CausalExactlyIdentifies Qs hQ π) :
    CausalNativelySufficient Qs π := by
  apply (causalNativelySufficient_iff_terminalDeficiencyZero Qs hQ π).2
  intro σ
  obtain ⟨κ, hκ, hκE⟩ := causalPath_blackwellLE_of_exactlyIdentifies Qs hQ π hid σ
  exact finiteMeasureDeficiency_garbling_eq_zero
    (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ σ)
    ⟨κ, hκ⟩ fun θ => Subtype.ext (hκE θ)

/-- The extra full-revelation attainability hypothesis is essential:
finiteness alone does not turn native sufficiency into identification. -/
theorem causalNativelySufficient_iff_exactlyIdentifies_of_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔ CausalExactlyIdentifies Qs hQ π := by
  constructor
  · intro hnative
    obtain ⟨ρ, hρ⟩ := hattain
    have hπρ := (causalNativelySufficient_iff_terminalDeficiencyZero Qs hQ π).1 hnative ρ
    have hρL := finiteMeasureDeficiency_exactLabel_eq_zero_of_blackwellLE
      (causalPathExperiment Qs hQ ρ) hρ
    have hPπ := isProbabilityMeasure_causalPathExperiment' Qs hQ π
    have hPρ := isProbabilityMeasure_causalPathExperiment' Qs hQ ρ
    have hL := isProbabilityMeasure_exactLabelExperiment (Θ := Θ)
    apply (causalExactlyIdentifies_iff_terminal_exactLabelDeficiency_eq_zero Qs hQ π).2
    apply le_antisymm ?_ (finiteMeasureDeficiency_nonneg_of_prob _ _ hPπ hL)
    have htri := finiteMeasureDeficiency_triangle_of_prob
      (causalPathExperiment Qs hQ π) (causalPathExperiment Qs hQ ρ)
      (exactLabelExperiment Θ) hPπ hPρ hL
    simpa only [hπρ, hρL, zero_add] using htri
  · exact causalNativelySufficient_of_exactlyIdentifies Qs hQ π

theorem causalNativelySufficient_iff_fullRevelationBlackwellEquiv_of_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
          (fun θ => Measure.dirac θ) ∧
        BlackwellLE (fun θ => Measure.dirac θ)
          (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))) :=
  (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).trans
    (causalExactlyIdentifies_iff_fullRevelationBlackwellEquiv Qs hQ π)

theorem causalNativelySufficient_iff_pairwise_mutuallySingular_of_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      Pairwise fun θ η =>
        (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)) ⟂ₘ
          (causalPathExperiment Qs hQ π η : Measure (CausalTraj A O)) :=
  (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).trans
    (causalExactlyIdentifies_iff_pairwise_mutuallySingular Qs hQ π)

theorem causalNativelySufficient_iff_prefixLabelDeficiency_tendsto_zero_of_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      Tendsto (fun t => finiteDeficiency (causalFiniteExperiment π.1 Qs t)
        (finiteLabelExperiment Θ)) atTop (𝓝 0) :=
  (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).trans
    ((causalExactlyIdentifies_iff_terminal_exactLabelDeficiency_eq_zero Qs hQ π).trans
      (causalPrefix_labelDeficiency_tendsto_zero_iff_terminal Qs hQ π).symm)

theorem causalNativelySufficient_iff_prefixDeterministicError_tendsto_zero_of_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      Tendsto (fun t => deterministicLabelMinimaxError (causalFiniteExperiment π.1 Qs t))
        atTop (𝓝 0) :=
  (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).trans
    (causalPrefix_deterministicLabelError_tendsto_zero_iff_exactlyIdentifies Qs hQ π).symm

/-- The five non-posterior items of the finite recovery theorem, on the
literal causal path and prefix experiments. The complete six-item theorem is
`causalFiniteRecovery` in `CausalPosterior.lean`; exact terminal greatestness
is supplied by `CausalTerminalGarbling.lean`. -/
theorem causalFiniteRecovery_without_posterior
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    (CausalNativelySufficient Qs π ↔
      BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
          (fun θ => Measure.dirac θ) ∧
        BlackwellLE (fun θ => Measure.dirac θ)
          (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))) ∧
    (CausalNativelySufficient Qs π ↔
      Pairwise fun θ η =>
        (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)) ⟂ₘ
          (causalPathExperiment Qs hQ π η : Measure (CausalTraj A O))) ∧
    (CausalNativelySufficient Qs π ↔
      ∃ D : CausalTraj A O → Θ, Measurable D ∧
        ∀ θ, (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))
          {ω | D ω = θ} = 1) ∧
    (CausalNativelySufficient Qs π ↔
      Tendsto (fun t => deterministicLabelMinimaxError (causalFiniteExperiment π.1 Qs t))
        atTop (𝓝 0)) :=
  ⟨causalNativelySufficient_iff_fullRevelationBlackwellEquiv_of_attainable Qs hQ hattain π,
    causalNativelySufficient_iff_pairwise_mutuallySingular_of_attainable Qs hQ hattain π,
    (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).trans
      (causalExactlyIdentifies_iff_correct_probability_one Qs hQ π),
    causalNativelySufficient_iff_prefixDeterministicError_tendsto_zero_of_attainable Qs hQ hattain π⟩

end IdExp
