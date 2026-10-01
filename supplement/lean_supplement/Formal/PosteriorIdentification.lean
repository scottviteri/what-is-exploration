import Formal.FiniteBayes
import Formal.FullRevelation

/-!
# Posterior concentration and exact identification

For a finite world class, finite observations that increase to the full
sample sigma-algebra have concentrating Bayes posteriors exactly when the
sample identifies the world. The observation spaces may vary with time.
The theorem is independent of how the sample laws were generated.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

variable {Θ Ω : Type*} [Fintype Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [mΩ : MeasurableSpace Ω]

/-- A sample filtration lifted to the Bayesian joint space: the hidden
class coordinate is never directly observed. -/
def finiteBayesFiltration (ℱ : Filtration ℕ mΩ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Θ × Ω)) where
  seq n := MeasurableSpace.comap Prod.snd (ℱ n)
  mono' := fun _ _ h => MeasurableSpace.comap_mono (ℱ.mono h)
  le' n := (MeasurableSpace.comap_mono (ℱ.le n)).trans
    (measurable_iff_comap_le.1 measurable_snd)

theorem iSup_finiteBayesFiltration (ℱ : Filtration ℕ mΩ)
    (hgen : (⨆ n, ℱ n) = mΩ) :
    (⨆ n, finiteBayesFiltration (Θ := Θ) ℱ n) =
      MeasurableSpace.comap (Prod.snd : Θ × Ω → Ω) mΩ := by
  change (⨆ n, MeasurableSpace.comap Prod.snd (ℱ n)) = _
  rw [← MeasurableSpace.comap_iSup, hgen]

variable {S : ℕ → Type*} [∀ n, Fintype (S n)]
  [∀ n, MeasurableSpace (S n)] [∀ n, MeasurableSingletonClass (S n)]

/-- Under each world, the posterior assigned to that world tends to one.
For a full-support prior this is equivalent to joint-law concentration. -/
def FiniteBayesConcentrates (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (p : ∀ n, Ω → S n) (E : ∀ n, Θ → S n → ℝ) : Prop :=
  ∀ θ, ∀ᵐ ω ∂μ θ,
    Tendsto (fun n => finiteBayesPosterior α (E n) (p n ω) θ) atTop (𝓝 1)

theorem finiteBayesConcentrates_iff_joint (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (p : ∀ n, Ω → S n) (E : ∀ n, Θ → S n → ℝ) (hfs : FullSupport α) :
    FiniteBayesConcentrates α μ p E ↔
      ∀ᵐ x ∂finiteBayesJoint α μ,
        Tendsto (fun n => finiteBayesPosterior α (E n) (p n x.2) x.1) atTop (𝓝 1) :=
  (ae_finiteBayesJoint_iff α μ hfs (fun x =>
    Tendsto (fun n => finiteBayesPosterior α (E n) (p n x.2) x.1) atTop (𝓝 1))).symm

theorem finiteBayesFiltration_eq_observation
    (ℱ : Filtration ℕ mΩ) (p : ∀ n, Ω → S n)
    (hℱ : ∀ n, ℱ n = MeasurableSpace.comap (p n) inferInstance) (n : ℕ) :
    finiteBayesFiltration (Θ := Θ) ℱ n = finiteBayesObservationSigma (p n) := by
  change MeasurableSpace.comap Prod.snd (ℱ n) = _
  rw [hℱ, MeasurableSpace.comap_comp]
  rfl

/-- Lévy convergence of every literal Bayes posterior coordinate, without
any identifiability assumption. -/
theorem finiteBayesPosterior_tendsto_condExp
    (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (hα : IsDist α) (hμ : ∀ θ, IsProbabilityMeasure (μ θ))
    (p : ∀ n, Ω → S n) (hp : ∀ n, Measurable (p n))
    (E : ∀ n, Θ → S n → ℝ) (hE : ∀ n θ s, 0 ≤ E n θ s)
    (hmass : ∀ n θ s, μ θ (p n ⁻¹' {s}) = ENNReal.ofReal (E n θ s))
    (ℱ : Filtration ℕ mΩ) (hℱ : ∀ n, ℱ n = MeasurableSpace.comap (p n) inferInstance)
    (hgen : (⨆ n, ℱ n) = mΩ) (θ : Θ) :
    ∀ᵐ x ∂finiteBayesJoint α μ,
      Tendsto (fun n => finiteBayesPosterior α (E n) (p n x.2) θ) atTop
        (𝓝 (((finiteBayesJoint α μ)[finiteBayesClassInd θ |
          MeasurableSpace.comap (Prod.snd : Θ × Ω → Ω) mΩ]) x)) := by
  have := isProbabilityMeasure_finiteBayesJoint hα μ hμ
  have hlevy := tendsto_ae_condExp (μ := finiteBayesJoint α μ)
    (ℱ := finiteBayesFiltration (Θ := Θ) ℱ) (finiteBayesClassInd θ)
  rw [iSup_finiteBayesFiltration ℱ hgen] at hlevy
  have hterm : ∀ᵐ x ∂finiteBayesJoint α μ, ∀ n,
      finiteBayesPosterior α (E n) (p n x.2) θ =
        ((finiteBayesJoint α μ)[finiteBayesClassInd θ |
          finiteBayesFiltration ℱ n]) x := by
    apply ae_all_iff.2
    intro n
    rw [finiteBayesFiltration_eq_observation ℱ p hℱ]
    exact finiteBayesPosterior_ae_eq_condExp α μ hα hμ (p n) (hp n) (E n)
      (hE n) (hmass n) θ
  filter_upwards [hlevy, hterm] with x hx hxterm
  exact hx.congr fun n => (hxterm n).symm

/-- Exact sample decoding makes the terminal conditional class probability
the class indicator, so every full-support posterior concentrates. -/
theorem finiteBayesConcentrates_of_exactDecoder
    (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (hα : IsDist α) (hfs : FullSupport α) (hμ : ∀ θ, IsProbabilityMeasure (μ θ))
    (p : ∀ n, Ω → S n) (hp : ∀ n, Measurable (p n))
    (E : ∀ n, Θ → S n → ℝ) (hE : ∀ n θ s, 0 ≤ E n θ s)
    (hmass : ∀ n θ s, μ θ (p n ⁻¹' {s}) = ENNReal.ofReal (E n θ s))
    (ℱ : Filtration ℕ mΩ) (hℱ : ∀ n, ℱ n = MeasurableSpace.comap (p n) inferInstance)
    (hgen : (⨆ n, ℱ n) = mΩ)
    (D : Ω → Θ) (hD : Measurable D) (hcorrect : ∀ θ, ∀ᵐ ω ∂μ θ, D ω = θ) :
    FiniteBayesConcentrates α μ p E := by
  have := isProbabilityMeasure_finiteBayesJoint hα μ hμ
  let m := MeasurableSpace.comap (Prod.snd : Θ × Ω → Ω) mΩ
  have hm : m ≤ (Prod.instMeasurableSpace : MeasurableSpace (Θ × Ω)) := by
    change MeasurableSpace.comap Prod.snd mΩ ≤ _
    exact measurable_iff_comap_le.1 (@measurable_snd Θ Ω _ mΩ)
  have key : ∀ θ, ∀ᵐ x ∂finiteBayesJoint α μ,
      Tendsto (fun n => finiteBayesPosterior α (E n) (p n x.2) θ) atTop
        (𝓝 (finiteBayesClassInd θ x)) := by
    intro θ
    let C : Set (Θ × Ω) := Prod.snd ⁻¹' (D ⁻¹' {θ})
    let g : Θ × Ω → ℝ := C.indicator fun _ => 1
    have hC : MeasurableSet[m] C := ⟨D ⁻¹' {θ}, hD (measurableSet_singleton θ), rfl⟩
    have hg : StronglyMeasurable[m] g := stronglyMeasurable_const.indicator hC
    have hgint : Integrable g (finiteBayesJoint α μ) :=
      (integrable_const 1).indicator (hm _ hC)
    have hind : finiteBayesClassInd θ =ᵐ[finiteBayesJoint α μ] g := by
      apply (ae_finiteBayesJoint_iff α μ hfs _).2
      intro η
      filter_upwards [hcorrect η] with ω hω
      change (Prod.fst ⁻¹' ({θ} : Set Θ)).indicator (fun _ => (1 : ℝ)) (η, ω) =
        (Prod.snd ⁻¹' D ⁻¹' ({θ} : Set Θ)).indicator (fun _ => (1 : ℝ)) (η, ω)
      by_cases hη : η = θ
      · rw [Set.indicator_of_mem (show (η, ω) ∈ Prod.fst ⁻¹' ({θ} : Set Θ) from hη),
          Set.indicator_of_mem
            (show (η, ω) ∈ Prod.snd ⁻¹' D ⁻¹' ({θ} : Set Θ) from hω.trans hη)]
      · rw [Set.indicator_of_notMem
            (show (η, ω) ∉ Prod.fst ⁻¹' ({θ} : Set Θ) from hη),
          Set.indicator_of_notMem
            (show (η, ω) ∉ Prod.snd ⁻¹' D ⁻¹' ({θ} : Set Θ) from
              fun h => hη (hω.symm.trans h))]
    have hlimit : (finiteBayesJoint α μ)[finiteBayesClassInd θ | m]
        =ᵐ[finiteBayesJoint α μ] finiteBayesClassInd θ :=
      (condExp_congr_ae hind).trans
        ((Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm hg hgint)).trans
          hind.symm)
    filter_upwards [finiteBayesPosterior_tendsto_condExp α μ hα hμ p hp E hE hmass
      ℱ hℱ hgen θ, hlimit] with x hx hxlim
    rwa [hxlim] at hx
  apply (finiteBayesConcentrates_iff_joint α μ p E hfs).2
  filter_upwards [ae_all_iff.2 key] with x hx
  simpa [finiteBayesClassInd, Set.indicator_apply] using hx x.1

/-- Distinct posterior coordinates cannot both converge to one on a
single sample. Their measurable convergence events yield singular carriers.
No martingale or full-support assumption is needed in this direction. -/
theorem pairwise_mutuallySingular_of_finiteBayesConcentrates
    (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (hα : ∀ θ, 0 ≤ α θ)
    (p : ∀ n, Ω → S n) (hp : ∀ n, Measurable (p n))
    (E : ∀ n, Θ → S n → ℝ) (hE : ∀ n θ s, 0 ≤ E n θ s)
    (hconc : FiniteBayesConcentrates α μ p E) :
    Pairwise fun θ η => μ θ ⟂ₘ μ η := by
  let L : Θ → Set Ω := fun θ =>
    {ω | Tendsto (fun n => finiteBayesPosterior α (E n) (p n ω) θ) atTop (𝓝 1)}
  have hL : ∀ θ, MeasurableSet (L θ) := fun θ =>
    measurableSet_tendsto (𝓝 (1 : ℝ))
      (fun n => (measurable_of_finite (fun s => finiteBayesPosterior α (E n) s θ)).comp
        (hp n))
  have hnull : ∀ θ, μ θ (L θ)ᶜ = 0 := fun θ => ae_iff.1 (hconc θ)
  intro θ η hne
  have hsub : L θ ⊆ (L η)ᶜ := by
    intro ω hθ hη
    have hlim : Tendsto
        (fun n => finiteBayesPosterior α (E n) (p n ω) θ +
          finiteBayesPosterior α (E n) (p n ω) η) atTop (𝓝 (1 + 1 : ℝ)) :=
      hθ.add hη
    have hle : (1 + 1 : ℝ) ≤ 1 := le_of_tendsto hlim
      (Eventually.of_forall fun n => finiteBayesPosterior_pair_le_one α (E n)
        hα (hE n) (p n ω) hne)
    norm_num at hle
  refine ⟨(L θ)ᶜ, (hL θ).compl, hnull θ, ?_⟩
  simpa only [compl_compl] using measure_mono_null hsub (hnull η)

end IdExp
