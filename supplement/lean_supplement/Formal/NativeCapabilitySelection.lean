import Formal.CapabilitySelectedProfiles
import Formal.CapabilityProfileScores
import Formal.StrictFinitaryRegularity

/-!
# Objective selection and calibration for actual native records

The rich profile consists of eventual deficiencies to actual randomized policy
records. The target horizon and family index are encoded with `Nat.unpair`.
Uniform target density transfers calibration to every native record, before
specializing the compact-cube selection theorem and positive weighted score.
Direct controlled-prefix-behavior wrappers discharge response validity.
-/

namespace IdExp

open Set Filter Topology

noncomputable section

variable {A O Θ P : Type*} [Fintype A] [Fintype O]
    [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- The rich countable profile, retaining actual randomized native records. -/
def nativeCapabilityProfile (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (ρ : ℕ → ℕ → ValidCausalPolicy A O) (π : ValidCausalPolicy A O) : ProfileCube :=
  fun j =>
    let n := (Nat.unpair j).1
    let k := (Nat.unpair j).2
    let T := causalFiniteExperiment (ρ n k).1 Qs n
    ⟨eventualLoss Qs π T,
      eventualLoss_nonneg Qs hQ π T (causalFiniteExperiment_valid _ (ρ n k).2 Qs hQ n),
      eventualLoss_le_one Qs hQ π T (causalFiniteExperiment_valid _ (ρ n k).2 Qs hQ n)⟩

set_option maxHeartbeats 1200000 in
@[simp] theorem nativeCapabilityProfile_pair (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (ρ : ℕ → ℕ → ValidCausalPolicy A O) (π : ValidCausalPolicy A O) (n k : ℕ) :
    (nativeCapabilityProfile Qs hQ ρ π (Nat.pair n k) : ℝ) =
      eventualLoss Qs π (causalFiniteExperiment (ρ n k).1 Qs n) := by
  change (fun nk : ℕ × ℕ => eventualLoss Qs π
    (causalFiniteExperiment (ρ nk.1 nk.2).1 Qs nk.1)) (Nat.unpair (Nat.pair n k)) = _
  rw [Nat.unpair_pair]

/-- Target perturbation passes to eventual loss through its actual time limit;
no interchange of the world supremum with that limit is used. -/
theorem eventualLoss_le_add_of_rowTV_target {Y : Type*} [Fintype Y]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (T U : FiniteExperiment Θ Y)
    (hT : IsFiniteExperiment T) (hU : IsFiniteExperiment U) (r : ℝ)
    (hrow : ∀ θ, finiteTV (T θ) (U θ) ≤ r) :
    eventualLoss Qs π U ≤ eventualLoss Qs π T + r := by
  apply le_of_tendsto_of_tendsto (tendsto_eventualLoss Qs hQ π U hU)
    ((tendsto_eventualLoss Qs hQ π T hT).add_const r)
  apply Eventually.of_forall
  intro t
  have h := (abs_le.1 (abs_finiteDeficiency_sub_le_of_rowTV_target
    (causalFiniteExperiment π.1 Qs t) T U
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) hT hU r hrow)).1
  linarith

/-- Calibration against every fixed native randomized record on the declared
feasible family. The tolerance may depend on the target and its accuracy. -/
def NativeRecordObjectiveCalibrated (Qs : Θ → CausalResponse A O)
    (F : P → ValidCausalPolicy A O) (J : P → ℝ) : Prop :=
  ∀ (σ : ValidCausalPolicy A O) (n : ℕ) (ε : ℝ), 0 < ε →
    ∃ η > 0, ∀ a ∈ selectedPolicySet J η,
      eventualLoss Qs (F a) (causalFiniteExperiment σ.1 Qs n) < ε

/-- Uniform density makes rich-coordinate calibration exactly calibration for
every finite native record, including randomized target policies. -/
theorem nativeRecordObjectiveCalibrated_iff_profile
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (ρ : ℕ → ℕ → ValidCausalPolicy A O)
    (hρ : DenseRecordFamily Qs (fun n k => causalFiniteExperiment (ρ n k).1 Qs n))
    (F : P → ValidCausalPolicy A O) (J : P → ℝ) :
    NativeRecordObjectiveCalibrated Qs F J ↔
      ProfileObjectiveCalibrated (nativeCapabilityProfile Qs hQ ρ ∘ F) J := by
  constructor
  · intro hc j ε hε
    exact hc (ρ (Nat.unpair j).1 (Nat.unpair j).2) (Nat.unpair j).1 ε hε
  · intro hc σ n ε hε
    obtain ⟨k, hk⟩ := hρ.2 σ n (ε / 3) (by positivity)
    obtain ⟨η, hη, hsmall⟩ := hc (Nat.pair n k) (ε / 3) (by positivity)
    refine ⟨η, hη, fun a ha => ?_⟩
    have hs : eventualLoss Qs (F a) (causalFiniteExperiment (ρ n k).1 Qs n) < ε / 3 := by
      simpa only [Function.comp_apply, nativeCapabilityProfile_pair] using hsmall a ha
    have hb := eventualLoss_le_add_of_rowTV_target Qs hQ (F a)
      (causalFiniteExperiment (ρ n k).1 Qs n) (causalFiniteExperiment σ.1 Qs n)
      (hρ.1 n k) (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ n) (ε / 3) hk
    linarith

/-- The full selection theorem on actual native profiles and an arbitrary
nonempty feasible family. Boundedness of the real objective is the only
objective assumption; its supremum and the zero profile may be unattained. -/
theorem native_capability_selected_profiles [Nonempty P]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (ρ : ℕ → ℕ → ValidCausalPolicy A O)
    (hρ : DenseRecordFamily Qs (fun n k => causalFiniteExperiment (ρ n k).1 Qs n))
    (F : P → ValidCausalPolicy A O) (J : P → ℝ) (hJ : BddAbove (range J)) :
    let ℓ := nativeCapabilityProfile Qs hQ ρ ∘ F
    (limitingSelectedProfiles ℓ J).Nonempty ∧
      IsCompact (limitingSelectedProfiles ℓ J) ∧
      (∀ p, p ∈ limitingSelectedProfiles ℓ J ↔
        ∃ a : ℕ → P,
          Tendsto (fun n => J (a n)) atTop (𝓝 (objectiveSup J)) ∧
          Tendsto (fun n => ℓ (a n)) atTop (𝓝 p)) ∧
      (NativeRecordObjectiveCalibrated Qs F J ↔
        limitingSelectedProfiles ℓ J = {zeroProfile}) := by
  dsimp only
  obtain ⟨hne, hc, hs, hcal⟩ := capability_selected_profiles
    (nativeCapabilityProfile Qs hQ ρ ∘ F) J hJ
  exact ⟨hne, hc, hs, (nativeRecordObjectiveCalibrated_iff_profile Qs hQ ρ hρ F J).trans hcal⟩

/-- Positive summable native weights calibrate all fixed native records as
soon as zero is approachable in the feasible profile family. -/
theorem weighted_nativeRecordObjectiveCalibrated [Nonempty P]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (ρ : ℕ → ℕ → ValidCausalPolicy A O)
    (hρ : DenseRecordFamily Qs (fun n k => causalFiniteExperiment (ρ n k).1 Qs n))
    (F : P → ValidCausalPolicy A O) {w : ℕ → ℝ}
    (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (hz : zeroProfile ∈ attainableProfileClosure (nativeCapabilityProfile Qs hQ ρ ∘ F)) :
    NativeRecordObjectiveCalibrated Qs F
      (weightedProfileScore w ∘ nativeCapabilityProfile Qs hQ ρ ∘ F) := by
  apply (nativeRecordObjectiveCalibrated_iff_profile Qs hQ ρ hρ F _).2
  intro j ε hε
  exact weightedProfileScore_calibration (nativeCapabilityProfile Qs hQ ρ ∘ F)
    hw hsum hz j hε

/-- Zero of the rich profile is exactly native sufficiency, without an attained
full-revelation assumption. -/
theorem nativeCapabilityProfile_eq_zero_iff
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (ρ : ℕ → ℕ → ValidCausalPolicy A O)
    (hρ : DenseRecordFamily Qs (fun n k => causalFiniteExperiment (ρ n k).1 Qs n))
    (π : ValidCausalPolicy A O) :
    nativeCapabilityProfile Qs hQ ρ π = zeroProfile ↔ CausalNativelySufficient Qs π := by
  rw [causalNativelySufficient_iff_finitarilyGreatest Qs hQ π]
  constructor
  · intro hz σ
    apply (causalFinitaryDominates_iff_eventualLoss Qs hQ _ hρ π σ).2
    intro n k
    have hp := congrArg (fun p : ProfileCube => (p (Nat.pair n k) : ℝ)) hz
    have heq : eventualLoss Qs π (causalFiniteExperiment (ρ n k).1 Qs n) = 0 := by
      simpa only [nativeCapabilityProfile_pair, zeroProfile] using hp
    rw [heq]
    exact eventualLoss_nonneg Qs hQ σ _ (hρ.1 n k)
  · intro hgreat
    funext j
    apply Subtype.ext
    change eventualLoss Qs π
      (causalFiniteExperiment (ρ (Nat.unpair j).1 (Nat.unpair j).2).1 Qs (Nat.unpair j).1) = 0
    apply le_antisymm _ (eventualLoss_nonneg Qs hQ π _
      (hρ.1 (Nat.unpair j).1 (Nat.unpair j).2))
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨t, ht⟩ := hgreat (ρ (Nat.unpair j).1 (Nat.unpair j).2) (Nat.unpair j).1 ε hε
    exact (eventualLoss_le Qs hQ π _
      (hρ.1 (Nat.unpair j).1 (Nat.unpair j).2) t).trans (by simpa using (ht t le_rfl).le)

/-- Rich native profiles stated on the canonical controlled-prefix behaviors. -/
def causalBehaviorNativeCapabilityProfile (ps : Θ → CausalBehavior A O)
    (ρ : ℕ → ℕ → ValidCausalPolicy A O) : ValidCausalPolicy A O → ProfileCube :=
  nativeCapabilityProfile (causalBehaviorResponsePresentation ps)
    (causalBehaviorResponsePresentation_valid ps) ρ

/-- Each coordinate is literally the infimum of actual behavior-record deficiencies. -/
theorem causalBehaviorNativeCapabilityProfile_apply (ps : Θ → CausalBehavior A O)
    (ρ : ℕ → ℕ → ValidCausalPolicy A O) (π : ValidCausalPolicy A O) (j : ℕ) :
    (causalBehaviorNativeCapabilityProfile ps ρ π j : ℝ) =
      ⨅ t : ℕ, finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps t)
        (causalBehaviorFiniteExperiment
          (ρ (Nat.unpair j).1 (Nat.unpair j).2).1 ps (Nat.unpair j).1) := by
  simp only [causalBehaviorNativeCapabilityProfile, nativeCapabilityProfile, eventualLoss,
    causalBehaviorFiniteExperiment_eq_toResponse]

/-- Native calibration with the semantic primitive of controlled-prefix behaviors. -/
def CausalBehaviorNativeRecordObjectiveCalibrated (ps : Θ → CausalBehavior A O)
    (F : P → ValidCausalPolicy A O) (J : P → ℝ) : Prop :=
  ∀ (σ : ValidCausalPolicy A O) (n : ℕ) (ε : ℝ), 0 < ε →
    ∃ η > 0, ∀ a ∈ selectedPolicySet J η,
      (⨅ t : ℕ, finiteDeficiency (causalBehaviorFiniteExperiment (F a).1 ps t)
        (causalBehaviorFiniteExperiment σ.1 ps n)) < ε

omit [Nonempty Θ] in
theorem causalBehaviorNativeRecordObjectiveCalibrated_iff_raw
    (ps : Θ → CausalBehavior A O) (F : P → ValidCausalPolicy A O) (J : P → ℝ) :
    CausalBehaviorNativeRecordObjectiveCalibrated ps F J ↔
      NativeRecordObjectiveCalibrated (causalBehaviorResponsePresentation ps) F J := by
  simp only [CausalBehaviorNativeRecordObjectiveCalibrated, NativeRecordObjectiveCalibrated,
    eventualLoss, causalBehaviorFiniteExperiment_eq_toResponse]

/-- The paper's selection theorem directly on controlled behaviors. The rich
native family is supplied by the checked density construction; no response
validity, objective continuity, or attainability premise remains to discharge. -/
theorem exists_causalBehavior_native_capability_selected_profiles [Nonempty P]
    (ps : Θ → CausalBehavior A O) (F : P → ValidCausalPolicy A O)
    (J : P → ℝ) (hJ : BddAbove (range J)) :
    ∃ ρ : ℕ → ℕ → ValidCausalPolicy A O,
      (∀ (σ : ValidCausalPolicy A O) (n : ℕ) (ε : ℝ), 0 < ε →
        ∃ k, ∀ θ, finiteTV (causalBehaviorFiniteExperiment (ρ n k).1 ps n θ)
          (causalBehaviorFiniteExperiment σ.1 ps n θ) ≤ ε) ∧
      let ℓ := causalBehaviorNativeCapabilityProfile ps ρ ∘ F
      (limitingSelectedProfiles ℓ J).Nonempty ∧
        IsCompact (limitingSelectedProfiles ℓ J) ∧
        (∀ p, p ∈ limitingSelectedProfiles ℓ J ↔
          ∃ a : ℕ → P,
            Tendsto (fun n => J (a n)) atTop (𝓝 (objectiveSup J)) ∧
            Tendsto (fun n => ℓ (a n)) atTop (𝓝 p)) ∧
        (CausalBehaviorNativeRecordObjectiveCalibrated ps F J ↔
          limitingSelectedProfiles ℓ J = {zeroProfile}) := by
  obtain ⟨ρ, hρ⟩ := exists_densePolicyRecordFamily
    (causalBehaviorResponsePresentation ps) (causalBehaviorResponsePresentation_valid ps)
  refine ⟨ρ, ?_, ?_⟩
  · simpa only [causalBehaviorFiniteExperiment_eq_toResponse] using hρ.2
  · simpa only [causalBehaviorNativeCapabilityProfile,
      causalBehaviorNativeRecordObjectiveCalibrated_iff_raw] using
      native_capability_selected_profiles (causalBehaviorResponsePresentation ps)
        (causalBehaviorResponsePresentation_valid ps) ρ hρ F J hJ

/-- The weighted native calibration consequence on actual controlled behaviors,
for a rich family furnished independently of the weights. -/
theorem exists_causalBehavior_weighted_native_calibration [Nonempty P]
    (ps : Θ → CausalBehavior A O) (F : P → ValidCausalPolicy A O) :
    ∃ ρ : ℕ → ℕ → ValidCausalPolicy A O,
      (∀ (σ : ValidCausalPolicy A O) (n : ℕ) (ε : ℝ), 0 < ε →
        ∃ k, ∀ θ, finiteTV (causalBehaviorFiniteExperiment (ρ n k).1 ps n θ)
          (causalBehaviorFiniteExperiment σ.1 ps n θ) ≤ ε) ∧
      ∀ w : ℕ → ℝ, (∀ j, 0 < w j) → Summable w →
        zeroProfile ∈ attainableProfileClosure (causalBehaviorNativeCapabilityProfile ps ρ ∘ F) →
        CausalBehaviorNativeRecordObjectiveCalibrated ps F
          (weightedProfileScore w ∘ causalBehaviorNativeCapabilityProfile ps ρ ∘ F) := by
  obtain ⟨ρ, hρ⟩ := exists_densePolicyRecordFamily
    (causalBehaviorResponsePresentation ps) (causalBehaviorResponsePresentation_valid ps)
  refine ⟨ρ, ?_, fun w hw hsum hz => ?_⟩
  · simpa only [causalBehaviorFiniteExperiment_eq_toResponse] using hρ.2
  · apply (causalBehaviorNativeRecordObjectiveCalibrated_iff_raw ps F _).2
    exact weighted_nativeRecordObjectiveCalibrated (causalBehaviorResponsePresentation ps)
      (causalBehaviorResponsePresentation_valid ps) ρ hρ F hw hsum hz

/-- In the direct semantic representation, zero rich profile means native
sufficiency. Density is stated only using actual behavior-record laws. -/
theorem causalBehaviorNativeCapabilityProfile_eq_zero_iff
    (ps : Θ → CausalBehavior A O) (ρ : ℕ → ℕ → ValidCausalPolicy A O)
    (hρ : ∀ (σ : ValidCausalPolicy A O) (n : ℕ) (ε : ℝ), 0 < ε →
      ∃ k, ∀ θ, finiteTV (causalBehaviorFiniteExperiment (ρ n k).1 ps n θ)
        (causalBehaviorFiniteExperiment σ.1 ps n θ) ≤ ε)
    (π : ValidCausalPolicy A O) :
    causalBehaviorNativeCapabilityProfile ps ρ π = zeroProfile ↔
      CausalBehaviorNativelySufficient ps π := by
  rw [causalBehaviorNativelySufficient_iff_raw]
  apply nativeCapabilityProfile_eq_zero_iff
  constructor
  · intro n k
    exact causalFiniteExperiment_valid _ (ρ n k).2 _
      (causalBehaviorResponsePresentation_valid ps) n
  · simpa only [causalBehaviorFiniteExperiment_eq_toResponse] using hρ

/-- The direct rich-profile coordinate is also the limit of the actual
nonincreasing finite-time deficiency sequence. -/
theorem tendsto_causalBehaviorNativeCapabilityProfile
    (ps : Θ → CausalBehavior A O) (ρ : ℕ → ℕ → ValidCausalPolicy A O)
    (π : ValidCausalPolicy A O) (j : ℕ) :
    Tendsto (fun t => finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps t)
      (causalBehaviorFiniteExperiment
        (ρ (Nat.unpair j).1 (Nat.unpair j).2).1 ps (Nat.unpair j).1)) atTop
      (𝓝 (causalBehaviorNativeCapabilityProfile ps ρ π j : ℝ)) := by
  simpa only [causalBehaviorNativeCapabilityProfile, nativeCapabilityProfile,
    causalBehaviorFiniteExperiment_eq_toResponse] using
    tendsto_eventualLoss (causalBehaviorResponsePresentation ps)
      (causalBehaviorResponsePresentation_valid ps) π _
      (causalFiniteExperiment_valid _ (ρ (Nat.unpair j).1 (Nat.unpair j).2).2 _
        (causalBehaviorResponsePresentation_valid ps) (Nat.unpair j).1)

end
end IdExp
