import Formal.CapabilityProfileScores
import Formal.CapabilitySelectedProfiles

/-!
# Limiting profile selection by continuous scalarization

Full profile-space assembly of `prop:capability-profile-scalarization`:
continuous scores defined on the closure of the attainable profile image
select exactly their maximizers, including unattained policy suprema.
-/

namespace IdExp

open Set Filter Topology

noncomputable section

variable {P : Type*} [Nonempty P]

omit [Nonempty P] in
theorem mem_limitingSelectedProfiles_profileScore_iff
    (ℓ : P → ProfileCube) (f : ProfileCube → ℝ)
    (hf : ContinuousOn f (attainableProfileClosure ℓ)) (p : ProfileCube) :
    p ∈ limitingSelectedProfiles ℓ (f ∘ ℓ) ↔
      p ∈ attainableProfileClosure ℓ ∧ f p = objectiveSup (f ∘ ℓ) := by
  constructor
  · intro hp
    obtain ⟨π, hJ, hπ⟩ :=
      (mem_limitingSelectedProfiles_iff_exists_sequence ℓ (f ∘ ℓ)
        (profileScore_bddAbove ℓ f hf) p).1 hp
    have hp' : p ∈ attainableProfileClosure ℓ :=
      mem_closure_of_tendsto hπ (Eventually.of_forall fun n => mem_range_self (π n))
    have hwithin : Tendsto (fun n => ℓ (π n)) atTop
        (𝓝[attainableProfileClosure ℓ] p) := tendsto_nhdsWithin_iff.2
      ⟨hπ, Eventually.of_forall fun n => subset_closure (mem_range_self (π n))⟩
    exact ⟨hp', tendsto_nhds_unique ((hf p hp').tendsto.comp hwithin) hJ⟩
  · rintro ⟨hp, hvalue⟩
    obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.1 hp
    choose π hπ using hq
    have hwithin : Tendsto (fun n => ℓ (π n)) atTop
        (𝓝[attainableProfileClosure ℓ] p) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨?_, Eventually.of_forall fun n => subset_closure (mem_range_self (π n))⟩
      simpa only [hπ] using hlim
    apply (mem_limitingSelectedProfiles_iff_exists_sequence ℓ (f ∘ ℓ)
      (profileScore_bddAbove ℓ f hf) p).2
    refine ⟨π, ?_, hwithin.mono_right nhdsWithin_le_nhds⟩
    simpa only [hvalue, Function.comp_def] using (hf p hp).tendsto.comp hwithin

/-- Continuous profile scores select precisely their maxima on the closed image. -/
theorem limitingSelectedProfiles_eq_profile_argmax
    (ℓ : P → ProfileCube) (f : ProfileCube → ℝ)
    (hf : ContinuousOn f (attainableProfileClosure ℓ)) :
    limitingSelectedProfiles ℓ (f ∘ ℓ) =
      {p | p ∈ attainableProfileClosure ℓ ∧
        ∀ q ∈ attainableProfileClosure ℓ, f q ≤ f p} := by
  ext p
  rw [mem_limitingSelectedProfiles_profileScore_iff ℓ f hf p]
  constructor
  · rintro ⟨hp, heq⟩
    exact ⟨hp, fun q hq => heq ▸ profileScore_le_sup ℓ f hf hq⟩
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (profileScore_le_sup ℓ f hf hp) ?_⟩
    obtain ⟨q, hq, heq⟩ := exists_profileScore_eq_sup ℓ f hf
    change sSup (range (f ∘ ℓ)) ≤ f p
    rw [← heq]
    exact hmax q hq

/-- Extend a score only to write the unrestricted-function version of the theorem.
Its values outside the closed attainable image play no role. -/
def closedProfileScoreExtension (ℓ : P → ProfileCube)
    (f : attainableProfileClosure ℓ → ℝ) (p : ProfileCube) : ℝ := by
  classical
  exact if hp : p ∈ attainableProfileClosure ℓ then f ⟨p, hp⟩ else 0

omit [Nonempty P] in
@[simp] theorem closedProfileScoreExtension_apply (ℓ : P → ProfileCube)
    (f : attainableProfileClosure ℓ → ℝ) (p : attainableProfileClosure ℓ) :
    closedProfileScoreExtension ℓ f p = f p := by
  simp [closedProfileScoreExtension, p.property]

omit [Nonempty P] in
theorem continuousOn_closedProfileScoreExtension (ℓ : P → ProfileCube)
    (f : attainableProfileClosure ℓ → ℝ) (hf : Continuous f) :
    ContinuousOn (closedProfileScoreExtension ℓ f) (attainableProfileClosure ℓ) := by
  apply continuousOn_iff_continuous_domRestrict.2
  simpa only [Set.domRestrict_def, closedProfileScoreExtension_apply] using hf

/-- Literal domain of the paper: `f` is defined only on the closed profile image. -/
theorem limitingSelectedProfiles_closed_score (ℓ : P → ProfileCube)
    (f : attainableProfileClosure ℓ → ℝ) (hf : Continuous f) :
    limitingSelectedProfiles ℓ
      (fun π => f ⟨ℓ π, subset_closure (mem_range_self π)⟩) =
      {p | ∃ hp : p ∈ attainableProfileClosure ℓ,
        ∀ q : attainableProfileClosure ℓ, f q ≤ f ⟨p, hp⟩} := by
  have h := limitingSelectedProfiles_eq_profile_argmax ℓ
    (closedProfileScoreExtension ℓ f) (continuousOn_closedProfileScoreExtension ℓ f hf)
  have heq : closedProfileScoreExtension ℓ f ∘ ℓ =
      fun π => f ⟨ℓ π, subset_closure (mem_range_self π)⟩ := by
    funext π
    exact closedProfileScoreExtension_apply ℓ f ⟨ℓ π, subset_closure (mem_range_self π)⟩
  rw [heq] at h
  rw [h]
  ext p
  constructor
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, fun q => ?_⟩
    simpa [closedProfileScoreExtension, hp, q.property] using hmax q q.property
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, fun q hq => ?_⟩
    simpa [closedProfileScoreExtension, hp, hq] using hmax ⟨q, hq⟩

/-- Positive weighted scores select minimum weighted deficiency profiles. -/
theorem limitingSelectedProfiles_weighted_argmin (ℓ : P → ProfileCube)
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : Summable w) :
    limitingSelectedProfiles ℓ (weightedProfileScore w ∘ ℓ) =
      {p | p ∈ attainableProfileClosure ℓ ∧
        ∀ q ∈ attainableProfileClosure ℓ,
          (∑' j, w j * (p j : ℝ)) ≤ ∑' j, w j * (q j : ℝ)} := by
  rw [limitingSelectedProfiles_eq_profile_argmax ℓ (weightedProfileScore w)
    (continuous_weightedProfileScore hw hsum).continuousOn]
  ext p
  simp only [mem_ofPred_eq, weightedProfileScore, weightedScore, sub_le_sub_iff_left]

theorem profileObjectiveCalibrated_weighted (ℓ : P → ProfileCube)
    {w : ℕ → ℝ} (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (hz : zeroProfile ∈ attainableProfileClosure ℓ) :
    ProfileObjectiveCalibrated ℓ (weightedProfileScore w ∘ ℓ) := by
  intro j ε hε
  obtain ⟨η, hη, hbound⟩ := weightedProfileScore_calibration ℓ hw hsum hz j hε
  exact ⟨η, hη, fun π hπ => hbound π hπ⟩

/-- No bounded real objective can calibrate a family whose profile closure misses zero. -/
theorem not_profileObjectiveCalibrated_of_zero_not_mem_closure
    (ℓ : P → ProfileCube) (J : P → ℝ) (hJ : BddAbove (range J))
    (hz : zeroProfile ∉ attainableProfileClosure ℓ) :
    ¬ ProfileObjectiveCalibrated ℓ J := by
  intro hc
  have heq := (profileObjectiveCalibrated_iff_limitingSelectedProfiles_eq_singleton
    ℓ J hJ).1 hc
  have hmem : zeroProfile ∈ limitingSelectedProfiles ℓ J := by simp [heq]
  exact hz (limitingSelectedProfiles_subset_closure_range ℓ J hmem)

/-- For positive summable weights, approachable zero is both necessary and sufficient. -/
theorem profileObjectiveCalibrated_weighted_iff (ℓ : P → ProfileCube)
    {w : ℕ → ℝ} (hw : ∀ j, 0 < w j) (hsum : Summable w) :
    ProfileObjectiveCalibrated ℓ (weightedProfileScore w ∘ ℓ) ↔
      zeroProfile ∈ attainableProfileClosure ℓ := by
  constructor
  · intro hc
    by_contra hz
    exact not_profileObjectiveCalibrated_of_zero_not_mem_closure ℓ
      (weightedProfileScore w ∘ ℓ)
      (profileScore_bddAbove ℓ _
        (continuous_weightedProfileScore (fun j => (hw j).le) hsum).continuousOn)
      hz hc
  · exact profileObjectiveCalibrated_weighted ℓ hw hsum

end
end IdExp
