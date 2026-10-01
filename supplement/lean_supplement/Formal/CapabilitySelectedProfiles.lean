import Formal.ProfileSpace

/-!
# Limiting objective selection in the countable native profile cube

This module proves `thm:capability-selected-profiles` from the shared paper
supplement. The feasible family is an arbitrary nonempty type, its profile map
is arbitrary, and the real objective is only assumed bounded above. In
particular no topology on the feasible family, continuity of the objective,
profile factorization, or attained optimum is required.

`limitingSelectedProfiles` is literally the intersection, over positive regret
tolerances, of the closures of the selected profile images in `ProfileCube`.
The cube carries its existing product topology. Its coordinates can be the
rich native eventual deficiencies without imposing any extra regularity on
their dependence on policy.
-/

namespace IdExp

open Set Filter Topology

variable {P : Type*}

/-- The finite supremum used for a bounded-above real objective. -/
noncomputable def objectiveSup (J : P → ℝ) : ℝ := sSup (Set.range J)

/-- All feasible policies with objective regret at most `η`. -/
def selectedPolicySet (J : P → ℝ) (η : ℝ) : Set P :=
  {π | objectiveSup J - J π ≤ η}

/-- Closure of the joint eventual profiles of the policies selected at `η`. -/
def closedSelectedProfiles (ℓ : P → ProfileCube) (J : P → ℝ) (η : ℝ) :
    Set ProfileCube := closure (ℓ '' selectedPolicySet J η)

/-- The limiting selected profile set, with every positive tolerance retained. -/
def limitingSelectedProfiles (ℓ : P → ProfileCube) (J : P → ℝ) :
    Set ProfileCube := ⋂ (η : ℝ) (_ : 0 < η), closedSelectedProfiles ℓ J η

/-- Small objective regret uniformly forces small error on each fixed target. -/
def ProfileObjectiveCalibrated (ℓ : P → ProfileCube) (J : P → ℝ) : Prop :=
  ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∃ η > 0,
    ∀ π ∈ selectedPolicySet J η, (ℓ π j : ℝ) < ε

theorem mem_limitingSelectedProfiles_iff (ℓ : P → ProfileCube) (J : P → ℝ)
    (p : ProfileCube) :
    p ∈ limitingSelectedProfiles ℓ J ↔
      ∀ η > 0, p ∈ closedSelectedProfiles ℓ J η := by
  simp [limitingSelectedProfiles]

theorem objective_le_objectiveSup (J : P → ℝ) (hJ : BddAbove (Set.range J))
    (π : P) : J π ≤ objectiveSup J :=
  le_csSup hJ (Set.mem_range_self π)

theorem objectiveRegret_nonneg (J : P → ℝ) (hJ : BddAbove (Set.range J))
    (π : P) : 0 ≤ objectiveSup J - J π :=
  sub_nonneg.mpr (objective_le_objectiveSup J hJ π)

theorem selectedPolicySet_mono (J : P → ℝ) {η η' : ℝ} (h : η ≤ η') :
    selectedPolicySet J η ⊆ selectedPolicySet J η' :=
  fun _ hπ => hπ.trans h

theorem closedSelectedProfiles_mono (ℓ : P → ProfileCube) (J : P → ℝ)
    {η η' : ℝ} (h : η ≤ η') :
    closedSelectedProfiles ℓ J η ⊆ closedSelectedProfiles ℓ J η' :=
  closure_mono (Set.image_mono (selectedPolicySet_mono J h))

theorem selectedPolicySet_nonempty [Nonempty P] (J : P → ℝ)
    (_hJ : BddAbove (Set.range J)) {η : ℝ} (hη : 0 < η) :
    (selectedPolicySet J η).Nonempty := by
  have hlt : objectiveSup J - η < sSup (Set.range J) := by
    change objectiveSup J - η < objectiveSup J
    linarith
  obtain ⟨y, ⟨π, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (Set.range_nonempty J) hlt
  exact ⟨π, by dsimp [selectedPolicySet]; linarith⟩

theorem closedSelectedProfiles_nonempty [Nonempty P] (ℓ : P → ProfileCube)
    (J : P → ℝ) (hJ : BddAbove (Set.range J)) {η : ℝ} (hη : 0 < η) :
    (closedSelectedProfiles ℓ J η).Nonempty :=
  ((selectedPolicySet_nonempty J hJ hη).image ℓ).closure

theorem isClosed_closedSelectedProfiles (ℓ : P → ProfileCube) (J : P → ℝ)
    (η : ℝ) : IsClosed (closedSelectedProfiles ℓ J η) := isClosed_closure

theorem isCompact_closedSelectedProfiles (ℓ : P → ProfileCube) (J : P → ℝ)
    (η : ℝ) : IsCompact (closedSelectedProfiles ℓ J η) := isClosed_closure.isCompact

theorem isCompact_limitingSelectedProfiles (ℓ : P → ProfileCube) (J : P → ℝ) :
    IsCompact (limitingSelectedProfiles ℓ J) :=
  (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closure).isCompact

/-- The limiting selection exists even if the supremum or zero profile is unattained. -/
theorem limitingSelectedProfiles_nonempty [Nonempty P] (ℓ : P → ProfileCube)
    (J : P → ℝ) (hJ : BddAbove (Set.range J)) :
    (limitingSelectedProfiles ℓ J).Nonempty := by
  let B : {η : ℝ // 0 < η} → Set ProfileCube :=
    fun η => closedSelectedProfiles ℓ J η
  have : Nonempty {η : ℝ // 0 < η} := ⟨⟨1, zero_lt_one⟩⟩
  have hdir : Directed (· ⊇ ·) B := by
    intro a b
    refine ⟨⟨min a.val b.val, lt_min a.property b.property⟩, ?_, ?_⟩
    · exact closedSelectedProfiles_mono ℓ J (min_le_left _ _)
    · exact closedSelectedProfiles_mono ℓ J (min_le_right _ _)
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed B
    hdir (fun η => closedSelectedProfiles_nonempty ℓ J hJ η.property)
    (fun η => isCompact_closedSelectedProfiles ℓ J η)
    (fun η => isClosed_closedSelectedProfiles ℓ J η)
  refine ⟨p, (mem_limitingSelectedProfiles_iff ℓ J p).2 ?_⟩
  intro η hη
  exact Set.mem_iInter.mp hp ⟨η, hη⟩

/-- Vanishing regret bounds suffice for convergence to the objective supremum. -/
theorem tendsto_objective_of_regret_le (J : P → ℝ) (hJ : BddAbove (Set.range J))
    {π : ℕ → P} {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hπ : ∀ n, objectiveSup J - J (π n) ≤ η n) :
    Tendsto (fun n => J (π n)) atTop (𝓝 (objectiveSup J)) := by
  have hg : Tendsto (fun n => objectiveSup J - J (π n)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun n => objectiveRegret_nonneg J hJ (π n)))
      (Eventually.of_forall hπ) hη
  simpa using hg.const_sub (objectiveSup J)


/-- Every limit of profiles with scores approaching the supremum belongs to
all the closed selected images. -/
theorem mem_limitingSelectedProfiles_of_sequence (ℓ : P → ProfileCube) (J : P → ℝ)
    {π : ℕ → P} {p : ProfileCube}
    (hJπ : Tendsto (fun n => J (π n)) atTop (𝓝 (objectiveSup J)))
    (hℓπ : Tendsto (fun n => ℓ (π n)) atTop (𝓝 p)) :
    p ∈ limitingSelectedProfiles ℓ J := by
  apply (mem_limitingSelectedProfiles_iff ℓ J p).2
  intro η hη
  have hg : Tendsto (fun n => objectiveSup J - J (π n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := objectiveSup J)).sub hJπ
  have he : ∀ᶠ n in atTop, objectiveSup J - J (π n) < η :=
    (tendsto_order.1 hg).2 η hη
  apply (isClosed_closedSelectedProfiles ℓ J η).mem_of_tendsto hℓπ
  filter_upwards [he] with n hn
  exact subset_closure ⟨π n, hn.le, rfl⟩

/-- Exact sequential characterization, without an attained objective optimum
or any continuity assumptions on the objective or profile map. -/
theorem mem_limitingSelectedProfiles_iff_exists_sequence (ℓ : P → ProfileCube)
    (J : P → ℝ) (hJ : BddAbove (Set.range J)) (p : ProfileCube) :
    p ∈ limitingSelectedProfiles ℓ J ↔
      ∃ π : ℕ → P,
        Tendsto (fun n => J (π n)) atTop (𝓝 (objectiveSup J)) ∧
        Tendsto (fun n => ℓ (π n)) atTop (𝓝 p) := by
  constructor
  · intro hp
    let : MetricSpace ProfileCube := TopologicalSpace.metrizableSpaceMetric ProfileCube
    let η : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
    have hηpos : ∀ n, 0 < η n := by intro n; dsimp [η]; positivity
    have hη : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hex : ∀ n, ∃ π ∈ selectedPolicySet J (η n), dist (ℓ π) p < η n := by
      intro n
      have hp' : p ∈ closure (ℓ '' selectedPolicySet J (η n)) :=
        (mem_limitingSelectedProfiles_iff ℓ J p).1 hp (η n) (hηpos n)
      obtain ⟨q, ⟨π, hπ, rfl⟩, hq⟩ :=
        Metric.mem_closure_iff.1 hp' (η n) (hηpos n)
      exact ⟨π, hπ, by simpa [dist_comm] using hq⟩
    choose π hπ hdist using hex
    refine ⟨π, tendsto_objective_of_regret_le J hJ hη hπ, ?_⟩
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le) hη
  · rintro ⟨π, hJπ, hℓπ⟩
    exact mem_limitingSelectedProfiles_of_sequence ℓ J hJπ hℓπ

/-- Calibration forces every limiting selected coordinate to be zero. -/
theorem eq_zeroProfile_of_mem_limitingSelectedProfiles_of_calibrated
    (ℓ : P → ProfileCube) (J : P → ℝ) (hc : ProfileObjectiveCalibrated ℓ J)
    {p : ProfileCube} (hp : p ∈ limitingSelectedProfiles ℓ J) : p = zeroProfile := by
  funext j
  apply Subtype.ext
  change (p j : ℝ) = 0
  apply le_antisymm _ (p j).property.1
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨η, hη, hbound⟩ := hc j ε hε
  have hclosed : IsClosed {q : ProfileCube | (q j : ℝ) ≤ ε} :=
    isClosed_le (continuous_subtype_val.comp (continuous_apply j)) continuous_const
  have hsub : closedSelectedProfiles ℓ J η ⊆ {q : ProfileCube | (q j : ℝ) ≤ ε} := by
    apply closure_minimal _ hclosed
    rintro q ⟨π, hπ, rfl⟩
    exact (hbound π hπ).le
  simpa using hsub ((mem_limitingSelectedProfiles_iff ℓ J p).1 hp η hη)

/-- Native calibration is exactly singleton-zero limiting selection. This
concerns eventual profiles, with no common finite acquisition deadline. -/
theorem profileObjectiveCalibrated_iff_limitingSelectedProfiles_eq_singleton
    [Nonempty P] (ℓ : P → ProfileCube) (J : P → ℝ)
    (hJ : BddAbove (Set.range J)) :
    ProfileObjectiveCalibrated ℓ J ↔ limitingSelectedProfiles ℓ J = {zeroProfile} := by
  constructor
  · intro hc
    apply Set.Subset.antisymm
    · intro p hp
      exact Set.mem_singleton_iff.2
        (eq_zeroProfile_of_mem_limitingSelectedProfiles_of_calibrated ℓ J hc hp)
    · obtain ⟨p, hp⟩ := limitingSelectedProfiles_nonempty ℓ J hJ
      have heq := eq_zeroProfile_of_mem_limitingSelectedProfiles_of_calibrated ℓ J hc hp
      simpa [heq] using Set.singleton_subset_iff.2 hp
  · intro hzero
    by_contra hc
    unfold ProfileObjectiveCalibrated at hc
    push Not at hc
    obtain ⟨j, ε, hε, hbad⟩ := hc
    let η : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
    have hηpos : ∀ n, 0 < η n := by intro n; dsimp [η]; positivity
    have hη : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    choose π hπ hbadπ using fun n => hbad (η n) (hηpos n)
    have hscore := tendsto_objective_of_regret_le J hJ hη hπ
    obtain ⟨p, _, φ, hφ, hlim⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set ProfileCube)).tendsto_subseq
        (fun n => Set.mem_univ (ℓ (π n)))
    have hp : p ∈ limitingSelectedProfiles ℓ J :=
      mem_limitingSelectedProfiles_of_sequence ℓ J (hscore.comp hφ.tendsto_atTop) hlim
    have hpzero : p = zeroProfile := by simpa [hzero] using hp
    have hcoord : Tendsto (fun n => (ℓ (π (φ n)) j : ℝ)) atTop (𝓝 (p j : ℝ)) :=
      tendsto_subtype_rng.mp ((tendsto_pi_nhds.mp hlim) j)
    have hle : ε ≤ (p j : ℝ) :=
      ge_of_tendsto hcoord (Eventually.of_forall (fun n => hbadπ (φ n)))
    rw [hpzero] at hle
    exact (not_le_of_gt hε) hle

/-- Limiting selected profiles stay in the closure of all feasible profiles. -/
theorem limitingSelectedProfiles_subset_closure_range
    (ℓ : P → ProfileCube) (J : P → ℝ) :
    limitingSelectedProfiles ℓ J ⊆ closure (Set.range ℓ) := by
  intro p hp
  have hp' := (mem_limitingSelectedProfiles_iff ℓ J p).1 hp 1 zero_lt_one
  exact closure_mono (Set.image_subset_range ℓ (selectedPolicySet J 1)) hp'

/-- All conclusions of the paper's limiting selection and calibration theorem
on its actual countable compact cube. The feasible family need not be compact,
and neither its objective supremum nor a limiting profile need be attained. -/
theorem capability_selected_profiles [Nonempty P]
    (ℓ : P → ProfileCube) (J : P → ℝ) (hJ : BddAbove (Set.range J)) :
    (limitingSelectedProfiles ℓ J).Nonempty ∧
      IsCompact (limitingSelectedProfiles ℓ J) ∧
      (∀ p, p ∈ limitingSelectedProfiles ℓ J ↔
        ∃ π : ℕ → P,
          Tendsto (fun n => J (π n)) atTop (𝓝 (objectiveSup J)) ∧
          Tendsto (fun n => ℓ (π n)) atTop (𝓝 p)) ∧
      (ProfileObjectiveCalibrated ℓ J ↔
        limitingSelectedProfiles ℓ J = {zeroProfile}) :=
  ⟨limitingSelectedProfiles_nonempty ℓ J hJ,
    isCompact_limitingSelectedProfiles ℓ J,
    mem_limitingSelectedProfiles_iff_exists_sequence ℓ J hJ,
    profileObjectiveCalibrated_iff_limitingSelectedProfiles_eq_singleton ℓ J hJ⟩

end IdExp
