/-
Infrastructure for the retained finite-POMDP `pathLaw_identification` theorem
in `Statements.lean`, using initial-observation histories. The former PDF
numbering is archived in `Formal/STATEMENTS.md`; current claim support belongs
in `Formal/PAPER_SUPPORT.json`.

Proof route. (1) ⇒ (3): the posterior at horizon `T` is the conditional
expectation of the class indicator given the length-`T` prefix σ-algebra;
Lévy's upward theorem sends it to the conditional expectation given the full
trajectory σ-algebra, which mutual singularity collapses to the class
indicator itself.  (3) ⇒ (2): the uniform prior is a full-support
distribution.  (2) ⇒ (1): two posteriors cannot both tend to one along the
same trajectory.

This file: the Bayesian joint law as an explicit finite sum, its probability
instance, the prefix filtration on `Θ × Ω∞`, and measurability of the
posterior process.
-/
import Formal.Nonneg
import Formal.PathLaw
import Mathlib.Probability.Martingale.Convergence

set_option linter.unusedSectionVars false

namespace IdExp

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Fintype Θ]
  [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Θ]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [MeasurableSingletonClass Θ]

/-! ### The joint law as a finite sum -/

theorem jointLaw_apply (α : Θ → ℝ) {μfam : Θ → Measure (Traj A O)}
    (hprob : ∀ θ, IsProbabilityMeasure (μfam θ))
    {S : Set (Θ × Traj A O)} (hS : MeasurableSet S) :
    jointLaw α μfam S = ∑ θ, ENNReal.ofReal (α θ) * μfam θ (Prod.mk θ ⁻¹' S) := by
  rw [jointLaw, Measure.sum_apply _ hS, tsum_fintype]
  refine Finset.sum_congr rfl fun θ _ => ?_
  have := hprob θ
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hS]

theorem isProbabilityMeasure_jointLaw {α : Θ → ℝ} (hα : IsDist α)
    {μfam : Θ → Measure (Traj A O)} (hprob : ∀ θ, IsProbabilityMeasure (μfam θ)) :
    IsProbabilityMeasure (jointLaw α μfam) := by
  constructor
  rw [jointLaw_apply α hprob MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun θ _ => hα.1 θ), hα.2, ENNReal.ofReal_one]

/-! ### The prefix filtration on `Θ × Ω∞` -/

/-- Truncating a history to its first `n` steps. -/
def histTrunc (n : ℕ) (h : Hist A O) : Hist A O := (h.1, h.2.take n)

theorem histTrunc_histPrefix {n m : ℕ} (hnm : n ≤ m) (ω : Traj A O) :
    histTrunc n (histPrefix m ω) = histPrefix n ω := by
  unfold histTrunc histPrefix
  refine Prod.ext rfl ?_
  change (List.ofFn fun k : Fin m => ω.2 k).take n = List.ofFn fun k : Fin n => ω.2 k
  rw [← Fin.ofFn_take_eq_take_ofFn hnm]
  congr 1

theorem length_histPrefix (n : ℕ) (ω : Traj A O) : (histPrefix n ω).2.length = n := by
  simp [histPrefix]

/-- On a length match, the set of trajectories with a given length-`n` prefix is
the history's cylinder. -/
theorem histPrefix_fiber_eq_cyl {n : ℕ} {h : Hist A O} (hlen : h.2.length = n) :
    {ω : Traj A O | histPrefix n ω = h} = cyl h := by
  ext ω
  rw [Set.mem_ofPred_eq, mem_cyl]
  constructor
  · rintro rfl
    refine ⟨rfl, fun k => ?_⟩
    simp [histPrefix]
  · rintro ⟨h1, h2⟩
    unfold histPrefix
    refine Prod.ext h1 ?_
    change (List.ofFn fun k : Fin n => ω.2 k) = h.2
    refine List.ext_getElem (by simp [hlen]) fun k hk1 hk2 => ?_
    simp only [List.getElem_ofFn]
    exact h2 ⟨k, hk2⟩

theorem histPrefix_fiber_eq_empty {n : ℕ} {h : Hist A O} (hlen : h.2.length ≠ n) :
    {ω : Traj A O | histPrefix n ω = h} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro heq
  exact hlen (by rw [← heq]; simp [histPrefix])

theorem measurableSet_histPrefix_fiber (n : ℕ) (h : Hist A O) :
    MeasurableSet {ω : Traj A O | histPrefix n ω = h} := by
  by_cases hlen : h.2.length = n
  · rw [histPrefix_fiber_eq_cyl hlen]
    exact measurableSet_cyl h
  · rw [histPrefix_fiber_eq_empty hlen]
    exact MeasurableSet.empty

/-- Any function of the length-`n` prefix is measurable on the path space:
its preimages are countable unions of prefix fibers. -/
theorem measurable_comp_histPrefix {β : Type*} [MeasurableSpace β]
    (g : Hist A O → β) (n : ℕ) :
    Measurable fun ω : Traj A O => g (histPrefix n ω) := by
  intro s _
  have hset : (fun ω : Traj A O => g (histPrefix n ω)) ⁻¹' s =
      ⋃ h ∈ g ⁻¹' s, {ω : Traj A O | histPrefix n ω = h} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun hω => ⟨_, hω, rfl⟩, fun ⟨h, hh, heq⟩ => by rw [heq]; exact hh⟩
  rw [hset]
  exact MeasurableSet.biUnion (Set.to_countable _) fun h _ =>
    measurableSet_histPrefix_fiber n h

set_option warn.classDefReducibility false in
/-- Events determined by the length-`n` history prefix, as a sub-σ-algebra of
the product σ-algebra on `Θ × Ω∞`. -/
def prefixSigma (A O Θ : Type*) [Fintype A] [Fintype O] [MeasurableSpace A]
    [MeasurableSpace O] [MeasurableSpace Θ] (n : ℕ) :
    MeasurableSpace (Θ × Traj A O) :=
  MeasurableSpace.comap (fun x => histPrefix n x.2) ⊤

theorem prefixSigma_le (n : ℕ) :
    prefixSigma A O Θ n ≤ (inferInstance : MeasurableSpace (Θ × Traj A O)) := by
  rintro _ ⟨S, -, rfl⟩
  have hset : (fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' S =
      ⋃ h ∈ S, Prod.snd ⁻¹' {ω : Traj A O | histPrefix n ω = h} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨h, hh, heq⟩ => heq ▸ hh⟩
  rw [hset]
  exact MeasurableSet.biUnion (Set.to_countable S) fun h _ =>
    measurable_snd (measurableSet_histPrefix_fiber n h)

theorem prefixSigma_mono : Monotone (prefixSigma A O Θ) := by
  intro n m hnm
  rintro _ ⟨S, -, rfl⟩
  refine ⟨histTrunc n ⁻¹' S, MeasurableSpace.measurableSet_top, ?_⟩
  ext x
  simp only [Set.mem_preimage]
  rw [histTrunc_histPrefix hnm]

/-- The prefix filtration on the Bayesian joint space. -/
def prefixFiltration (A O Θ : Type*) [Fintype A] [Fintype O] [Fintype Θ]
    [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Θ]
    [MeasurableSingletonClass A] [MeasurableSingletonClass O] [MeasurableSingletonClass Θ] :
    Filtration ℕ (inferInstance : MeasurableSpace (Θ × Traj A O)) where
  seq := prefixSigma A O Θ
  mono' := prefixSigma_mono
  le' := prefixSigma_le

/-- Any function of the length-`n` prefix is `prefixSigma n`-measurable. -/
theorem measurable_prefixSigma_comp {β : Type*} [MeasurableSpace β]
    (g : Hist A O → β) (n : ℕ) :
    Measurable[prefixSigma A O Θ n] fun x : Θ × Traj A O => g (histPrefix n x.2) :=
  fun s _ => ⟨g ⁻¹' s, MeasurableSpace.measurableSet_top, rfl⟩

/-- The horizon-`n` posterior process is measurable for the prefix σ-algebra. -/
theorem stronglyMeasurable_posterior_prefix (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (θ : Θ) (n : ℕ) :
    StronglyMeasurable[prefixSigma A O Θ n]
      (fun x : Θ × Traj A O => posterior α Ms (histPrefix n x.2) θ) :=
  (measurable_prefixSigma_comp (fun h => posterior α Ms h θ) n).stronglyMeasurable

/-! ### The class indicator -/

/-- The indicator of class `θ` on the Bayesian joint space. -/
noncomputable def classInd (θ : Θ) : Θ × Traj A O → ℝ :=
  (Prod.fst ⁻¹' ({θ} : Set Θ)).indicator fun _ => 1

theorem measurableSet_classSet (θ : Θ) :
    MeasurableSet (Prod.fst ⁻¹' ({θ} : Set Θ) : Set (Θ × Traj A O)) :=
  measurable_fst (measurableSet_singleton θ)

theorem integrable_classInd (μ : Measure (Θ × Traj A O)) [IsFiniteMeasure μ] (θ : Θ) :
    Integrable (classInd θ) μ :=
  (integrable_const 1).indicator (measurableSet_classSet θ)

/-! ### The conditional-expectation identification (prefix posteriors to path-law identification)

The horizon-`n` posterior evaluated along the trajectory prefix is a version of
`E[1_{C⋆ = θ} | ℱ_n]` under the Bayesian joint law. -/

section CondExp

variable (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O)
  (μfam : Θ → Measure (Traj A O))

/-- Bayes algebra: the posterior times the mixture mass reproduces the joint
mass, including the null-history convention (`0/0 = 0`). -/
theorem posterior_mul_mixProb (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid)
    (h : Hist A O) (θ : Θ) :
    posterior α Ms h θ * (∑ c, α c * traceProb π (Ms c) h) =
      α θ * traceProb π (Ms θ) h := by
  unfold traceProb
  have hsum : (∑ c, α c * (polWeight π h * traceLik (Ms c) h)) =
      polWeight π h * ∑ c, α c * traceLik (Ms c) h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsum]
  by_cases hD : (∑ c, α c * traceLik (Ms c) h) = 0
  · have hz : α θ * traceLik (Ms θ) h = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun c _ =>
        mul_nonneg (hα.1 c) (traceLik_nonneg _ (hV c) h)).1 hD θ (Finset.mem_univ θ)
    unfold posterior
    rw [hD, div_zero, zero_mul,
      show α θ * (polWeight π h * traceLik (Ms θ) h)
          = polWeight π h * (α θ * traceLik (Ms θ) h) from by ring, hz, mul_zero]
  · unfold posterior
    field_simp

/-- Mass of a prefix atom under the joint law: the `α`-mixture of trace
probabilities. -/
theorem jointLaw_atom (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) {n : ℕ} {h : Hist A O}
    (hlen : h.2.length = n) :
    jointLaw α μfam ((fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h}) =
      ENNReal.ofReal (∑ c, α c * traceProb π (Ms c) h) := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hset : (fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h} =
      Prod.snd ⁻¹' {ω : Traj A O | histPrefix n ω = h} := rfl
  rw [hset, jointLaw_apply α hprob
    (measurable_snd (measurableSet_histPrefix_fiber n h))]
  have hcomp : ∀ c : Θ, Prod.mk c ⁻¹'
      (Prod.snd ⁻¹' {ω : Traj A O | histPrefix n ω = h}) =
      {ω : Traj A O | histPrefix n ω = h} := fun c => rfl
  simp_rw [hcomp, histPrefix_fiber_eq_cyl hlen]
  rw [ENNReal.ofReal_sum_of_nonneg fun c _ =>
    mul_nonneg (hα.1 c) (traceProb_nonneg π hπ _ (hV c) h)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(hμ c).cylinder, ← ENNReal.ofReal_mul (hα.1 c)]

/-- Mass of a prefix atom intersected with a class slice. -/
theorem jointLaw_atom_inter_class (hα : IsDist α)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) (θ : Θ)
    {n : ℕ} {h : Hist A O} (hlen : h.2.length = n) :
    jointLaw α μfam
        ((fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h} ∩
          Prod.fst ⁻¹' ({θ} : Set Θ)) =
      ENNReal.ofReal (α θ * traceProb π (Ms θ) h) := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hmeasS : MeasurableSet
      ((fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h} ∩
        Prod.fst ⁻¹' ({θ} : Set Θ)) :=
    ((measurable_snd (measurableSet_histPrefix_fiber n h))).inter
      (measurableSet_classSet θ)
  rw [jointLaw_apply α hprob hmeasS]
  rw [Finset.sum_eq_single θ]
  · have hcomp : Prod.mk θ ⁻¹'
        ((fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h} ∩
          Prod.fst ⁻¹' ({θ} : Set Θ)) = {ω : Traj A O | histPrefix n ω = h} := by
      ext ω
      simp [Set.mem_preimage]
    rw [hcomp, histPrefix_fiber_eq_cyl hlen, (hμ θ).cylinder,
      ← ENNReal.ofReal_mul (hα.1 θ)]
  · intro c _ hc
    have hcomp : Prod.mk c ⁻¹'
        ((fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h} ∩
          Prod.fst ⁻¹' ({θ} : Set Θ)) = ∅ := by
      ext ω
      simp [Set.mem_preimage, hc]
    rw [hcomp]
    simp
  · intro habs
    exact absurd (Finset.mem_univ θ) habs

/-- **The martingale identity**: the horizon-`n` posterior along the trajectory
prefix is a version of the conditional expectation of the class indicator given
the prefix σ-algebra, under the Bayesian joint law. -/
theorem posterior_ae_eq_condExp (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid)
    (hπ : IsPolicy π) (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) (θ : Θ) (n : ℕ) :
    (fun x : Θ × Traj A O => posterior α Ms (histPrefix n x.2) θ)
      =ᵐ[jointLaw α μfam]
      (jointLaw α μfam)[classInd θ | prefixSigma A O Θ n] := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have hint_ind : Integrable (classInd θ) (jointLaw α μfam) :=
    integrable_classInd _ θ
  have hmeas_post : Measurable fun x : Θ × Traj A O =>
      posterior α Ms (histPrefix n x.2) θ :=
    (measurable_prefixSigma_comp (fun h => posterior α Ms h θ) n).mono
      (prefixSigma_le n) le_rfl
  have hint_post : Integrable
      (fun x : Θ × Traj A O => posterior α Ms (histPrefix n x.2) θ)
      (jointLaw α μfam) := by
    refine Integrable.mono' (integrable_const 1)
      hmeas_post.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (posterior_nonneg α hα Ms hV _ θ)]
    exact posterior_le_one α hα Ms hV _ θ
  refine ae_eq_condExp_of_forall_setIntegral_eq (prefixSigma_le n) hint_ind
    (fun s _ _ => hint_post.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_posterior_prefix α Ms θ n).aestronglyMeasurable
  obtain ⟨S, -, rfl⟩ := hs
  -- Only length-`n` histories are attained by the prefix map.
  have hFS : (fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' S =
      (fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹'
        (S ∩ {h : Hist A O | h.2.length = n}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun hx => ⟨hx, length_histPrefix n x.2⟩, fun hx => hx.1⟩
  have hfin : (S ∩ {h : Hist A O | h.2.length = n}).Finite := by
    refine Set.Finite.subset (Set.finite_range
      (fun p : O × (Fin n → A × O) => ((p.1, List.ofFn p.2) : Hist A O))) ?_
    rintro h ⟨-, (hlen : h.2.length = n)⟩
    refine ⟨(h.1, fun k : Fin n => h.2.get (Fin.cast hlen.symm k)), Prod.ext rfl ?_⟩
    change List.ofFn (fun k : Fin n => h.2.get (Fin.cast hlen.symm k)) = h.2
    refine List.ext_getElem (by simp [hlen]) fun k hk1 hk2 => ?_
    simp [List.getElem_ofFn, List.get_eq_getElem]
  have hunion : (fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹'
      (S ∩ {h : Hist A O | h.2.length = n}) =
      ⋃ h ∈ hfin.toFinset,
        (fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.Finite.mem_toFinset,
      Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨h, hh, heq⟩ => heq ▸ hh⟩
  have hatom_meas : ∀ h : Hist A O, MeasurableSet
      ((fun x : Θ × Traj A O => histPrefix n x.2) ⁻¹' {h}) := fun h =>
    prefixSigma_le n _ ⟨{h}, MeasurableSpace.measurableSet_top, rfl⟩
  rw [hFS, hunion,
    integral_biUnion_finset _ (fun h _ => hatom_meas h)
      (fun h₁ _ h₂ _ hne => (Set.disjoint_singleton.mpr hne).preimage _)
      (fun h _ => hint_post.integrableOn),
    integral_biUnion_finset _ (fun h _ => hatom_meas h)
      (fun h₁ _ h₂ _ hne => (Set.disjoint_singleton.mpr hne).preimage _)
      (fun h _ => hint_ind.integrableOn)]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hlen : h.2.length = n := (hfin.mem_toFinset.1 hh).2
  -- Left side: the integrand is constant on the atom.
  rw [setIntegral_congr_fun (hatom_meas h)
    (fun x (hx : histPrefix n x.2 = h) => by
      rw [show posterior α Ms (histPrefix n x.2) θ = posterior α Ms h θ from by
        rw [hx]]),
    setIntegral_const]
  -- Right side: the indicator localizes to the class slice.
  rw [show classInd θ = (Prod.fst ⁻¹' ({θ} : Set Θ)).indicator
      (fun _ : Θ × Traj A O => (1 : ℝ)) from rfl,
    setIntegral_indicator (measurableSet_classSet θ), setIntegral_const]
  rw [Measure.real, Measure.real, jointLaw_atom α Ms π μfam hα hV hπ hμ hlen,
    jointLaw_atom_inter_class α Ms π μfam hα hμ θ hlen,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun c _ =>
      mul_nonneg (hα.1 c) (traceProb_nonneg π hπ _ (hV c) h)),
    ENNReal.toReal_ofReal (mul_nonneg (hα.1 θ)
      (traceProb_nonneg π hπ _ (hV θ) h)),
    smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  exact posterior_mul_mixProb α Ms π hα hV h θ

end CondExp


/-! ### The limit σ-algebra -/

theorem comap_histPrefix_le (n : ℕ) :
    MeasurableSpace.comap (histPrefix n : Traj A O → Hist A O) ⊤ ≤
      (inferInstance : MeasurableSpace (Traj A O)) := by
  rintro _ ⟨S, -, rfl⟩
  have hset : histPrefix n ⁻¹' S =
      ⋃ h ∈ S, {ω : Traj A O | histPrefix n ω = h} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun hω => ⟨_, hω, rfl⟩, fun ⟨h, hh, heq⟩ => by rw [heq]; exact hh⟩
  rw [hset]
  exact MeasurableSet.biUnion (Set.to_countable S) fun h _ =>
    measurableSet_histPrefix_fiber n h

/-- The prefix σ-algebras exhaust exactly the trajectory information: their
supremum is the pullback of the full path-space σ-algebra. -/
theorem iSup_prefixSigma :
    (⨆ n, prefixSigma A O Θ n) =
      MeasurableSpace.comap (Prod.snd : Θ × Traj A O → Traj A O)
        inferInstance := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    have hcomp : prefixSigma A O Θ n =
        MeasurableSpace.comap (Prod.snd : Θ × Traj A O → Traj A O)
          (MeasurableSpace.comap (histPrefix n) ⊤) := by
      rw [prefixSigma, MeasurableSpace.comap_comp]
      rfl
    rw [hcomp]
    exact MeasurableSpace.comap_mono (comap_histPrefix_le n)
  · rw [show (inferInstance : MeasurableSpace (Traj A O)) =
        MeasurableSpace.generateFrom
          (Set.range (cyl : Hist A O → Set (Traj A O))) from
      generateFrom_range_cyl, MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    have hfib : (Prod.snd : Θ × Traj A O → Traj A O) ⁻¹' cyl h =
        (fun x : Θ × Traj A O => histPrefix h.2.length x.2) ⁻¹' {h} := by
      rw [← histPrefix_fiber_eq_cyl (n := h.2.length) rfl]
      rfl
    rw [hfib]
    exact le_iSup (prefixSigma A O Θ) h.2.length _
      ⟨{h}, MeasurableSpace.measurableSet_top, rfl⟩

/-! ### Carriers from mutual singularity -/

/-- Pairwise mutual singularity yields a measurable carrier for each class:
full mass under its own law, null under every other. -/
theorem exists_carriers (μfam : Θ → Measure (Traj A O))
    (hsing : Pairwise fun θ θ' => μfam θ ⟂ₘ μfam θ') :
    ∃ E : Θ → Set (Traj A O), (∀ θ, MeasurableSet (E θ)) ∧
      (∀ θ, μfam θ (E θ)ᶜ = 0) ∧ ∀ θ c, c ≠ θ → μfam c (E θ) = 0 := by
  refine ⟨fun θ => ⋂ c : {c : Θ // c ≠ θ}, (hsing c.2).nullSet,
    fun θ => MeasurableSet.iInter fun c => (hsing c.2).measurableSet_nullSet,
    fun θ => ?_, fun θ c hc => ?_⟩
  · rw [Set.compl_iInter]
    exact measure_iUnion_null fun c => (hsing c.2).measure_compl_nullSet
  · exact measure_mono_null (Set.iInter_subset _ ⟨c, hc⟩)
      (hsing hc).measure_nullSet

/-- Under the joint law, the class indicator agrees a.e. with the indicator of
the class carrier pulled back from the trajectory: the trajectory determines
the class. -/
theorem classInd_ae_eq_carrier (α : Θ → ℝ) (μfam : Θ → Measure (Traj A O))
    (hprob : ∀ c, IsProbabilityMeasure (μfam c))
    {E : Θ → Set (Traj A O)} (hEmeas : ∀ θ, MeasurableSet (E θ))
    (hEself : ∀ θ, μfam θ (E θ)ᶜ = 0)
    (hEother : ∀ θ c, c ≠ θ → μfam c (E θ) = 0) (θ : Θ) :
    classInd θ =ᵐ[jointLaw α μfam]
      (Prod.snd ⁻¹' E θ).indicator fun _ => (1 : ℝ) := by
  have hp1 : jointLaw α μfam
      (Prod.fst ⁻¹' ({θ} : Set Θ) ∩ (Prod.snd ⁻¹' E θ)ᶜ) = 0 := by
    rw [jointLaw_apply α hprob ((measurableSet_classSet θ).inter
      (measurable_snd (hEmeas θ)).compl)]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = θ
    · subst hc
      have hpre : Prod.mk c ⁻¹'
          (Prod.fst ⁻¹' ({c} : Set Θ) ∩ (Prod.snd ⁻¹' E c)ᶜ) = (E c)ᶜ := by
        ext ω
        simp
      rw [hpre, hEself c, mul_zero]
    · have hpre : Prod.mk c ⁻¹'
          (Prod.fst ⁻¹' ({θ} : Set Θ) ∩ (Prod.snd ⁻¹' E θ)ᶜ) =
          (∅ : Set (Traj A O)) := by
        ext ω
        simp [hc]
      rw [hpre, measure_empty, mul_zero]
  have hp2 : jointLaw α μfam
      ((Prod.fst ⁻¹' ({θ} : Set Θ))ᶜ ∩ Prod.snd ⁻¹' E θ) = 0 := by
    rw [jointLaw_apply α hprob ((measurableSet_classSet θ).compl.inter
      (measurable_snd (hEmeas θ)))]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = θ
    · subst hc
      have hpre : Prod.mk c ⁻¹'
          ((Prod.fst ⁻¹' ({c} : Set Θ))ᶜ ∩ Prod.snd ⁻¹' E c) =
          (∅ : Set (Traj A O)) := by
        ext ω
        simp
      rw [hpre, measure_empty, mul_zero]
    · have hpre : Prod.mk c ⁻¹'
          ((Prod.fst ⁻¹' ({θ} : Set Θ))ᶜ ∩ Prod.snd ⁻¹' E θ) = E θ := by
        ext ω
        simp [hc]
      rw [hpre, hEother θ c hc, mul_zero]
  have hsub : {x : Θ × Traj A O |
      ¬ classInd θ x = (Prod.snd ⁻¹' E θ).indicator (fun _ => (1 : ℝ)) x} ⊆
      (Prod.fst ⁻¹' ({θ} : Set Θ) ∩ (Prod.snd ⁻¹' E θ)ᶜ) ∪
        ((Prod.fst ⁻¹' ({θ} : Set Θ))ᶜ ∩ Prod.snd ⁻¹' E θ) := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx
    by_cases h1 : x.1 = θ <;> by_cases h2 : x.2 ∈ E θ
    · exact absurd (by
        rw [show classInd θ x = 1 from
            Set.indicator_of_mem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) h1 _,
          show (Prod.snd ⁻¹' E θ).indicator (fun _ => (1 : ℝ)) x = 1 from
            Set.indicator_of_mem (s := Prod.snd ⁻¹' E θ) h2 _]) hx
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (by
        rw [show classInd θ x = 0 from
            Set.indicator_of_notMem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) h1 _,
          show (Prod.snd ⁻¹' E θ).indicator (fun _ => (1 : ℝ)) x = 0 from
            Set.indicator_of_notMem (s := Prod.snd ⁻¹' E θ) h2 _]) hx
  exact ae_iff.mpr (measure_mono_null hsub (measure_union_null hp1 hp2))

/-! ### (1) ⇒ (3): singularity forces concentration -/

/-- **`pathLaw_identification`, singularity ⇒ concentration for every prior**: if the path laws are pairwise mutually
singular then the posterior concentrates on the true class for every prior.
Route: `posterior_ae_eq_condExp` identifies the posterior process with the
conditional-expectation martingale of the class indicator; Lévy's upward
theorem sends it to the conditional expectation given the full trajectory
σ-algebra (`iSup_prefixSigma`); the carriers from mutual singularity make the
class indicator trajectory-measurable a.e., collapsing that conditional
expectation to the indicator itself. -/
theorem concentrates_of_pairwise_singular (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (π : Policy A O) (μfam : Θ → Measure (Traj A O)) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ))
    (hsing : Pairwise fun θ θ' => μfam θ ⟂ₘ μfam θ') :
    ConcentratesOnTruth α Ms μfam := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  obtain ⟨E, hEmeas, hEself, hEother⟩ := exists_carriers μfam hsing
  have hm : (⨆ n, (prefixFiltration A O Θ) n) ≤
      (inferInstance : MeasurableSpace (Θ × Traj A O)) :=
    iSup_le fun n => prefixSigma_le n
  have key : ∀ θ : Θ, ∀ᵐ x ∂ jointLaw α μfam,
      Tendsto (fun T => posterior α Ms (histPrefix T x.2) θ) atTop
        (𝓝 (classInd θ x)) := by
    intro θ
    have hint_carrier : Integrable
        ((Prod.snd ⁻¹' E θ).indicator fun _ : Θ × Traj A O => (1 : ℝ))
        (jointLaw α μfam) :=
      (integrable_const 1).indicator (measurable_snd (hEmeas θ))
    have hsm_carrier : StronglyMeasurable[⨆ n, (prefixFiltration A O Θ) n]
        ((Prod.snd ⁻¹' E θ).indicator fun _ : Θ × Traj A O => (1 : ℝ)) := by
      refine stronglyMeasurable_const.indicator ?_
      rw [show (⨆ n, (prefixFiltration A O Θ) n) =
          ⨆ n, prefixSigma A O Θ n from rfl, iSup_prefixSigma]
      exact ⟨E θ, hEmeas θ, rfl⟩
    have hind := classInd_ae_eq_carrier α μfam hprob hEmeas hEself hEother θ
    have hlimit : (jointLaw α μfam)[classInd θ | ⨆ n, (prefixFiltration A O Θ) n]
        =ᵐ[jointLaw α μfam] classInd θ := by
      calc (jointLaw α μfam)[classInd θ | ⨆ n, (prefixFiltration A O Θ) n]
          =ᵐ[jointLaw α μfam]
            (jointLaw α μfam)[(Prod.snd ⁻¹' E θ).indicator fun _ => (1 : ℝ) |
              ⨆ n, (prefixFiltration A O Θ) n] := condExp_congr_ae hind
        _ = (Prod.snd ⁻¹' E θ).indicator fun _ => (1 : ℝ) :=
            condExp_of_stronglyMeasurable hm hsm_carrier hint_carrier
        _ =ᵐ[jointLaw α μfam] classInd θ := hind.symm
    have hlevy := tendsto_ae_condExp (μ := jointLaw α μfam)
      (ℱ := prefixFiltration A O Θ) (classInd θ)
    have hterm : ∀ᵐ x ∂ jointLaw α μfam, ∀ T : ℕ,
        posterior α Ms (histPrefix T x.2) θ =
          ((jointLaw α μfam)[classInd θ | prefixSigma A O Θ T]) x :=
      ae_all_iff.2 fun T => posterior_ae_eq_condExp α Ms π μfam hα hV hπ hμ θ T
    filter_upwards [hlevy, hlimit, hterm] with x hx1 hx2 hx3
    rw [← hx2]
    exact hx1.congr fun T => (hx3 T).symm
  filter_upwards [ae_all_iff.2 key] with x hx
  have hx1 := hx x.1
  have hone : classInd (A := A) (O := O) x.1 x = 1 :=
    Set.indicator_of_mem (show x ∈ Prod.fst ⁻¹' ({x.1} : Set Θ) from rfl) _
  rwa [hone] at hx1


/-! ### (2) ⇒ (1): concentration for one full-support prior forces singularity -/

/-- Two posteriors at distinct classes never sum above one (the null-history
convention makes both zero). -/
theorem posterior_pair_le_one (α : Θ → ℝ) (Ms : Θ → POMDP A O) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) {θ θ' : Θ} (hne : θ ≠ θ') (h : Hist A O) :
    posterior α Ms h θ + posterior α Ms h θ' ≤ 1 := by
  classical
  have hnn : ∀ c, 0 ≤ α c * traceLik (Ms c) h := fun c =>
    mul_nonneg (hα.1 c) (traceLik_nonneg _ (hV c) h)
  unfold posterior
  by_cases hD : (∑ c, α c * traceLik (Ms c) h) = 0
  · rw [hD]
    simp
  · rw [← add_div, div_le_one
      (lt_of_le_of_ne (Finset.sum_nonneg fun c _ => hnn c) (Ne.symm hD))]
    calc α θ * traceLik (Ms θ) h + α θ' * traceLik (Ms θ') h
        = ∑ c ∈ ({θ, θ'} : Finset Θ), α c * traceLik (Ms c) h :=
          (Finset.sum_pair (f := fun c => α c * traceLik (Ms c) h) hne).symm
      _ ≤ ∑ c, α c * traceLik (Ms c) h :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun c _ _ => hnn c

/-! ### Decoders: Le Cam's route to singularity -/

/-- The class whose posterior exceeds one half, if any (it is then unique);
otherwise an arbitrary class. -/
noncomputable def majorityDecoder [Nonempty Θ] (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (h : Hist A O) : Θ :=
  if hex : ∃ θ, (1 / 2 : ℝ) < posterior α Ms h θ then hex.choose
  else Classical.arbitrary Θ

theorem majorityDecoder_eq [Nonempty Θ] (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid) (h : Hist A O) {θ : Θ}
    (hθ : (1 / 2 : ℝ) < posterior α Ms h θ) : majorityDecoder α Ms h = θ := by
  unfold majorityDecoder
  have hex : ∃ θ, (1 / 2 : ℝ) < posterior α Ms h θ := ⟨θ, hθ⟩
  rw [dif_pos hex]
  by_contra hne
  have hsum := posterior_pair_le_one α Ms hα hV hne h
  have := hex.choose_spec
  linarith

/-- Under a full-support prior, joint-law concentration gives, for each class,
concentration of that class's posterior coordinate under its own path law. -/
theorem ae_tendsto_posterior_of_concentrates (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (μfam : Θ → Measure (Traj A O)) (hfs : FullSupport α)
    (hprob : ∀ c, IsProbabilityMeasure (μfam c))
    (hconc : ConcentratesOnTruth α Ms μfam) (c : Θ) :
    ∀ᵐ ω ∂ μfam c,
      Tendsto (fun T => posterior α Ms (histPrefix T ω) c) atTop (𝓝 1) := by
  obtain ⟨t, hsub, htmeas, ht0⟩ := exists_measurable_superset_of_null
    (ae_iff.1 hconc)
  rw [jointLaw_apply α hprob htmeas] at ht0
  have hterm := (Finset.sum_eq_zero_iff.1 ht0) c (Finset.mem_univ c)
  have hμc : μfam c (Prod.mk c ⁻¹' t) = 0 := by
    rcases mul_eq_zero.1 hterm with hzero | hzero
    · exact absurd hzero (ENNReal.ofReal_pos.2 (hfs c)).ne'
    · exact hzero
  refine ae_iff.mpr (measure_mono_null (fun ω hω => ?_) hμc)
  exact hsub hω

/-- **Concentration gives decoders.**  Under a full-support prior the majority
decoder errs only where the true class's posterior is at most one half, and
almost-sure concentration gives convergence in measure, so its classwise error
tends to zero. -/
theorem exists_decoders_of_concentrates [Nonempty Θ] (α : Θ → ℝ)
    (Ms : Θ → POMDP A O) (μfam : Θ → Measure (Traj A O)) (hα : IsDist α)
    (hfs : FullSupport α) (hV : ∀ θ, (Ms θ).Valid)
    (hprob : ∀ c, IsProbabilityMeasure (μfam c))
    (hconc : ConcentratesOnTruth α Ms μfam) :
    ∃ dec : ℕ → Hist A O → Θ, ∀ θ,
      Tendsto (fun T => μfam θ {ω | dec T (histPrefix T ω) ≠ θ}) atTop (𝓝 0) := by
  refine ⟨fun _ h => majorityDecoder α Ms h, fun θ => ?_⟩
  have hae := ae_tendsto_posterior_of_concentrates α Ms μfam hfs hprob hconc θ
  have hmeas : ∀ T, AEStronglyMeasurable
      (fun ω : Traj A O => posterior α Ms (histPrefix T ω) θ) (μfam θ) := fun T =>
    (measurable_comp_histPrefix (fun h => posterior α Ms h θ) T).aestronglyMeasurable
  have hprob' := hprob θ
  have hinm := tendstoInMeasure_of_tendsto_ae (μ := μfam θ) hmeas
    (g := fun _ => (1 : ℝ)) hae
  have hhalf := hinm (ENNReal.ofReal (1 / 2)) (ENNReal.ofReal_pos.2 (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhalf
    (fun _ => zero_le) fun T => measure_mono fun ω hω => ?_
  rw [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt
  rw [not_le] at hlt
  apply hω
  have hpost : (1 / 2 : ℝ) < posterior α Ms (histPrefix T ω) θ := by
    have hle1 := posterior_le_one α hα Ms hV (histPrefix T ω) θ
    rw [edist_lt_ofReal, Real.dist_eq, abs_sub_lt_iff] at hlt
    linarith [hlt.2]
  exact majorityDecoder_eq α Ms hα hV _ hpost

/-- **Decoders give singularity** (Borel–Cantelli).  Along horizons where the
worst-class error is summable the decoder is eventually correct under each
class, and the eventually-`θ` events are pairwise disjoint with full mass. -/
theorem pairwise_singular_of_decoders (μfam : Θ → Measure (Traj A O))
    (dec : ℕ → Hist A O → Θ)
    (hdec : ∀ θ, Tendsto (fun T => μfam θ {ω | dec T (histPrefix T ω) ≠ θ}) atTop (𝓝 0)) :
    Pairwise fun θ θ' => μfam θ ⟂ₘ μfam θ' := by
  intro θ θ' hne
  have hpick : ∀ k : ℕ, ∃ T : ℕ, ∀ c : Θ,
      μfam c {ω | dec T (histPrefix T ω) ≠ c} ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    have hpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ k :=
      ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) k
    have hev : ∀ᶠ T in atTop, ∀ c : Θ,
        μfam c {ω | dec T (histPrefix T ω) ≠ c} ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
      rw [Filter.eventually_all]
      intro c
      exact (hdec c).eventually (Iio_mem_nhds hpos) |>.mono fun T hT => le_of_lt hT
    exact hev.exists
  choose Ts hTs using hpick
  let E : Θ → ℕ → Set (Traj A O) := fun c k =>
    {ω | dec (Ts k) (histPrefix (Ts k) ω) ≠ c}
  have hEmeas : ∀ c k, MeasurableSet (E c k) := fun c k =>
    measurable_comp_histPrefix (fun h => dec (Ts k) h) (Ts k)
      (measurableSet_singleton c).compl
  have hnull : ∀ c, μfam c (limsup (E c) atTop) = 0 := by
    intro c
    refine measure_limsup_atTop_eq_zero (ne_of_lt ?_)
    calc ∑' k, μfam c (E c k) ≤ ∑' k, (2 : ℝ≥0∞)⁻¹ ^ k :=
          ENNReal.tsum_le_tsum fun k => hTs k c
      _ < ∞ := by
          rw [ENNReal.tsum_geometric]
          exact lt_top_iff_ne_top.2 (ENNReal.inv_ne_top.2
            (tsub_pos_iff_lt.2 (ENNReal.inv_lt_one.2 (by norm_num))).ne')
  have hmem : ∀ c (ω : Traj A O), ω ∉ limsup (E c) atTop ↔
      ∀ᶠ k in atTop, dec (Ts k) (histPrefix (Ts k) ω) = c := by
    intro c ω
    rw [mem_limsup_iff_frequently_mem, Filter.not_frequently]
    simp only [E, Set.mem_ofPred_eq, not_not]
  have hsub : (limsup (E θ) atTop)ᶜ ⊆ limsup (E θ') atTop := by
    intro ω hω
    rw [Set.mem_compl_iff, hmem] at hω
    by_contra hω'
    rw [hmem] at hω'
    obtain ⟨k, hk, hk'⟩ := (hω.and hω').exists
    exact hne (hk.symm.trans hk')
  refine ⟨limsup (E θ) atTop, MeasurableSet.measurableSet_limsup (hEmeas θ), hnull θ, ?_⟩
  exact measure_mono_null hsub (hnull θ')

/-- **`pathLaw_identification`, concentration ⇒ singularity**, by Le Cam's route: posterior concentration
under one full-support prior yields decoders with vanishing worst-class error,
and Borel–Cantelli turns those into pairwise mutual singularity. -/
theorem pairwise_singular_of_concentrates (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (μfam : Θ → Measure (Traj A O)) (hα : IsDist α) (hfs : FullSupport α)
    (hV : ∀ θ, (Ms θ).Valid) (hprob : ∀ c, IsProbabilityMeasure (μfam c))
    (hconc : ConcentratesOnTruth α Ms μfam) :
    Pairwise fun θ θ' => μfam θ ⟂ₘ μfam θ' := by
  have hΘ : Nonempty Θ := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have h1 := hα.2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  obtain ⟨dec, hdec⟩ := exists_decoders_of_concentrates α Ms μfam hα hfs hV hprob hconc
  exact pairwise_singular_of_decoders μfam dec hdec

/-! ### (3) ⇒ (2): the uniform prior exists -/

theorem exists_fullSupport_isDist (Θ : Type*) [Fintype Θ] [Nonempty Θ] :
    ∃ α : Θ → ℝ, IsDist α ∧ FullSupport α := by
  have hpos : (0 : ℝ) < Fintype.card Θ := by
    exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => 1 / Fintype.card Θ, ⟨fun _ => by positivity, ?_⟩,
    fun _ => by positivity⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp


/-! ### Expected posterior entropy: the sum–integral bridge (toward Thm 7.1) -/

section InfoBridge

variable [DecidableEq A] [DecidableEq O]
variable (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O)
  (μfam : Θ → Measure (Traj A O))

theorem mem_histSet_iff {T : ℕ} {h : Hist A O} :
    h ∈ histSet A O T ↔ h.2.length = T := by
  unfold histSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, -, rfl⟩
    simp
  · intro hlen
    refine ⟨(h.1, fun k : Fin T => h.2.get (Fin.cast hlen.symm k)),
      Finset.mem_univ _, Prod.ext rfl ?_⟩
    change List.ofFn (fun k : Fin T => h.2.get (Fin.cast hlen.symm k)) = h.2
    refine List.ext_getElem (by simp [hlen]) fun k hk1 hk2 => ?_
    simp [List.getElem_ofFn, List.get_eq_getElem]

/-- A bounded function of the length-`T` prefix integrates against the joint
law as the mixture-weighted sum over the length-`T` histories. -/
theorem integral_comp_histPrefix (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid)
    (hπ : IsPolicy π) (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ))
    (g : Hist A O → ℝ) (C : ℝ) (hbound : ∀ h : Hist A O, |g h| ≤ C) (T : ℕ) :
    ∫ x, g (histPrefix T x.2) ∂ jointLaw α μfam =
      ∑ h ∈ histSet A O T, (∑ c, α c * traceProb π (Ms c) h) * g h := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have hmeas : Measurable fun x : Θ × Traj A O => g (histPrefix T x.2) :=
    (measurable_prefixSigma_comp g T).mono (prefixSigma_le T) le_rfl
  have hint : Integrable (fun x : Θ × Traj A O => g (histPrefix T x.2))
      (jointLaw α μfam) :=
    Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable
      (Eventually.of_forall fun x => hbound _)
  have hatom_meas : ∀ h : Hist A O, MeasurableSet
      ((fun x : Θ × Traj A O => histPrefix T x.2) ⁻¹' {h}) := fun h =>
    prefixSigma_le T _ ⟨{h}, MeasurableSpace.measurableSet_top, rfl⟩
  have hcover : (Set.univ : Set (Θ × Traj A O)) =
      ⋃ h ∈ histSet A O T,
        (fun x : Θ × Traj A O => histPrefix T x.2) ⁻¹' {h} := by
    ext x
    simp only [Set.mem_univ, true_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨_, mem_histSet_iff.2 (length_histPrefix T x.2), rfl⟩
  rw [← setIntegral_univ, hcover,
    integral_biUnion_finset _ (fun h _ => hatom_meas h)
      (fun h₁ _ h₂ _ hne => (Set.disjoint_singleton.mpr hne).preimage _)
      (fun h _ => hint.integrableOn)]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hlen : h.2.length = T := mem_histSet_iff.1 hh
  rw [setIntegral_congr_fun (hatom_meas h)
      (fun x (hx : histPrefix T x.2 = h) => by
        rw [show g (histPrefix T x.2) = g h from by rw [hx]]),
    setIntegral_const, Measure.real, jointLaw_atom α Ms π μfam hα hV hπ hμ hlen,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun c _ =>
      mul_nonneg (hα.1 c) (traceProb_nonneg π hπ _ (hV c) h)), smul_eq_mul]

theorem ent_le_card {p : Θ → ℝ} (h0 : ∀ c, 0 ≤ p c) (_h1 : ∀ c, p c ≤ 1) :
    ent p ≤ Fintype.card Θ := by
  unfold ent
  calc ∑ c, Real.negMulLog (p c) ≤ ∑ _c : Θ, (1 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have := Real.negMulLog_le_one_sub_self (h0 c)
        linarith [h0 c]
    _ = Fintype.card Θ := by simp
  
theorem abs_ent_le_card {p : Θ → ℝ} (h0 : ∀ c, 0 ≤ p c) (h1 : ∀ c, p c ≤ 1) :
    |ent p| ≤ Fintype.card Θ := by
  rw [abs_of_nonneg (ent_nonneg_of_mem_Icc h0 h1)]
  exact ent_le_card h0 h1

/-- Concentration drives every posterior coordinate to its class indicator,
hence the posterior entropy to zero, along almost every trajectory. -/
theorem tendsto_ent_posterior_of_concentrates (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hconc : ConcentratesOnTruth α Ms μfam) :
    ∀ᵐ x ∂ jointLaw α μfam,
      Tendsto (fun T => ent (posterior α Ms (histPrefix T x.2))) atTop (𝓝 0) := by
  classical
  filter_upwards [hconc] with x hx
  have hcoord : ∀ θ : Θ,
      Tendsto (fun T => posterior α Ms (histPrefix T x.2) θ) atTop
        (𝓝 (if θ = x.1 then 1 else 0)) := by
    intro θ
    by_cases hθ : θ = x.1
    · subst hθ
      simpa using hx
    · rw [if_neg hθ]
      have hup : ∀ T, posterior α Ms (histPrefix T x.2) θ ≤
          1 - posterior α Ms (histPrefix T x.2) x.1 := fun T => by
        have := posterior_pair_le_one α Ms hα hV hθ (histPrefix T x.2)
        linarith
      have hupt : Tendsto
          (fun T => 1 - posterior α Ms (histPrefix T x.2) x.1) atTop (𝓝 0) := by
        have hsub := (tendsto_const_nhds (α := ℕ) (x := (1 : ℝ))).sub hx
        norm_num at hsub
        exact hsub
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupt
        (fun T => posterior_nonneg α hα Ms hV _ θ) hup
  have hsum : Tendsto
      (fun T => ∑ θ, Real.negMulLog (posterior α Ms (histPrefix T x.2) θ))
      atTop (𝓝 (∑ θ : Θ, Real.negMulLog (if θ = x.1 then 1 else 0))) := by
    refine tendsto_finsetSum _ fun θ _ => ?_
    exact (Real.continuous_negMulLog.continuousAt).tendsto.comp (hcoord θ)
  simpa [ent, apply_ite Real.negMulLog] using hsum

/-- Under concentration, the expected posterior entropy vanishes. -/
theorem tendsto_integral_ent_posterior_zero (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ))
    (hconc : ConcentratesOnTruth α Ms μfam) :
    Tendsto
      (fun T => ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam)
      atTop (𝓝 0) := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have hzero : (𝓝 (0 : ℝ)) = 𝓝 (∫ _x, (0 : ℝ) ∂ jointLaw α μfam) := by simp
  rw [hzero]
  refine tendsto_integral_of_dominated_convergence
    (fun _ => (Fintype.card Θ : ℝ))
    (fun T => ((measurable_prefixSigma_comp
      (fun h => ent (posterior α Ms h)) T).mono
        (prefixSigma_le T) le_rfl).aestronglyMeasurable)
    (integrable_const _)
    (fun T => Eventually.of_forall fun x => ?_)
    (tendsto_ent_posterior_of_concentrates α Ms μfam hα hV hconc)
  rw [Real.norm_eq_abs]
  exact abs_ent_le_card (fun c => posterior_nonneg α hα Ms hV _ c)
    (fun c => posterior_le_one α hα Ms hV _ c)

theorem infoAt_le_ent (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid)
    (hπ : IsPolicy π) (T : ℕ) : infoAt α Ms π T ≤ ent α := by
  unfold infoAt
  refine sub_le_self _ (Finset.sum_nonneg fun h _ => mul_nonneg ?_ ?_)
  · exact Finset.sum_nonneg fun θ _ =>
      mul_nonneg (hα.1 θ) (traceProb_nonneg π hπ (Ms θ) (hV θ) h)
  · exact ent_posterior_nonneg α hα Ms hV h

/-- The finite-horizon information in integral form. -/
theorem infoAt_eq_sub_integral (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid)
    (hπ : IsPolicy π) (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) (T : ℕ) :
    infoAt α Ms π T = ent α -
      ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam := by
  unfold infoAt
  rw [integral_comp_histPrefix α Ms π μfam hα hV hπ hμ
    (fun h => ent (posterior α Ms h)) (Fintype.card Θ)
    (fun h => abs_ent_le_card (fun c => posterior_nonneg α hα Ms hV _ c)
      (fun c => posterior_le_one α hα Ms hV _ c)) T]

/-- **Thm 7.1, attainment half**: posterior concentration drives `I_∞` to the
prior entropy. -/
theorem infoInf_eq_ent_of_concentrates (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ))
    (hconc : ConcentratesOnTruth α Ms μfam) :
    infoInf α Ms π = ent α := by
  have hbdd : BddAbove (Set.range fun T => infoAt α Ms π T) := by
    refine ⟨ent α, ?_⟩
    rintro y ⟨T, rfl⟩
    exact infoAt_le_ent α Ms π hα hV hπ T
  refine le_antisymm (ciSup_le fun T => infoAt_le_ent α Ms π hα hV hπ T) ?_
  have hlim : Tendsto (fun T => infoAt α Ms π T) atTop (𝓝 (ent α)) := by
    have hsub := (tendsto_const_nhds (α := ℕ) (x := ent α)).sub
      (tendsto_integral_ent_posterior_zero α Ms π μfam hα hV hμ hconc)
    norm_num at hsub
    exact hsub.congr fun T =>
      (infoAt_eq_sub_integral α Ms π μfam hα hV hπ hμ T).symm
  exact le_of_tendsto hlim (Eventually.of_forall fun T => le_ciSup hbdd T)

/-! ### Monotonicity of the expected posterior entropy (finite Jensen) -/

/-- Total trace probability is conserved by one-step extension. -/
theorem sum_traceProb_append [Nonempty O] (M : POMDP A O) (hM : M.Valid)
    {π : Policy A O} (hπ : IsPolicy π) (h : Hist A O) :
    ∑ ao : A × O, traceProb π M (h.1, h.2 ++ [ao]) = traceProb π M h := by
  rw [Fintype.sum_prod_type]
  simp_rw [traceProb_append π M hM h]
  calc ∑ a, ∑ o', traceProb π M h * π h a * nextObs M h a o'
      = ∑ a, traceProb π M h * π h a * ∑ o', nextObs M h a o' := by
        simp_rw [Finset.mul_sum]
    _ = ∑ a, traceProb π M h * π h a := by
        simp_rw [sum_nextObs M hM h, mul_one]
    _ = traceProb π M h := by
        rw [← Finset.mul_sum, (hπ h).2, mul_one]

theorem histSet_succ (T : ℕ) :
    histSet A O (T + 1) = Finset.image
      (fun p : Hist A O × (A × O) => ((p.1.1, p.1.2 ++ [p.2]) : Hist A O))
      ((histSet A O T) ×ˢ (Finset.univ : Finset (A × O))) := by
  ext h'
  rw [mem_histSet_iff, Finset.mem_image]
  constructor
  · intro hlen
    have hne : h'.2 ≠ [] := by
      intro h0
      rw [h0] at hlen
      simp at hlen
    refine ⟨((h'.1, h'.2.dropLast), h'.2.getLast hne), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨mem_histSet_iff.2 ?_, Finset.mem_univ _⟩
      rw [List.length_dropLast, hlen]
      omega
    · show ((h'.1, h'.2.dropLast ++ [h'.2.getLast hne]) : Hist A O) = h'
      rw [List.dropLast_append_getLast hne]
  · rintro ⟨⟨h, ao⟩, hmem, rfl⟩
    rw [Finset.mem_product] at hmem
    have hlen := mem_histSet_iff.1 hmem.1
    simp [hlen]

/-- The mixture mass of a history under a prior and a model family. -/
noncomputable def mixMass (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O)
    (g : Hist A O) : ℝ :=
  ∑ c, α c * traceProb π (Ms c) g

/-- The nonnegative orthant of class vectors, where every posterior lives. -/
def nonnegOrthant (Θ : Type*) : Set (Θ → ℝ) := Set.pi Set.univ fun _ => Set.Ici (0 : ℝ)

theorem convex_nonnegOrthant : Convex ℝ (nonnegOrthant Θ) :=
  convex_pi fun _ _ => convex_Ici 0

theorem posterior_mem_nonnegOrthant (α : Θ → ℝ) (Ms : Θ → POMDP A O) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (h : Hist A O) : posterior α Ms h ∈ nonnegOrthant Θ :=
  fun c _ => posterior_nonneg α hα Ms hV h c

/-- **Blackwell monotonicity along the prefix chain, for every concave potential.**
One more step of information can only lower the expected value of a concave
function of the posterior: finite Jensen against the child decomposition of each
history atom (the parent posterior is the mass-weighted average of its children's).
Entropy, Gini, and the negative of any Bregman-generating convex potential are
instances, so every conservative reward's partial sums are monotone in the horizon. -/
theorem expPotential_succ_le [Nonempty O] (φ : (Θ → ℝ) → ℝ)
    (hφ : ConcaveOn ℝ (nonnegOrthant Θ) φ)
    (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π) (T : ℕ) :
    ∑ h' ∈ histSet A O (T + 1),
        (∑ c, α c * traceProb π (Ms c) h') * φ (posterior α Ms h') ≤
      ∑ h ∈ histSet A O T,
        (∑ c, α c * traceProb π (Ms c) h) * φ (posterior α Ms h) := by
  classical
  have hminj : ∀ p₁ ∈ (histSet A O T) ×ˢ (Finset.univ : Finset (A × O)),
      ∀ p₂ ∈ (histSet A O T) ×ˢ (Finset.univ : Finset (A × O)),
      ((p₁.1.1, p₁.1.2 ++ [p₁.2]) : Hist A O) = (p₂.1.1, p₂.1.2 ++ [p₂.2]) →
        p₁ = p₂ := by
    rintro ⟨h₁, ao₁⟩ hm₁ ⟨h₂, ao₂⟩ hm₂ heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨hfst, hsnd⟩ := heq
    obtain ⟨hl, hs⟩ := List.append_inj' hsnd (by simp)
    have hao : ao₁ = ao₂ := by simpa using hs
    have hh : h₁ = h₂ := Prod.ext hfst hl
    rw [hh, hao]
  rw [histSet_succ, Finset.sum_image hminj, Finset.sum_product]
  refine Finset.sum_le_sum fun h hh => ?_
  dsimp only
  show ∑ ao : A × O,
      mixMass α Ms π (h.1, h.2 ++ [ao]) * φ (posterior α Ms (h.1, h.2 ++ [ao])) ≤
    mixMass α Ms π h * φ (posterior α Ms h)
  have hmnonneg : ∀ g, 0 ≤ mixMass α Ms π g := fun g => Finset.sum_nonneg fun c _ =>
    mul_nonneg (hα.1 c) (traceProb_nonneg π hπ _ (hV c) g)
  have hsum_children : ∑ ao : A × O, mixMass α Ms π (h.1, h.2 ++ [ao]) =
      mixMass α Ms π h := by
    unfold mixMass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum, sum_traceProb_append (Ms c) (hV c) hπ h]
  by_cases hm0 : mixMass α Ms π h = 0
  · have hchild0 : ∀ ao : A × O, mixMass α Ms π (h.1, h.2 ++ [ao]) = 0 := fun ao =>
      (Finset.sum_eq_zero_iff_of_nonneg fun ao' _ =>
        hmnonneg (h.1, h.2 ++ [ao'])).1 (hsum_children.trans hm0) ao
        (Finset.mem_univ ao)
    rw [hm0, zero_mul]
    refine le_of_eq (Finset.sum_eq_zero fun ao _ => ?_)
    rw [hchild0 ao, zero_mul]
  · have hmpos : 0 < mixMass α Ms π h := lt_of_le_of_ne (hmnonneg h) (Ne.symm hm0)
    have hwsum : ∑ ao : A × O, mixMass α Ms π (h.1, h.2 ++ [ao]) / mixMass α Ms π h = 1 := by
      rw [← Finset.sum_div, hsum_children, div_self hm0]
    -- the parent posterior is the weighted average of the child posteriors
    have hmix : ∀ θ, ∑ ao : A × O,
        (mixMass α Ms π (h.1, h.2 ++ [ao]) / mixMass α Ms π h) *
          posterior α Ms (h.1, h.2 ++ [ao]) θ =
        posterior α Ms h θ := by
      intro θ
      have hterm : ∀ ao : A × O,
          (mixMass α Ms π (h.1, h.2 ++ [ao]) / mixMass α Ms π h) *
            posterior α Ms (h.1, h.2 ++ [ao]) θ =
          α θ * traceProb π (Ms θ) (h.1, h.2 ++ [ao]) / mixMass α Ms π h := by
        intro ao
        rw [div_mul_eq_mul_div, mul_comm,
          show posterior α Ms (h.1, h.2 ++ [ao]) θ *
              mixMass α Ms π (h.1, h.2 ++ [ao]) =
            α θ * traceProb π (Ms θ) (h.1, h.2 ++ [ao]) from
            posterior_mul_mixProb α Ms π hα hV (h.1, h.2 ++ [ao]) θ]
      simp_rw [hterm]
      rw [← Finset.sum_div, ← Finset.mul_sum,
        sum_traceProb_append (Ms θ) (hV θ) hπ h,
        show α θ * traceProb π (Ms θ) h = posterior α Ms h θ * mixMass α Ms π h from
          (posterior_mul_mixProb α Ms π hα hV h θ).symm,
        mul_div_assoc, div_self hm0, mul_one]
    -- vector Jensen on the child decomposition
    have hjensen : ∑ ao : A × O,
        (mixMass α Ms π (h.1, h.2 ++ [ao]) / mixMass α Ms π h) *
          φ (posterior α Ms (h.1, h.2 ++ [ao])) ≤
        φ (posterior α Ms h) := by
      have hJ := hφ.le_map_sum (t := (Finset.univ : Finset (A × O)))
        (w := fun ao => mixMass α Ms π (h.1, h.2 ++ [ao]) / mixMass α Ms π h)
        (p := fun ao => posterior α Ms (h.1, h.2 ++ [ao]))
        (fun ao _ => div_nonneg (hmnonneg _) hmpos.le) hwsum
        (fun ao _ => posterior_mem_nonnegOrthant α Ms hα hV _)
      have hvec : (∑ ao : A × O, (mixMass α Ms π (h.1, h.2 ++ [ao]) / mixMass α Ms π h) •
          posterior α Ms (h.1, h.2 ++ [ao])) = posterior α Ms h := by
        funext θ
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hmix θ
      rw [hvec] at hJ
      simpa only [smul_eq_mul] using hJ
    calc ∑ ao : A × O,
          mixMass α Ms π (h.1, h.2 ++ [ao]) * φ (posterior α Ms (h.1, h.2 ++ [ao]))
        = mixMass α Ms π h * ∑ ao : A × O,
            (mixMass α Ms π (h.1, h.2 ++ [ao]) / mixMass α Ms π h) *
              φ (posterior α Ms (h.1, h.2 ++ [ao])) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ao _ => ?_
          field_simp
      _ ≤ mixMass α Ms π h * φ (posterior α Ms h) :=
          mul_le_mul_of_nonneg_left hjensen hmpos.le

/-- Concavity of a finite sum of concave functions. -/
theorem concaveOn_finset_sum {ι : Type*} (s : Finset ι) {S : Set (Θ → ℝ)} (hS : Convex ℝ S)
    {f : ι → (Θ → ℝ) → ℝ} (hf : ∀ i ∈ s, ConcaveOn ℝ S (f i)) :
    ConcaveOn ℝ S fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using concaveOn_const (0 : ℝ) hS
  | insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Shannon entropy is concave on the nonnegative orthant. -/
theorem concaveOn_ent : ConcaveOn ℝ (nonnegOrthant Θ) (ent : (Θ → ℝ) → ℝ) := by
  have hc : ∀ c : Θ, ConcaveOn ℝ (nonnegOrthant Θ)
      fun p : Θ → ℝ => Real.negMulLog (p c) := by
    intro c
    have h := Real.concaveOn_negMulLog.comp_linearMap
      (LinearMap.proj c : (Θ → ℝ) →ₗ[ℝ] ℝ)
    refine h.subset (fun p hp => ?_) convex_nonnegOrthant
    simpa using hp c (Set.mem_univ c)
  exact concaveOn_finset_sum Finset.univ convex_nonnegOrthant fun c _ => hc c

/-- One step of information can only lower the expected posterior entropy. -/
theorem expEnt_succ_le [Nonempty O]
    (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π) (T : ℕ) :
    ∑ h' ∈ histSet A O (T + 1),
        (∑ c, α c * traceProb π (Ms c) h') * ent (posterior α Ms h') ≤
      ∑ h ∈ histSet A O T,
        (∑ c, α c * traceProb π (Ms c) h) * ent (posterior α Ms h) :=
  expPotential_succ_le ent concaveOn_ent α Ms π hα hV hπ T

/-- The expected value of any concave potential of the posterior is antitone in
the horizon: the chain-level form of Blackwell monotonicity. -/
theorem expPotential_antitone [Nonempty O] (φ : (Θ → ℝ) → ℝ)
    (hφ : ConcaveOn ℝ (nonnegOrthant Θ) φ)
    (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π) :
    Antitone fun T => ∑ h ∈ histSet A O T,
      (∑ c, α c * traceProb π (Ms c) h) * φ (posterior α Ms h) :=
  antitone_nat_of_succ_le fun T => expPotential_succ_le φ hφ α Ms π hα hV hπ T

/-- The finite-horizon information curve is nondecreasing in the horizon
(the paper's Lemma "Prefix continuity" (i), monotonicity part), as a corollary of
the entropy instance of Blackwell monotonicity. -/
theorem infoAt_mono [Nonempty O] (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O)
    (hα : IsDist α) (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π) :
    Monotone (infoAt α Ms π) := by
  refine monotone_nat_of_le_succ fun T => ?_
  unfold infoAt
  have := expEnt_succ_le α Ms π hα hV hπ T
  linarith

/-! ### The converse: attained information forces concentration -/

/-- The limit posterior: conditional probability of each class given the whole
trajectory. -/
noncomputable def limitPosterior (α : Θ → ℝ) (μfam : Θ → Measure (Traj A O))
    (θ : Θ) : Θ × Traj A O → ℝ :=
  (jointLaw α μfam)[classInd θ | ⨆ n, (prefixFiltration A O Θ) n]

/-- Lévy's upward theorem for the posterior process, with no singularity
assumption: the posterior converges a.e. to the limit posterior. -/
theorem ae_tendsto_limitPosterior (α : Θ → ℝ) (Ms : Θ → POMDP A O)
    (π : Policy A O) (μfam : Θ → Measure (Traj A O)) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) (θ : Θ) :
    ∀ᵐ x ∂ jointLaw α μfam,
      Tendsto (fun T => posterior α Ms (histPrefix T x.2) θ) atTop
        (𝓝 (limitPosterior α μfam θ x)) := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have hlevy := tendsto_ae_condExp (μ := jointLaw α μfam)
    (ℱ := prefixFiltration A O Θ) (classInd θ)
  have hterm : ∀ᵐ x ∂ jointLaw α μfam, ∀ T : ℕ,
      posterior α Ms (histPrefix T x.2) θ =
        ((jointLaw α μfam)[classInd θ | prefixSigma A O Θ T]) x :=
    ae_all_iff.2 fun T => posterior_ae_eq_condExp α Ms π μfam hα hV hπ hμ θ T
  filter_upwards [hlevy, hterm] with x hx1 hx3
  exact hx1.congr fun T => (hx3 T).symm

theorem sum_classInd_eq_one (x : Θ × Traj A O) :
    ∑ θ, classInd (A := A) (O := O) θ x = 1 := by
  classical
  have hterm : ∀ θ : Θ, classInd (A := A) (O := O) θ x =
      if x.1 = θ then 1 else 0 := by
    intro θ
    by_cases hθ : x.1 = θ
    · rw [if_pos hθ]
      exact Set.indicator_of_mem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) hθ _
    · rw [if_neg hθ]
      exact Set.indicator_of_notMem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) hθ _
  simp_rw [hterm]
  simp

/-- The limit posterior is a probability vector a.e. -/
theorem ae_sum_limitPosterior (α : Θ → ℝ) (π : Policy A O)
    (Ms : Θ → POMDP A O) (μfam : Θ → Measure (Traj A O)) (hα : IsDist α)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) :
    ∀ᵐ x ∂ jointLaw α μfam, ∑ θ, limitPosterior α μfam θ x = 1 := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have hm : (⨆ n, (prefixFiltration A O Θ) n) ≤
      (inferInstance : MeasurableSpace (Θ × Traj A O)) :=
    iSup_le fun n => prefixSigma_le n
  have hsum := condExp_finsetSum (μ := jointLaw α μfam)
    (s := (Finset.univ : Finset Θ)) (f := fun θ => classInd (A := A) (O := O) θ)
    (fun θ _ => integrable_classInd _ θ) (⨆ n, (prefixFiltration A O Θ) n)
  have hconst : (jointLaw α μfam)[∑ θ, classInd (A := A) (O := O) θ |
      ⨆ n, (prefixFiltration A O Θ) n] =ᵐ[jointLaw α μfam]
      fun _ => (1 : ℝ) := by
    have h1 : (∑ θ, classInd (A := A) (O := O) θ) =
        fun _ : Θ × Traj A O => (1 : ℝ) := by
      funext x
      rw [Finset.sum_apply]
      exact sum_classInd_eq_one x
    rw [h1]
    exact Filter.EventuallyEq.of_eq (condExp_const hm (1 : ℝ))
  have hchain := hsum.symm.trans hconst
  filter_upwards [hchain] with x hx
  rw [Finset.sum_apply] at hx
  exact hx

/-- The class is a.e. determined wherever the limit posterior hits one. -/
theorem ae_classEq_of_limitPosterior_one (α : Θ → ℝ) (π : Policy A O)
    (Ms : Θ → POMDP A O) (μfam : Θ → Measure (Traj A O)) (hα : IsDist α)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) (θ : Θ) :
    ∀ᵐ x ∂ jointLaw α μfam, limitPosterior α μfam θ x = 1 → x.1 = θ := by
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have hm : (⨆ n, (prefixFiltration A O Θ) n) ≤
      (inferInstance : MeasurableSpace (Θ × Traj A O)) :=
    iSup_le fun n => prefixSigma_le n
  have hsmeas_m : MeasurableSet[⨆ n, (prefixFiltration A O Θ) n]
      {x : Θ × Traj A O | limitPosterior α μfam θ x = 1} :=
    (stronglyMeasurable_condExp (f := classInd θ)
      (μ := jointLaw α μfam)).measurable (measurableSet_singleton (1 : ℝ))
  have hsmeas : MeasurableSet {x : Θ × Traj A O | limitPosterior α μfam θ x = 1} :=
    hm _ hsmeas_m
  have hint_ind : Integrable (classInd θ) (jointLaw α μfam) :=
    integrable_classInd _ θ
  have hkey : ∫ x in {x : Θ × Traj A O | limitPosterior α μfam θ x = 1},
      limitPosterior α μfam θ x ∂ jointLaw α μfam =
      ∫ x in {x : Θ × Traj A O | limitPosterior α μfam θ x = 1},
        classInd θ x ∂ jointLaw α μfam :=
    setIntegral_condExp hm hint_ind hsmeas_m
  have hleft : ∫ x in {x : Θ × Traj A O | limitPosterior α μfam θ x = 1},
      limitPosterior α μfam θ x ∂ jointLaw α μfam =
      (jointLaw α μfam).real {x : Θ × Traj A O | limitPosterior α μfam θ x = 1} := by
    rw [setIntegral_congr_fun hsmeas (fun x hx => hx), setIntegral_const,
      smul_eq_mul, mul_one]
  have hright : ∫ x in {x : Θ × Traj A O | limitPosterior α μfam θ x = 1},
      classInd θ x ∂ jointLaw α μfam =
      (jointLaw α μfam).real
        ({x : Θ × Traj A O | limitPosterior α μfam θ x = 1} ∩
          Prod.fst ⁻¹' ({θ} : Set Θ)) := by
    rw [show classInd (A := A) (O := O) θ =
        (Prod.fst ⁻¹' ({θ} : Set Θ)).indicator (fun _ => (1 : ℝ)) from rfl,
      setIntegral_indicator (measurableSet_classSet θ), setIntegral_const,
      smul_eq_mul, mul_one]
  have hμeq : jointLaw α μfam {x : Θ × Traj A O | limitPosterior α μfam θ x = 1} =
      jointLaw α μfam ({x : Θ × Traj A O | limitPosterior α μfam θ x = 1} ∩
        Prod.fst ⁻¹' ({θ} : Set Θ)) :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
      (hleft.symm.trans (hkey.trans hright))
  have hadd := measure_sdiff_add_inter
    (μ := jointLaw α μfam)
    {x : Θ × Traj A O | limitPosterior α μfam θ x = 1}
    (measurableSet_classSet θ)
  rw [hμeq] at hadd
  have hdiff : jointLaw α μfam
      ({x : Θ × Traj A O | limitPosterior α μfam θ x = 1} \
        Prod.fst ⁻¹' ({θ} : Set Θ)) = 0 := by
    have hne := measure_ne_top (jointLaw α μfam)
      ({x : Θ × Traj A O | limitPosterior α μfam θ x = 1} ∩
        Prod.fst ⁻¹' ({θ} : Set Θ))
    nth_rewrite 2 [show jointLaw α μfam
        ({x : Θ × Traj A O | limitPosterior α μfam θ x = 1} ∩
          Prod.fst ⁻¹' ({θ} : Set Θ)) = 0 +
        jointLaw α μfam
          ({x : Θ × Traj A O | limitPosterior α μfam θ x = 1} ∩
            Prod.fst ⁻¹' ({θ} : Set Θ)) from (zero_add _).symm] at hadd
    exact WithTop.add_right_cancel hne hadd
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hdiff
  rw [Set.mem_ofPred_eq] at hx
  rw [Classical.not_imp] at hx
  exact ⟨hx.1, hx.2⟩

/-- A `[0,1]`-valued probability vector with zero entropy sits at a vertex. -/
theorem exists_eq_one_of_ent_eq_zero {p : Θ → ℝ} (h0 : ∀ c, 0 ≤ p c)
    (h1 : ∀ c, p c ≤ 1) (hsum : ∑ c, p c = 1) (hent : ent p = 0) :
    ∃ θ, p θ = 1 := by
  classical
  have hterm : ∀ c : Θ, Real.negMulLog (p c) = 0 := fun c =>
    (Finset.sum_eq_zero_iff_of_nonneg fun c' _ =>
      Real.negMulLog_nonneg (h0 c') (h1 c')).1 hent c (Finset.mem_univ c)
  have h01 : ∀ c, p c = 0 ∨ p c = 1 := by
    intro c
    have hc := hterm c
    simp only [Real.negMulLog_def] at hc
    rw [neg_mul, neg_eq_zero] at hc
    rcases mul_eq_zero.1 hc with hc0 | hlog
    · exact Or.inl hc0
    · rcases Real.log_eq_zero.1 hlog with hc0 | hc1 | hcm
      · exact Or.inl hc0
      · exact Or.inr hc1
      · exact absurd hcm (by linarith [h0 c])
  by_contra hno
  rw [not_exists] at hno
  have hall0 : ∀ c, p c = 0 := fun c => (h01 c).resolve_right (hno c)
  rw [Finset.sum_congr rfl fun c _ => hall0 c, Finset.sum_const_zero] at hsum
  exact absurd hsum (by norm_num)

/-- **The limit of the information curve.**  The expected posterior entropy
converges to the expected entropy of the limit posterior (dominated convergence
along the prefix filtration): the limit in the paper's Lemma "Prefix continuity
of the three curves" (i), $I_t \uparrow I(C;H_\infty)$, in the entropy form. -/
theorem tendsto_integral_ent_posterior_limit [Nonempty O]
    (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O)
    (μfam : Θ → Measure (Traj A O)) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) :
    Tendsto (fun T => ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam) atTop
      (𝓝 (∫ x, ent (fun θ => limitPosterior α μfam θ x) ∂ jointLaw α μfam)) := by
  classical
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have htendall : ∀ᵐ x ∂ jointLaw α μfam, ∀ θ : Θ,
      Tendsto (fun T => posterior α Ms (histPrefix T x.2) θ) atTop
        (𝓝 (limitPosterior α μfam θ x)) :=
    ae_all_iff.2 fun θ => ae_tendsto_limitPosterior α Ms π μfam hα hV hπ hμ θ
  have hlim_ae : ∀ᵐ x ∂ jointLaw α μfam,
      Tendsto (fun T => ent (posterior α Ms (histPrefix T x.2))) atTop
        (𝓝 (ent fun θ => limitPosterior α μfam θ x)) := by
    filter_upwards [htendall] with x htend
    unfold ent
    refine tendsto_finsetSum _ fun θ _ => ?_
    exact (Real.continuous_negMulLog.continuousAt).tendsto.comp (htend θ)
  refine tendsto_integral_of_dominated_convergence
    (fun _ => (Fintype.card Θ : ℝ))
    (fun T => ((measurable_prefixSigma_comp
      (fun h => ent (posterior α Ms h)) T).mono
        (prefixSigma_le T) le_rfl).aestronglyMeasurable)
    (integrable_const _)
    (fun T => Eventually.of_forall fun x => ?_) hlim_ae
  rw [Real.norm_eq_abs]
  exact abs_ent_le_card (fun c => posterior_nonneg α hα Ms hV _ c)
    (fun c => posterior_le_one α hα Ms hV _ c)

/-- **Thm 7.1, converse half**: if the terminal information attains the prior
entropy, the posterior concentrates on the true class.  The expected posterior
entropy is antitone (finite Jensen) with infimum zero, hence tends to zero; by
dominated convergence the limit posterior has zero entropy a.e., so it sits at
a vertex, and the vertex must be the true class. -/
theorem concentrates_of_infoInf_eq_ent [Nonempty O]
    (α : Θ → ℝ) (Ms : Θ → POMDP A O) (π : Policy A O)
    (μfam : Θ → Measure (Traj A O)) (hα : IsDist α)
    (hV : ∀ θ, (Ms θ).Valid) (hπ : IsPolicy π)
    (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ))
    (hsup : infoInf α Ms π = ent α) :
    ConcentratesOnTruth α Ms μfam := by
  classical
  have hprob : ∀ c, IsProbabilityMeasure (μfam c) := fun c => (hμ c).isProb
  have hPM : IsProbabilityMeasure (jointLaw α μfam) :=
    isProbabilityMeasure_jointLaw hα hprob
  have hm : (⨆ n, (prefixFiltration A O Θ) n) ≤
      (inferInstance : MeasurableSpace (Θ × Traj A O)) :=
    iSup_le fun n => prefixSigma_le n
  have htendall : ∀ᵐ x ∂ jointLaw α μfam, ∀ θ : Θ,
      Tendsto (fun T => posterior α Ms (histPrefix T x.2) θ) atTop
        (𝓝 (limitPosterior α μfam θ x)) :=
    ae_all_iff.2 fun θ => ae_tendsto_limitPosterior α Ms π μfam hα hV hπ hμ θ
  have hsum1 : ∀ᵐ x ∂ jointLaw α μfam, ∑ θ, limitPosterior α μfam θ x = 1 :=
    ae_sum_limitPosterior α π Ms μfam hα hμ
  have htruth : ∀ᵐ x ∂ jointLaw α μfam, ∀ θ : Θ,
      limitPosterior α μfam θ x = 1 → x.1 = θ :=
    ae_all_iff.2 fun θ => ae_classEq_of_limitPosterior_one α π Ms μfam hα hμ θ
  -- The expected posterior entropy tends to zero.
  have hee : ∀ T, ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam =
      ∑ h ∈ histSet A O T,
        (∑ c, α c * traceProb π (Ms c) h) * ent (posterior α Ms h) := fun T =>
    integral_comp_histPrefix α Ms π μfam hα hV hπ hμ
      (fun h => ent (posterior α Ms h)) (Fintype.card Θ)
      (fun h => abs_ent_le_card (fun c => posterior_nonneg α hα Ms hV _ c)
        (fun c => posterior_le_one α hα Ms hV _ c)) T
  have hanti : Antitone fun T =>
      ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam := by
    refine antitone_nat_of_succ_le fun T => ?_
    rw [hee, hee]
    exact expEnt_succ_le α Ms π hα hV hπ T
  have henn : ∀ T, 0 ≤ ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam :=
    fun T => integral_nonneg fun x => ent_nonneg_of_mem_Icc
      (fun c => posterior_nonneg α hα Ms hV _ c)
      (fun c => posterior_le_one α hα Ms hV _ c)
  have hbddB : BddBelow (Set.range fun T =>
      ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam) := by
    refine ⟨0, ?_⟩
    rintro y ⟨T, rfl⟩
    exact henn T
  have hinf0 : (⨅ T, ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam) = 0 := by
    refine le_antisymm ?_ (le_ciInf henn)
    by_contra hpos
    rw [not_le] at hpos
    have hlt : ∀ T, infoAt α Ms π T ≤ ent α -
        ⨅ T, ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam := by
      intro T
      rw [infoAt_eq_sub_integral α Ms π μfam hα hV hπ hμ T]
      have := ciInf_le hbddB T
      linarith
    have hsup_le : infoInf α Ms π ≤ ent α -
        ⨅ T, ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam :=
      ciSup_le hlt
    rw [hsup] at hsup_le
    linarith
  have htend_e : Tendsto (fun T =>
      ∫ x, ent (posterior α Ms (histPrefix T x.2)) ∂ jointLaw α μfam) atTop (𝓝 0) := by
    have := tendsto_atTop_ciInf hanti hbddB
    rwa [hinf0] at this
  -- Dominated convergence toward the limit posterior's entropy.
  have hDCT := tendsto_integral_ent_posterior_limit α Ms π μfam hα hV hπ hμ
  have hint0 : ∫ x, ent (fun θ => limitPosterior α μfam θ x) ∂ jointLaw α μfam = 0 :=
    tendsto_nhds_unique hDCT htend_e
  -- limit range bounds, a.e.
  have hrange_ae : ∀ᵐ x ∂ jointLaw α μfam, ∀ θ : Θ,
      0 ≤ limitPosterior α μfam θ x ∧ limitPosterior α μfam θ x ≤ 1 := by
    filter_upwards [htendall] with x htend
    intro θ
    constructor
    · exact ge_of_tendsto (htend θ) (Eventually.of_forall fun T =>
        posterior_nonneg α hα Ms hV _ θ)
    · exact le_of_tendsto (htend θ) (Eventually.of_forall fun T =>
        posterior_le_one α hα Ms hV _ θ)
  have hnonneg_ae : 0 ≤ᵐ[jointLaw α μfam]
      fun x => ent (fun θ => limitPosterior α μfam θ x) := by
    filter_upwards [hrange_ae] with x hr
    exact ent_nonneg_of_mem_Icc (fun c => (hr c).1) (fun c => (hr c).2)
  have hmeas_lim : Measurable fun x => ent (fun θ => limitPosterior α μfam θ x) := by
    unfold ent
    refine Finset.measurable_sum _ fun θ _ => ?_
    exact Real.continuous_negMulLog.measurable.comp
      ((stronglyMeasurable_condExp (f := classInd θ)
        (μ := jointLaw α μfam)).mono hm).measurable
  have hint_lim : Integrable (fun x => ent (fun θ => limitPosterior α μfam θ x))
      (jointLaw α μfam) := by
    refine Integrable.mono' (integrable_const (Fintype.card Θ : ℝ))
      hmeas_lim.aestronglyMeasurable ?_
    filter_upwards [hrange_ae] with x hr
    rw [Real.norm_eq_abs]
    exact abs_ent_le_card (fun c => (hr c).1) (fun c => (hr c).2)
  have hent0_ae := (integral_eq_zero_iff_of_nonneg_ae hnonneg_ae hint_lim).1 hint0
  -- Assemble the pointwise conclusion.
  filter_upwards [htendall, hsum1, htruth, hrange_ae, hent0_ae]
    with x htend hsum htru hr hent0
  obtain ⟨θs, hθs⟩ := exists_eq_one_of_ent_eq_zero
    (fun c => (hr c).1) (fun c => (hr c).2) hsum hent0
  have hx1 : x.1 = θs := htru θs hθs
  rw [hx1]
  have hfin := htend θs
  rwa [hθs] at hfin

end InfoBridge


end IdExp
