/-
Cylinder sets generate the path σ-algebra, and form a π-system.

`Formal.Basic` parameterizes every path-law statement by `IsPathLaw`, whose
only content is the cylinder probabilities.  For that to pin down a measure
the cylinders `cyl h` must generate the σ-algebra on `Traj A O = O × (A × O)^ℕ`
and be closed under nonempty intersection.  Both hold when `A`, `O` are finite
with measurable singletons (STATEMENTS.md choice C3: the intended discrete
instance): every generator of the product σ-algebra — `{ω | ω.1 = o}` and
`{ω | ω.2 k = v}` — is a *finite* union of cylinders.
-/
import Formal.Basic

-- The membership lemmas do not use the section instances that `Basic`'s
-- definitions carry; per-theorem `omit` churn is not worth it.
set_option linter.unusedSectionVars false

namespace IdExp

open MeasureTheory Set

variable {A O : Type*} [Fintype A] [Fintype O] [MeasurableSpace A] [MeasurableSpace O]

/-! ### Cylinder membership -/

theorem mem_cyl {h : Hist A O} {ω : Traj A O} :
    ω ∈ cyl h ↔ ω.1 = h.1 ∧ ∀ k : Fin h.2.length, ω.2 k.1 = h.2[k.1]'k.2 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k => h2 k.1 k.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k hk => h2 ⟨k, hk⟩⟩

theorem mem_cyl_nil {o : O} {ω : Traj A O} : ω ∈ cyl (o, []) ↔ ω.1 = o := by
  unfold cyl
  simp

theorem mem_cyl_ofFn {n : ℕ} {o : O} {w : Fin n → A × O} {ω : Traj A O} :
    ω ∈ cyl (o, List.ofFn w) ↔ ω.1 = o ∧ ∀ j : Fin n, ω.2 j.1 = w j := by
  unfold cyl
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    have hj : j.1 < (List.ofFn w).length := by simp [j.2]
    have := h2 j.1 hj
    simpa [List.getElem_ofFn] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    have hk' : k < n := by simpa using hk
    rw [List.getElem_ofFn]
    exact h2 ⟨k, hk'⟩

/-! ### Measurability and the π-system property -/

theorem measurableSet_cyl [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (h : Hist A O) : MeasurableSet (cyl h) := by
  have hrepr : cyl h = (Prod.fst ⁻¹' {h.1}) ∩
      ⋂ k : Fin h.2.length, (fun ω : Traj A O => ω.2 k.1) ⁻¹' {h.2[k.1]'k.2} := by
    ext ω
    simp only [mem_cyl, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_iInter]
  rw [hrepr]
  exact (measurable_fst (measurableSet_singleton _)).inter
    (MeasurableSet.iInter fun k =>
      ((measurable_pi_apply k.1).comp measurable_snd) (measurableSet_singleton _))

/-- Two cylinders with a common point are nested, so their intersection is a
cylinder. -/
theorem isPiSystem_range_cyl :
    IsPiSystem (range (cyl : Hist A O → Set (Traj A O))) := by
  rintro _ ⟨h, rfl⟩ _ ⟨h', rfl⟩ ⟨ω, hω, hω'⟩
  rw [mem_cyl] at hω hω'
  rcases le_total h'.2.length h.2.length with hle | hle
  · have hsub : cyl h ⊆ cyl h' := by
      intro ω' hω2
      rw [mem_cyl] at hω2 ⊢
      refine ⟨hω2.1.trans (hω.1.symm.trans hω'.1), fun k => ?_⟩
      have hk : k.1 < h.2.length := lt_of_lt_of_le k.2 hle
      calc ω'.2 k.1 = h.2[k.1]'hk := hω2.2 ⟨k.1, hk⟩
        _ = ω.2 k.1 := (hω.2 ⟨k.1, hk⟩).symm
        _ = h'.2[k.1]'k.2 := hω'.2 k
    rw [inter_eq_left.2 hsub]
    exact ⟨h, rfl⟩
  · have hsub : cyl h' ⊆ cyl h := by
      intro ω' hω2
      rw [mem_cyl] at hω2 ⊢
      refine ⟨hω2.1.trans (hω'.1.symm.trans hω.1), fun k => ?_⟩
      have hk : k.1 < h'.2.length := lt_of_lt_of_le k.2 hle
      calc ω'.2 k.1 = h'.2[k.1]'hk := hω2.2 ⟨k.1, hk⟩
        _ = ω.2 k.1 := (hω'.2 ⟨k.1, hk⟩).symm
        _ = h.2[k.1]'k.2 := hω.2 k
    rw [inter_eq_right.2 hsub]
    exact ⟨h', rfl⟩

/-! ### Cylinders generate the product σ-algebra -/

theorem generateFrom_range_cyl [MeasurableSingletonClass A] [MeasurableSingletonClass O] :
    (inferInstance : MeasurableSpace (Traj A O)) =
      MeasurableSpace.generateFrom (range (cyl : Hist A O → Set (Traj A O))) := by
  set G := MeasurableSpace.generateFrom (range (cyl : Hist A O → Set (Traj A O))) with hG
  apply le_antisymm
  · -- every generator of the product σ-algebra is a finite union of cylinders
    have hfst : ∀ o : O, MeasurableSet[G] (Prod.fst ⁻¹' {o} : Set (Traj A O)) := by
      intro o
      have hrepr : (Prod.fst ⁻¹' {o} : Set (Traj A O)) = cyl (o, []) := by
        ext ω
        simp [mem_cyl_nil]
      rw [hrepr]
      exact MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
    have hcoord : ∀ (k : ℕ) (v : A × O), MeasurableSet[G] {ω : Traj A O | ω.2 k = v} := by
      intro k v
      have hrepr : {ω : Traj A O | ω.2 k = v} =
          ⋃ (o : O) (w : Fin (k + 1) → A × O) (_ : w (Fin.last k) = v),
            cyl (o, List.ofFn w) := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion, mem_cyl_ofFn]
        constructor
        · intro hv
          refine ⟨ω.1, fun j => ω.2 j.1, ?_, rfl, fun j => rfl⟩
          show ω.2 (Fin.last k).1 = v
          rw [Fin.val_last]
          exact hv
        · rintro ⟨o, w, hw, -, hall⟩
          have := hall (Fin.last k)
          rw [Fin.val_last, hw] at this
          exact this
      rw [hrepr]
      exact MeasurableSet.iUnion fun o => MeasurableSet.iUnion fun w =>
        MeasurableSet.iUnion fun _ => MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
    show MeasurableSpace.comap Prod.fst ‹MeasurableSpace O› ⊔
        MeasurableSpace.comap Prod.snd MeasurableSpace.pi ≤ G
    refine sup_le ?_ ?_
    · rw [MeasurableSpace.comap_le_iff_le_map]
      refine MeasurableSpace.le_def.2 fun s _ => ?_
      show MeasurableSet[G] (Prod.fst ⁻¹' s)
      have hrepr : (Prod.fst ⁻¹' s : Set (Traj A O)) = ⋃ o ∈ s, Prod.fst ⁻¹' {o} := by
        ext ω
        simp
      rw [hrepr]
      exact (Set.toFinite s).measurableSet_biUnion fun o _ => hfst o
    · rw [MeasurableSpace.comap_le_iff_le_map]
      show (⨆ k : ℕ, MeasurableSpace.comap (fun f : ℕ → A × O => f k)
          (Prod.instMeasurableSpace : MeasurableSpace (A × O))) ≤ MeasurableSpace.map Prod.snd G
      refine iSup_le fun k => ?_
      rw [MeasurableSpace.comap_le_iff_le_map]
      refine MeasurableSpace.le_def.2 fun s _ => ?_
      show MeasurableSet[G] (Prod.snd ⁻¹' ((fun f : ℕ → A × O => f k) ⁻¹' s))
      have hrepr : (Prod.snd ⁻¹' ((fun f : ℕ → A × O => f k) ⁻¹' s) : Set (Traj A O)) =
          ⋃ v ∈ s, {ω : Traj A O | ω.2 k = v} := by
        ext ω
        simp
      rw [hrepr]
      exact (Set.toFinite s).measurableSet_biUnion fun v _ => hcoord k v
  · exact MeasurableSpace.generateFrom_le (by
      rintro _ ⟨h, rfl⟩
      exact measurableSet_cyl h)

end IdExp
