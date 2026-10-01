import Formal.CausalKernel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Path laws for arbitrary causal response kernels

**Relevance:** direct current-paper support (`Paper/draft/main.tex`, causal path laws in Sections 2
and 3 and the proof map).  Unlike `PathLaw.lean` and `PathLawExists.lean`, this module uses the
paper's current primitive directly: arbitrary history-dependent causal response kernels, histories
in `(A × O)^{<∞}`, and paths in `(A × O)^ℕ`.

The construction uses one independent dummy coordinate internally so that Mathlib's homogeneous
Ionescu--Tulcea trajectory API can generate the first real action--observation pair with the same
step kernel as every later pair.  `causalShift` removes that dummy coordinate.  The public path law
therefore has exactly the paper's path convention.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

variable {A O : Type*} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- Infinite causal action--observation paths. -/
abbrev CausalTraj (A O : Type*) := ℕ → A × O

/-- The exact finite-history cylinder. -/
def causalCyl (h : CausalHistory A O) : Set (CausalTraj A O) :=
  {ω | ∀ k : Fin h.length, ω k.1 = h[k.1]'k.2}

theorem mem_causalCyl {h : CausalHistory A O} {ω : CausalTraj A O} :
    ω ∈ causalCyl h ↔ ∀ k : Fin h.length, ω k.1 = h[k.1]'k.2 := Iff.rfl

theorem mem_causalCyl_ofFn {n : ℕ} {w : Fin n → A × O} {ω : CausalTraj A O} :
    ω ∈ causalCyl (List.ofFn w) ↔ ∀ j : Fin n, ω j.1 = w j := by
  constructor
  · intro h j
    simpa [List.getElem_ofFn] using h ⟨j.1, by simpa using j.2⟩
  · intro h j
    simpa [List.getElem_ofFn] using h ⟨j.1, by simpa using j.2⟩

theorem measurableSet_causalCyl (h : CausalHistory A O) : MeasurableSet (causalCyl h) := by
  have hrepr : causalCyl h =
      ⋂ k : Fin h.length, (fun ω : CausalTraj A O => ω k.1) ⁻¹' {h[k.1]'k.2} := by
    ext ω
    simp [mem_causalCyl]
  rw [hrepr]
  exact MeasurableSet.iInter fun k =>
    (measurable_pi_apply k.1) (measurableSet_singleton _)

/-- Exact prefix cylinders form a π-system. -/
theorem isPiSystem_range_causalCyl :
    IsPiSystem (range (causalCyl : CausalHistory A O → Set (CausalTraj A O))) := by
  rintro _ ⟨h, rfl⟩ _ ⟨h', rfl⟩ ⟨ω, hω, hω'⟩
  rcases le_total h'.length h.length with hle | hle
  · have hsub : causalCyl h ⊆ causalCyl h' := by
      intro ω' hω2 k
      have hk : k.1 < h.length := lt_of_lt_of_le k.2 hle
      calc
        ω' k.1 = h[k.1]'hk := hω2 ⟨k.1, hk⟩
        _ = ω k.1 := (hω ⟨k.1, hk⟩).symm
        _ = h'[k.1]'k.2 := hω' k
    rw [inter_eq_left.2 hsub]
    exact ⟨h, rfl⟩
  · have hsub : causalCyl h' ⊆ causalCyl h := by
      intro ω' hω2 k
      have hk : k.1 < h'.length := lt_of_lt_of_le k.2 hle
      calc
        ω' k.1 = h'[k.1]'hk := hω2 ⟨k.1, hk⟩
        _ = ω k.1 := (hω' ⟨k.1, hk⟩).symm
        _ = h[k.1]'k.2 := hω k
    rw [inter_eq_right.2 hsub]
    exact ⟨h', rfl⟩

/-- Exact finite-history cylinders generate the product σ-algebra. -/
theorem generateFrom_range_causalCyl :
    (inferInstance : MeasurableSpace (CausalTraj A O)) =
      MeasurableSpace.generateFrom
        (range (causalCyl : CausalHistory A O → Set (CausalTraj A O))) := by
  set G := MeasurableSpace.generateFrom
    (range (causalCyl : CausalHistory A O → Set (CausalTraj A O))) with hG
  apply le_antisymm
  · show (⨆ k : ℕ, MeasurableSpace.comap (fun f : CausalTraj A O => f k)
        (Prod.instMeasurableSpace : MeasurableSpace (A × O))) ≤ G
    refine iSup_le fun k => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    refine MeasurableSpace.le_def.2 fun s _ => ?_
    show MeasurableSet[G] ((fun f : CausalTraj A O => f k) ⁻¹' s)
    have hcoord : ∀ v : A × O,
        MeasurableSet[G] {ω : CausalTraj A O | ω k = v} := by
      intro v
      have hrepr : {ω : CausalTraj A O | ω k = v} =
          ⋃ (w : Fin (k + 1) → A × O) (_ : w (Fin.last k) = v),
            causalCyl (List.ofFn w) := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion, mem_causalCyl_ofFn]
        constructor
        · intro hv
          refine ⟨fun j => ω j.1, ?_, fun j => rfl⟩
          simpa using hv
        · rintro ⟨w, hw, hall⟩
          have hlast := hall (Fin.last k)
          simpa [hw] using hlast
      rw [hrepr]
      exact MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun _ =>
        MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
    have hrepr : ((fun f : CausalTraj A O => f k) ⁻¹' s) =
        ⋃ v ∈ s, {ω : CausalTraj A O | ω k = v} := by
      ext ω
      simp
    rw [hrepr]
    exact (Set.toFinite s).measurableSet_biUnion fun v _ => hcoord v
  · exact MeasurableSpace.generateFrom_le (by
      rintro _ ⟨h, rfl⟩
      exact measurableSet_causalCyl h)

/-- Cylinder characterization of the causal path law. -/
structure IsCausalPathLaw (π : CausalPolicy A O) (Q : CausalResponse A O)
    (μ : Measure (CausalTraj A O)) : Prop where
  isProb : IsProbabilityMeasure μ
  cylinder : ∀ h, μ (causalCyl h) = ENNReal.ofReal (causalTraceProb π Q h)

/-! ## Ionescu--Tulcea construction -/

/-- Internal prefixes contain a dummy coordinate at zero and real history coordinates `1, …, n`. -/
abbrev CausalPrefix (A O : Type*) (n : ℕ) := Π _ : Finset.Iic n, A × O

/-- Drop the dummy coordinate from an internal finite prefix. -/
def causalHistOfPrefix {n : ℕ} (x : CausalPrefix A O n) : CausalHistory A O :=
  List.ofFn fun k : Fin n => x ⟨k.1 + 1, by simp only [Finset.mem_Iic]; omega⟩

noncomputable def causalStepVec (π : CausalPolicy A O) (Q : CausalResponse A O)
    (h : CausalHistory A O) (ao : A × O) : ℝ≥0∞ :=
  ENNReal.ofReal (π h ao.1 * Q h ao.1 ao.2)

theorem sum_causalStepVec [Nonempty O] (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) (h : CausalHistory A O) :
    ∑ ao : A × O, causalStepVec π Q h ao = 1 := by
  unfold causalStepVec
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun ao _ => mul_nonneg ((hπ h).1 ao.1) ((hQ h ao.1).1 ao.2))]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp only [(hQ _ _).2, mul_one, (hπ h).2, ENNReal.ofReal_one]

noncomputable def causalStepPMF [Nonempty O] (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (h : CausalHistory A O) : PMF (A × O) :=
  PMF.ofFintype (causalStepVec π Q h) (sum_causalStepVec π hπ Q hQ h)

noncomputable def causalStepKernel [Nonempty O] (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (n : ℕ) : Kernel (CausalPrefix A O n) (A × O) :=
  Kernel.ofFunOfCountable fun x => (causalStepPMF π hπ Q hQ (causalHistOfPrefix x)).toMeasure

theorem causalStepKernel_apply_singleton [Nonempty O] (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (n : ℕ) (x : CausalPrefix A O n) (ao : A × O) :
    causalStepKernel π hπ Q hQ n x {ao} =
      causalStepVec π Q (causalHistOfPrefix x) ao := by
  change (causalStepPMF π hπ Q hQ (causalHistOfPrefix x)).toMeasure {ao} = _
  rw [PMF.toMeasure_apply_singleton]
  · rfl
  · exact measurableSet_singleton ao

instance isMarkovKernel_causalStepKernel [Nonempty O] (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Q : CausalResponse A O) (hQ : IsCausalResponse Q) (n : ℕ) :
    IsMarkovKernel (causalStepKernel π hπ Q hQ n) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

/-- Internal trajectory law.  Its coordinate zero is an independent dummy. -/
noncomputable def causalRawPathMeasure [Nonempty A] [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) : Measure (ℕ → A × O) :=
  Kernel.trajMeasure (X := fun _ => A × O) (PMF.uniformOfFintype (A × O)).toMeasure
    (causalStepKernel π hπ Q hQ)

instance [Nonempty A] [Nonempty O] (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) :
    IsProbabilityMeasure (causalRawPathMeasure π hπ Q hQ) := by
  unfold causalRawPathMeasure
  infer_instance

/-- Remove the internal dummy coordinate. -/
def causalShift (x : ℕ → A × O) : CausalTraj A O := fun n => x (n + 1)

theorem measurable_causalShift : Measurable (causalShift : (ℕ → A × O) → CausalTraj A O) :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

/-- The public causal path measure. -/
noncomputable def causalPathMeasure [Nonempty A] [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) : Measure (CausalTraj A O) :=
  Measure.map causalShift (causalRawPathMeasure π hπ Q hQ)

instance [Nonempty A] [Nonempty O] (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) :
    IsProbabilityMeasure (causalPathMeasure π hπ Q hQ) :=
  Measure.isProbabilityMeasure_map measurable_causalShift.aemeasurable

def causalPrefixCyl (h : CausalHistory A O) : Set (CausalPrefix A O h.length) :=
  causalHistOfPrefix ⁻¹' {h}

theorem measurableSet_causalPrefixCyl (h : CausalHistory A O) :
    MeasurableSet (causalPrefixCyl h) :=
  (Set.toFinite (causalPrefixCyl h)).measurableSet

theorem preimage_causalShift_cyl_eq (h : CausalHistory A O) :
    causalShift ⁻¹' causalCyl h =
      Preorder.frestrictLe h.length ⁻¹' causalPrefixCyl h := by
  ext x
  change (∀ k : Fin h.length, x (k.1 + 1) = h[k.1]'k.2) ↔
    List.ofFn (fun k : Fin h.length => x (k.1 + 1)) = h
  constructor
  · intro hall
    calc
      List.ofFn (fun k : Fin h.length => x (k.1 + 1)) = List.ofFn h.get :=
        List.ofFn_inj.mpr (funext hall)
      _ = h := List.ofFn_get h
  · intro heq k
    have heqFn : (fun j : Fin h.length => x (j.1 + 1)) = h.get := by
      rw [← List.ofFn_inj]
      exact heq.trans (List.ofFn_get h).symm
    exact congrFun heqFn k

theorem preimage_causalShift_cyl_snoc (l : CausalHistory A O) (ao : A × O) :
    causalShift ⁻¹' causalCyl (l ++ [ao]) =
      (fun x : ℕ → A × O =>
        (Preorder.frestrictLe l.length x, x (l.length + 1))) ⁻¹'
          (causalPrefixCyl l ×ˢ ({ao} : Set (A × O))) := by
  ext x
  have hfirst : (Preorder.frestrictLe l.length x ∈ causalPrefixCyl l) ↔
      ∀ k : Fin l.length, x (k.1 + 1) = l[k.1]'k.2 := by
    change (x ∈ Preorder.frestrictLe l.length ⁻¹' causalPrefixCyl l) ↔ _
    rw [← preimage_causalShift_cyl_eq]
    rfl
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, hfirst,
    mem_causalCyl, causalShift]
  constructor
  · intro hall
    constructor
    · intro k
      have hk : k.1 < (l ++ [ao]).length := by simp
      simpa [List.getElem_append_left k.2] using hall ⟨k.1, hk⟩
    · have hk : l.length < (l ++ [ao]).length := by simp
      simpa [List.getElem_concat_length] using hall ⟨l.length, hk⟩
  · rintro ⟨hhead, hlast⟩ k
    have hk : k.1 < l.length + 1 := by simpa using k.2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · simpa [List.getElem_append_left hlt] using hhead ⟨k.1, hlt⟩
    · simp only [heq]
      simpa [List.getElem_concat_length] using hlast

theorem causalRawPath_prefixCyl_eq [Nonempty A] [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) (h : CausalHistory A O) :
    ((causalRawPathMeasure π hπ Q hQ).map (Preorder.frestrictLe h.length))
        (causalPrefixCyl h) =
      causalRawPathMeasure π hπ Q hQ (causalShift ⁻¹' causalCyl h) := by
  rw [Measure.map_apply (Preorder.measurable_frestrictLe _) (measurableSet_causalPrefixCyl _),
    ← preimage_causalShift_cyl_eq]

theorem causalRawPath_shift_cyl_snoc [Nonempty A] [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (l : CausalHistory A O) (ao : A × O) :
    causalRawPathMeasure π hπ Q hQ (causalShift ⁻¹' causalCyl (l ++ [ao])) =
      causalStepVec π Q l ao *
        causalRawPathMeasure π hπ Q hQ (causalShift ⁻¹' causalCyl l) := by
  have hmap : Measurable fun x : ℕ → A × O =>
      (Preorder.frestrictLe l.length x, x (l.length + 1)) := by fun_prop
  have hprod : MeasurableSet (causalPrefixCyl l ×ˢ ({ao} : Set (A × O))) :=
    (measurableSet_causalPrefixCyl _).prod (measurableSet_singleton _)
  rw [preimage_causalShift_cyl_snoc, ← Measure.map_apply hmap hprod]
  have hkey :
      (causalRawPathMeasure π hπ Q hQ).map (Preorder.frestrictLe l.length) ⊗ₘ
          causalStepKernel π hπ Q hQ l.length =
        (causalRawPathMeasure π hπ Q hQ).map
          (fun x => (Preorder.frestrictLe l.length x, x (l.length + 1))) := by
    unfold causalRawPathMeasure
    exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  rw [← hkey]
  calc
    (((causalRawPathMeasure π hπ Q hQ).map (Preorder.frestrictLe l.length)) ⊗ₘ
        causalStepKernel π hπ Q hQ l.length)
          (causalPrefixCyl l ×ˢ ({ao} : Set (A × O)))
      = ∫⁻ x in causalPrefixCyl l, causalStepKernel π hπ Q hQ l.length x {ao}
          ∂((causalRawPathMeasure π hπ Q hQ).map (Preorder.frestrictLe l.length)) :=
        Measure.compProd_apply_prod (measurableSet_causalPrefixCyl _)
          (measurableSet_singleton _)
    _ = ∫⁻ _ in causalPrefixCyl l, causalStepVec π Q l ao
          ∂((causalRawPathMeasure π hπ Q hQ).map (Preorder.frestrictLe l.length)) := by
        refine setLIntegral_congr_fun (measurableSet_causalPrefixCyl _) (fun x hx => ?_)
        rw [causalStepKernel_apply_singleton]
        exact congrArg (fun h' => causalStepVec π Q h' ao) hx
    _ = causalStepVec π Q l ao *
          ((causalRawPathMeasure π hπ Q hQ).map (Preorder.frestrictLe l.length))
            (causalPrefixCyl l) := setLIntegral_const _ _
    _ = causalStepVec π Q l ao *
          causalRawPathMeasure π hπ Q hQ (causalShift ⁻¹' causalCyl l) :=
        congrArg (causalStepVec π Q l ao * ·)
          (causalRawPath_prefixCyl_eq π hπ Q hQ l)

theorem causalPathMeasure_cyl [Nonempty A] [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) (h : CausalHistory A O) :
    causalPathMeasure π hπ Q hQ (causalCyl h) =
      ENNReal.ofReal (causalTraceProb π Q h) := by
  rw [causalPathMeasure, Measure.map_apply measurable_causalShift (measurableSet_causalCyl _)]
  induction h using List.reverseRecOn with
  | nil => simp [causalCyl, causalTraceProb, causalTraceProbFrom]
  | append_singleton l ao ih =>
      rw [causalRawPath_shift_cyl_snoc π hπ Q hQ l ao, ih,
        causalTraceProb_append_singleton]
      unfold causalStepVec
      rw [← ENNReal.ofReal_mul
        (mul_nonneg ((hπ l).1 ao.1) ((hQ l ao.1).1 ao.2))]
      congr 1
      ring

theorem isCausalPathLaw_causalPathMeasure [Nonempty A] [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) :
    IsCausalPathLaw π Q (causalPathMeasure π hπ Q hQ) :=
  ⟨inferInstance, causalPathMeasure_cyl π hπ Q hQ⟩

/-- Existence of the path law for the paper's current arbitrary causal response kernels. -/
theorem causalPathLaw_exists (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) :
    ∃ μ : Measure (CausalTraj A O), IsCausalPathLaw π Q μ := by
  have hA : Nonempty A := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have h1 := (hπ []).2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  letI : Nonempty A := hA
  obtain ⟨a⟩ := hA
  have hO : Nonempty O := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have h1 := (hQ [] a).2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  letI : Nonempty O := hO
  exact ⟨causalPathMeasure π hπ Q hQ, isCausalPathLaw_causalPathMeasure π hπ Q hQ⟩

/-- Cylinder probabilities uniquely determine the current causal path law. -/
theorem causalPathLaw_unique (π : CausalPolicy A O) (Q : CausalResponse A O)
    {μ ν : Measure (CausalTraj A O)}
    (hμ : IsCausalPathLaw π Q μ) (hν : IsCausalPathLaw π Q ν) : μ = ν := by
  have := hμ.isProb
  have := hν.isProb
  refine ext_of_generate_finite _ generateFrom_range_causalCyl isPiSystem_range_causalCyl ?_ ?_
  · rintro _ ⟨h, rfl⟩
    rw [hμ.cylinder, hν.cylinder]
  · rw [measure_univ, measure_univ]

end IdExp
