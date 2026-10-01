/-
The Ionescu–Tulcea construction for the retained finite-POMDP `pathLaw_exists`.
This layer includes a standalone initial observation; see `Basic.lean` and the
interface conventions in `Formal/README.md`.

Mathlib's `trajMeasure μ₀ κ` builds the law of an infinite trajectory in
`Π n, X n` from an initial law and step kernels.  With `X n := A × O` throughout
(the time-0 action is a dummy), a policy `π` and a valid POMDP `M` determine
* the step kernel `stepKernel π M n`: from a prefix `x : Π i : Iic n, A × O`
  read off the history `histOfPrefix x`, choose `a ~ π`, then `o' ~ nextObs`;
* the initial law `initPMF M`: uniform dummy action times `traceLik M (o, [])`.
This file defines them and proves they are probability laws / Markov kernels.
The cylinder computation below proves that the pushforward to
`O × (A × O)^ℕ` has the `IsPathLaw` cylinder probabilities.
-/
import Formal.Nonneg
import Formal.PathLaw
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

set_option linter.unusedSectionVars false

namespace IdExp

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {A O : Type*} [Fintype A] [Fintype O] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- The initial-observation law is the trace likelihood of the empty history, and it
sums to one. -/
theorem sum_traceLik_nil (M : POMDP A O) (hM : M.Valid) :
    ∑ o : O, traceLik M (o, []) = 1 := by
  simp only [traceLik, fwd, List.foldl_nil]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [hM.2.2.2.2.2, mul_one, hM.2.1]

/-- Time-`n` prefixes of Mathlib's trajectory space with the constant fibre `A × O`. -/
abbrev Prefix (A O : Type*) (n : ℕ) := Π _ : Finset.Iic n, A × O

/-- The history encoded by a prefix: the observation at time 0 (whose action is a
dummy) followed by the steps at times `1, …, n`. -/
def histOfPrefix {n : ℕ} (x : Prefix A O n) : Hist A O :=
  ((x ⟨0, by simp⟩).2,
    List.ofFn fun k : Fin n => x ⟨k.1 + 1, by simp only [Finset.mem_Iic]; omega⟩)

/-! ### The step kernel -/

/-- Probability vector of the next `(action, observation)` pair at history `h`. -/
noncomputable def stepVec (π : Policy A O) (M : POMDP A O) (h : Hist A O)
    (ao : A × O) : ℝ≥0∞ :=
  ENNReal.ofReal (π h ao.1 * nextObs M h ao.1 ao.2)

theorem sum_stepVec [Nonempty O] (π : Policy A O) (hπ : IsPolicy π) (M : POMDP A O)
    (hM : M.Valid) (h : Hist A O) : ∑ ao : A × O, stepVec π M h ao = 1 := by
  unfold stepVec
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun ao _ => mul_nonneg ((hπ h).1 ao.1) (nextObs_nonneg M hM h ao.1 ao.2))]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp only [sum_nextObs M hM h, mul_one, (hπ h).2, ENNReal.ofReal_one]

noncomputable def stepPMF [Nonempty O] (π : Policy A O) (hπ : IsPolicy π) (M : POMDP A O)
    (hM : M.Valid) (h : Hist A O) : PMF (A × O) :=
  PMF.ofFintype (stepVec π M h) (sum_stepVec π hπ M hM h)

noncomputable def stepKernel [Nonempty O] (π : Policy A O) (hπ : IsPolicy π) (M : POMDP A O)
    (hM : M.Valid) (n : ℕ) : Kernel (Prefix A O n) (A × O) :=
  Kernel.ofFunOfCountable fun x => (stepPMF π hπ M hM (histOfPrefix x)).toMeasure

theorem stepKernel_apply_singleton [Nonempty O] (p : Policy A O) (hp : IsPolicy p)
    (M : POMDP A O) (hM : M.Valid) (n : ℕ) (x : Prefix A O n) (ao : A × O) :
    stepKernel p hp M hM n x {ao} = stepVec p M (histOfPrefix x) ao := by
  change (stepPMF p hp M hM (histOfPrefix x)).toMeasure {ao} = _
  rw [PMF.toMeasure_apply_singleton]
  · rfl
  · exact measurableSet_singleton _

instance isMarkovKernel_stepKernel [Nonempty O] (π : Policy A O) (hπ : IsPolicy π)
    (M : POMDP A O) (hM : M.Valid) (n : ℕ) : IsMarkovKernel (stepKernel π hπ M hM n) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

/-! ### The initial law -/

/-- Uniform dummy action at time 0, observation by the initial-observation law. -/
noncomputable def initVec [Nonempty A] (M : POMDP A O) (ao : A × O) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / Fintype.card A : ℝ) * traceLik M (ao.2, []))

theorem sum_initVec [Nonempty A] (M : POMDP A O) (hM : M.Valid) :
    ∑ ao : A × O, initVec M ao = 1 := by
  unfold initVec
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun ao _ => mul_nonneg (by positivity) (traceLik_nonneg M hM _))]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp only [sum_traceLik_nil M hM, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [one_div_mul_cancel (by exact_mod_cast Fintype.card_ne_zero), ENNReal.ofReal_one]

noncomputable def initPMF [Nonempty A] (M : POMDP A O) (hM : M.Valid) : PMF (A × O) :=
  PMF.ofFintype (initVec M) (sum_initVec M hM)

theorem initPMF_apply_singleton [Nonempty A] (M : POMDP A O) (hM : M.Valid)
    (ao : A × O) : (initPMF M hM).toMeasure {ao} = initVec M ao := by
  rw [PMF.toMeasure_apply_singleton]
  · rfl
  · exact measurableSet_singleton _


/-- The dummy action sums out, leaving the correct initial-observation law. -/
theorem initPMF_map_snd [Nonempty A] (M : POMDP A O) (hM : M.Valid) (o : O) :
    (initPMF M hM).map Prod.snd o = ENNReal.ofReal (traceLik M (o, [])) := by
  classical
  rw [PMF.map_apply]
  simp only [initPMF, PMF.ofFintype_apply, initVec]
  rw [tsum_fintype, Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_eq Finset.univ o]
  simp [Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _
/-- The Ionescu–Tulcea trajectory law on `Π n, A × O`. -/
noncomputable def pathMeasure [Nonempty A] [Nonempty O] (π : Policy A O) (hπ : IsPolicy π)
    (M : POMDP A O) (hM : M.Valid) : Measure (Π _ : ℕ, A × O) :=
  Kernel.trajMeasure (X := fun _ => A × O) (initPMF M hM).toMeasure (stepKernel π hπ M hM)

instance [Nonempty A] [Nonempty O] (π : Policy A O) (hπ : IsPolicy π) (M : POMDP A O)
    (hM : M.Valid) : IsProbabilityMeasure (pathMeasure π hπ M hM) := by
  unfold pathMeasure
  infer_instance

/-! ### Pushforward to the observable path space -/

/-- Drop the dummy time-0 action and retain its observation. -/
def toPath (x : ℕ → A × O) : Traj A O :=
  ((x 0).2, fun n => x (n + 1))

theorem measurable_toPath : Measurable (toPath : (ℕ → A × O) → Traj A O) := by
  apply Measurable.prod
  · exact (measurable_pi_apply 0).snd
  · exact measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)


/-- The finite marginal at time zero is the initial law, packaged on `Iic 0`. -/
theorem pathMeasure_map_frestrictLe_zero [Nonempty A] [Nonempty O]
    (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O) (hM : M.Valid) :
    (pathMeasure p hp M hM).map (Preorder.frestrictLe 0) =
      (initPMF M hM).toMeasure.map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => A × O)).symm := by
  unfold pathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe_of_le le_rfl, Measure.deterministic_comp_eq_map]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- The coordinate at trajectory time zero has exactly the initial PMF law. -/
theorem pathMeasure_map_zero [Nonempty A] [Nonempty O]
    (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O) (hM : M.Valid) :
    (pathMeasure p hp M hM).map (fun x => x 0) = (initPMF M hM).toMeasure := by
  calc
    _ = ((pathMeasure p hp M hM).map (Preorder.frestrictLe 0)).map
          (fun x => x ⟨0, by simp⟩) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = ((initPMF M hM).toMeasure.map
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => A × O)).symm).map
          (fun x => x ⟨0, by simp⟩) := by rw [pathMeasure_map_frestrictLe_zero]
    _ = _ := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      convert Measure.map_id
      congr 1
/-- Candidate observable path law obtained from the Ionescu--Tulcea trajectory. -/
noncomputable def pathLawMeasure [Nonempty A] [Nonempty O] (p : Policy A O) (hp : IsPolicy p)
    (M : POMDP A O) (hM : M.Valid) : Measure (Traj A O) :=
  Measure.map toPath (pathMeasure p hp M hM)

instance [Nonempty A] [Nonempty O] (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O)
    (hM : M.Valid) : IsProbabilityMeasure (pathLawMeasure p hp M hM) := by
  constructor
  rw [pathLawMeasure, Measure.map_apply measurable_toPath MeasurableSet.univ]
  simp

/-- Pulling a history cylinder back through `toPath` fixes the observation at
trajectory time zero and the action--observation pairs at times `1, ..., n`. -/
theorem mem_preimage_toPath_cyl {h : Hist A O} {x : ℕ → A × O} :
    x ∈ toPath ⁻¹' cyl h ↔
      (x 0).2 = h.1 ∧ ∀ k : Fin h.2.length, x (k.1 + 1) = h.2[k.1]'k.2 := by
  rw [Set.mem_preimage, mem_cyl]
  rfl

/-- The finite-prefix event that encodes exactly history `h`; the dummy action at
coordinate zero remains unconstrained. -/
def prefixCyl (h : Hist A O) : Set (Prefix A O h.2.length) :=
  histOfPrefix ⁻¹' {h}

theorem measurableSet_prefixCyl (h : Hist A O) : MeasurableSet (prefixCyl h) := by
  exact (Set.toFinite (prefixCyl h)).measurableSet

/-- An infinite trajectory is in the pulled-back history cylinder exactly when
its finite marginal through the history length is in `prefixCyl`. -/
theorem preimage_toPath_cyl_eq (h : Hist A O) :
    toPath ⁻¹' cyl h = Preorder.frestrictLe h.2.length ⁻¹' prefixCyl h := by
  ext x
  rw [mem_preimage_toPath_cyl]
  change ((x 0).2 = h.1 ∧ ∀ k : Fin h.2.length,
    x (k.1 + 1) = h.2[k.1]'k.2) ↔ histOfPrefix (Preorder.frestrictLe h.2.length x) = h
  unfold histOfPrefix
  simp only [Preorder.frestrictLe_apply]
  constructor
  · rintro ⟨ho, hs⟩
    apply Prod.ext
    · exact ho
    · change List.ofFn (fun k : Fin h.2.length => x (k.1 + 1)) = h.2
      calc
        List.ofFn (fun k : Fin h.2.length => x (k.1 + 1)) = List.ofFn h.2.get :=
          List.ofFn_inj.mpr (funext fun k => hs k)
        _ = h.2 := List.ofFn_get h.2
  · intro heq
    have ho := congrArg Prod.fst heq
    have ho := congrArg Prod.fst heq
    have hl := congrArg Prod.snd heq
    constructor
    · exact ho
    · intro k
      have heqFn : (fun j : Fin h.2.length => x (j.1 + 1)) = h.2.get := by
        rw [← List.ofFn_inj]
        exact hl.trans (List.ofFn_get h.2).symm
      exact congrFun heqFn k
/-- Cylinder probability for a history with no action--observation steps. -/
theorem pathLawMeasure_cyl_nil [Nonempty A] [Nonempty O]
    (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O) (hM : M.Valid) (o : O) :
    pathLawMeasure p hp M hM (cyl (o, [])) = ENNReal.ofReal (traceProb p M (o, [])) := by
  rw [pathLawMeasure, Measure.map_apply measurable_toPath (measurableSet_cyl _)]
  have hevent : toPath ⁻¹' cyl (o, []) = (fun x : ℕ → A × O => (x 0).2) ⁻¹' {o} := by
    ext x
    simp [mem_cyl_nil, toPath]
  rw [hevent, ← Measure.map_apply (by fun_prop) (measurableSet_singleton o)]
  have hmap : (pathMeasure p hp M hM).map (fun x => (x 0).2) =
      ((initPMF M hM).map Prod.snd).toMeasure := by
    calc
      _ = ((pathMeasure p hp M hM).map (fun x => x 0)).map Prod.snd := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
      _ = (initPMF M hM).toMeasure.map Prod.snd := by rw [pathMeasure_map_zero]
      _ = _ := PMF.toMeasure_map _ _ (by fun_prop)
  rw [hmap, PMF.toMeasure_apply_singleton]
  · rw [initPMF_map_snd]
    simp [traceProb, polWeight, polWeightAux]
  · exact measurableSet_singleton _


/-! ### The cylinder computation -/

/-- Peeling the last step off a pulled-back history cylinder: a trajectory lies in
the cylinder of `(o, l ++ [ao])` iff its length-`|l|` marginal encodes `(o, l)` and
the next coordinate is exactly `ao`. -/
theorem preimage_toPath_cyl_snoc (o : O) (l : List (A × O)) (ao : A × O) :
    toPath ⁻¹' cyl (o, l ++ [ao]) =
      (fun x : ℕ → A × O => (Preorder.frestrictLe l.length x, x (l.length + 1))) ⁻¹'
        (prefixCyl (o, l) ×ˢ ({ao} : Set (A × O))) := by
  ext x
  have hfirst : (Preorder.frestrictLe l.length x ∈ prefixCyl (o, l)) ↔
      ((x 0).2 = o ∧ ∀ k : Fin l.length, x (k.1 + 1) = l[k.1]'k.2) := by
    change (x ∈ Preorder.frestrictLe ((o, l) : Hist A O).2.length ⁻¹' prefixCyl (o, l)) ↔ _
    rw [← preimage_toPath_cyl_eq]
    exact mem_preimage_toPath_cyl
  rw [mem_preimage_toPath_cyl]
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, hfirst]
  constructor
  · rintro ⟨ho, hs⟩
    refine ⟨⟨ho, fun k => ?_⟩, ?_⟩
    · have hk : (k.1 : ℕ) < (l ++ [ao]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hstep := hs ⟨k.1, hk⟩
      simpa [List.getElem_append_left k.2] using hstep
    · have hk : l.length < (l ++ [ao]).length := by
        simp [List.length_append]
      have hstep := hs ⟨l.length, hk⟩
      simpa [List.getElem_concat_length] using hstep
  · rintro ⟨⟨ho, hs⟩, hlast⟩
    refine ⟨ho, fun k => ?_⟩
    have hk1 : (k.1 : ℕ) < l.length + 1 := by
      have hk2 := k.2
      simpa [List.length_append] using hk2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk1 with hlt | heq
    · have hstep := hs ⟨k.1, hlt⟩
      simpa [List.getElem_append_left hlt] using hstep
    · simp only [heq]
      simpa [List.getElem_concat_length] using hlast

/-- The marginal of the trajectory law through a history's length, evaluated on the
prefix event of that history, is the trajectory mass of the pulled-back cylinder. -/
theorem pathMeasure_prefixCyl_eq [Nonempty A] [Nonempty O]
    (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O) (hM : M.Valid) (h : Hist A O) :
    ((pathMeasure p hp M hM).map (Preorder.frestrictLe h.2.length)) (prefixCyl h) =
      pathMeasure p hp M hM (toPath ⁻¹' cyl h) := by
  rw [Measure.map_apply (Preorder.measurable_frestrictLe _) (measurableSet_prefixCyl _),
    ← preimage_toPath_cyl_eq]

/-- One-step recursion for the trajectory mass of a pulled-back cylinder: appending a
step multiplies by the step-kernel weight of that step at the current history. -/
theorem pathMeasure_toPath_cyl_snoc [Nonempty A] [Nonempty O]
    (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O) (hM : M.Valid)
    (o : O) (l : List (A × O)) (ao : A × O) :
    pathMeasure p hp M hM (toPath ⁻¹' cyl (o, l ++ [ao])) =
      stepVec p M (o, l) ao * pathMeasure p hp M hM (toPath ⁻¹' cyl (o, l)) := by
  have hmap : Measurable fun x : ℕ → A × O =>
      (Preorder.frestrictLe l.length x, x (l.length + 1)) := by fun_prop
  have hprod : MeasurableSet (prefixCyl (o, l) ×ˢ ({ao} : Set (A × O))) :=
    (measurableSet_prefixCyl _).prod (measurableSet_singleton _)
  rw [preimage_toPath_cyl_snoc, ← Measure.map_apply hmap hprod]
  have hkey :
      (pathMeasure p hp M hM).map
          (fun x => (Preorder.frestrictLe l.length x, x (l.length + 1))) =
        (pathMeasure p hp M hM).map (Preorder.frestrictLe l.length) ⊗ₘ
          stepKernel p hp M hM l.length := by
    unfold pathMeasure
    exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
  have hpm : IsProbabilityMeasure
      ((pathMeasure p hp M hM).map (Preorder.frestrictLe l.length)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [hkey]
  calc
    (((pathMeasure p hp M hM).map (Preorder.frestrictLe l.length)) ⊗ₘ
        stepKernel p hp M hM l.length) (prefixCyl (o, l) ×ˢ ({ao} : Set (A × O)))
      = ∫⁻ x in prefixCyl (o, l), stepKernel p hp M hM l.length x {ao}
          ∂((pathMeasure p hp M hM).map (Preorder.frestrictLe l.length)) :=
        Measure.compProd_apply_prod (measurableSet_prefixCyl _) (measurableSet_singleton _)
    _ = ∫⁻ _ in prefixCyl (o, l), stepVec p M (o, l) ao
        ∂((pathMeasure p hp M hM).map (Preorder.frestrictLe l.length)) := by
        refine setLIntegral_congr_fun (measurableSet_prefixCyl _) (fun x hx => ?_)
        rw [stepKernel_apply_singleton]
        exact congrArg (fun h' => stepVec p M h' ao) hx
    _ = stepVec p M (o, l) ao *
        ((pathMeasure p hp M hM).map (Preorder.frestrictLe l.length)) (prefixCyl (o, l)) :=
        setLIntegral_const _ _
    _ = stepVec p M (o, l) ao * pathMeasure p hp M hM (toPath ⁻¹' cyl (o, l)) :=
        congrArg (stepVec p M (o, l) ao * ·) (pathMeasure_prefixCyl_eq p hp M hM (o, l))

/-- The pushforward trajectory law gives every history cylinder its trace
probability: `pathLawMeasure` has the `IsPathLaw` cylinder values. -/
theorem pathLawMeasure_cyl [Nonempty A] [Nonempty O]
    (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O) (hM : M.Valid) (h : Hist A O) :
    pathLawMeasure p hp M hM (cyl h) = ENNReal.ofReal (traceProb p M h) := by
  rw [pathLawMeasure, Measure.map_apply measurable_toPath (measurableSet_cyl _)]
  obtain ⟨o, l⟩ := h
  induction l using List.reverseRecOn with
  | nil =>
      have hbase := pathLawMeasure_cyl_nil p hp M hM o
      rwa [pathLawMeasure,
        Measure.map_apply measurable_toPath (measurableSet_cyl _)] at hbase
  | append_singleton l ao ih =>
      obtain ⟨a, o'⟩ := ao
      rw [pathMeasure_toPath_cyl_snoc p hp M hM o l (a, o'), ih,
        show traceProb p M (o, l ++ [(a, o')]) =
            traceProb p M (o, l) * p (o, l) a * nextObs M (o, l) a o' from
          traceProb_append p M hM (o, l) a o']
      unfold stepVec
      dsimp only
      rw [← ENNReal.ofReal_mul
        (mul_nonneg ((hp (o, l)).1 a) (nextObs_nonneg M hM (o, l) a o'))]
      congr 1
      ring

/-- `pathLawMeasure` is a path law: existence half of the path-law
construction. -/
theorem isPathLaw_pathLawMeasure [Nonempty A] [Nonempty O]
    (p : Policy A O) (hp : IsPolicy p) (M : POMDP A O) (hM : M.Valid) :
    IsPathLaw p M (pathLawMeasure p hp M hM) :=
  ⟨inferInstance, pathLawMeasure_cyl p hp M hM⟩

end IdExp
