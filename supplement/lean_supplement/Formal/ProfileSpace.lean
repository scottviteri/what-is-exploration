import Mathlib
import Formal.Frontier

/-!
# The concrete profile space

Instantiates the abstract compact-order lemma of `Frontier.lean` on the concrete native
capability profile cube `ℕ → [0,1]` of the causal-first paper
(`Paper/draft/main.tex`, Theorem `thm:profile-frontier`;
`TheoryDocs/native_test_geometry.tex`, Theorem `thm:profile`): one limiting deficiency
coordinate per enumerated native test, ordered coordinatewise, smaller deficiency more
capable.

Machine-checked here: the cube is a compact space; the graph of coordinatewise order and
coordinatewise down-sets are closed;
in every **closed** set of profiles, every profile is dominated (coordinatewise ≤, i.e.
weakly more capable everywhere) by a Pareto-minimal profile of that set — the frontier
is nonempty and above every point; and the zero profile, when present, is the unique
minimal point.  `CausalProfile.lean` constructs the paper's actual `𝒫`
(the closure of the attainable profiles `{p(π)}`) inside this cube and proves
that its coordinates are the limiting Le Cam deficiencies to the enumerated
native tests.
-/

namespace IdExp

open Set

/-- Minimal elements below every point: the order dual of
`exists_maximal_of_compactSpace`. -/
theorem exists_minimal_of_compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Preorder X] (hclosed : ∀ x : X, IsClosed (Iic x)) (x : X) :
    ∃ m, m ≤ x ∧ ∀ y, y ≤ m → m ≤ y := by
  haveI : CompactSpace Xᵒᵈ := ‹CompactSpace X›
  obtain ⟨m, hxm, hmax⟩ :=
    exists_maximal_of_compactSpace (X := Xᵒᵈ)
      (fun z => hclosed (OrderDual.ofDual z)) (OrderDual.toDual x)
  exact ⟨OrderDual.ofDual m, hxm, fun y hy => hmax (OrderDual.toDual y) hy⟩

/-- The native capability profile cube: one deficiency coordinate in `[0,1]` per
enumerated native test. -/
abbrev ProfileCube : Type := ℕ → Set.Icc (0 : ℝ) 1

instance : CompactSpace ProfileCube := by
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  infer_instance

/-- Coordinatewise down-sets of the profile cube are closed. -/
theorem isClosed_Iic_profile (q : ProfileCube) : IsClosed (Iic q) := by
  have h : Iic q = ⋂ j, {p : ProfileCube | ((p j : ℝ)) ≤ ((q j : ℝ))} := by
    ext p
    simp only [mem_Iic, Set.mem_iInter, Set.mem_ofPred_eq, Pi.le_def]
    exact forall_congr' fun j => Iff.symm Subtype.coe_le_coe
  rw [h]
  exact isClosed_iInter fun j =>
    isClosed_le (continuous_subtype_val.comp (continuous_apply j)) continuous_const

/-- The graph of coordinatewise order on the profile cube is closed.  This is the
concrete `closed preorder` assertion used in the paper's compact-frontier theorem. -/
theorem isClosed_profileOrder :
    IsClosed {pq : ProfileCube × ProfileCube | pq.1 ≤ pq.2} := by
  have h : {pq : ProfileCube × ProfileCube | pq.1 ≤ pq.2} =
      ⋂ j, {pq : ProfileCube × ProfileCube |
        ((pq.1 j : Set.Icc (0 : ℝ) 1) : ℝ) ≤ ((pq.2 j : Set.Icc (0 : ℝ) 1) : ℝ)} := by
    ext pq
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Pi.le_def, Subtype.coe_le_coe]
  rw [h]
  exact isClosed_iInter fun j => by
    have hleft : Continuous (fun pq : ProfileCube × ProfileCube => (pq.1 j : ℝ)) := by
      fun_prop
    have hright : Continuous (fun pq : ProfileCube × ProfileCube => (pq.2 j : ℝ)) := by
      fun_prop
    exact isClosed_le hleft hright

/-- **The concrete Pareto frontier** (order/topology content of the compact-profile
theorem, concrete instance).  In any closed set of native capability profiles, every
profile is dominated — coordinatewise smaller deficiency — by a Pareto-admissible
(minimal) profile of the same set.  The frontier of a closed profile set is nonempty
and sits above every attainable point. -/
theorem exists_pareto_profile {S : Set ProfileCube} (hS : IsClosed S)
    {p : ProfileCube} (hp : p ∈ S) :
    ∃ m ∈ S, m ≤ p ∧ ∀ q ∈ S, q ≤ m → m ≤ q := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  have hIic : ∀ x : S, IsClosed (Iic x) := by
    intro x
    have h : (Iic x : Set S) = Subtype.val ⁻¹' (Iic (x : ProfileCube)) := by
      ext y
      simp [Set.mem_Iic]
    rw [h]
    exact (isClosed_Iic_profile _).preimage continuous_subtype_val
  obtain ⟨m, hmp, hmin⟩ := exists_minimal_of_compactSpace hIic (⟨p, hp⟩ : S)
  exact ⟨m, m.2, hmp, fun q hq hqm => hmin ⟨q, hq⟩ hqm⟩

/-- The zero profile: every native deficiency zero — complete exploration. -/
def zeroProfile : ProfileCube := fun _ => ⟨0, by norm_num⟩

/-- Zero deficiency everywhere dominates every profile. -/
theorem zeroProfile_le (p : ProfileCube) : zeroProfile ≤ p := fun j => (p j).2.1

/-- If the zero profile lies in the set, it is the unique Pareto-minimal profile:
native sufficiency is attainment of the unique frontier point. -/
theorem eq_zeroProfile_of_minimal {S : Set ProfileCube} (hz : zeroProfile ∈ S)
    {m : ProfileCube} (hm : m ∈ S) (hmin : ∀ q ∈ S, q ≤ m → m ≤ q) :
    m = zeroProfile :=
  le_antisymm (hmin zeroProfile hz (zeroProfile_le m)) (zeroProfile_le m)

end IdExp
