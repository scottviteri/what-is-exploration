import Formal.DualCertificate

/-!
# Effective-binary reductions for finite experiments

The paper's effective-binary theorem assumes that every named world's acquired
row and every target row use the same affine coordinate between two named
anchors.  FiniteTV.finiteTV_affine_le_max proves the pointwise norm
inequality.  This file closes the outer optimizer layer:

* post-processing preserves the common affine coordinate;
* every fixed decoder's worst-world error is attained at one of the anchors;
* the full-class and two-anchor deficiency candidate sets, hence their
  infima, are exactly equal; and
* the same reduction holds for an arbitrary admissible family of decoders.

The last formulation deliberately abstracts the constraint defining a
coherent causal model.  Since admissibility is world-independent, restricting
the parameter class changes only the error quantifier.  Thus the theorem
applies to separate decoders, coherent decoder families, and any stronger
world-independent reconstruction constraint without re-proving the affine
argument.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset Set

variable {Theta X Y I : Type*} [Fintype X] [Fintype Y]

/-- Restrict a parameter-indexed experiment to two named anchors. -/
def binaryAnchorRestriction (E : FiniteExperiment Theta X)
    (theta0 theta1 : Theta) : FiniteExperiment Bool X
  | false => E theta0
  | true => E theta1

@[simp] theorem binaryAnchorRestriction_false
    (E : FiniteExperiment Theta X) (theta0 theta1 : Theta) :
    binaryAnchorRestriction E theta0 theta1 false = E theta0 := rfl

@[simp] theorem binaryAnchorRestriction_true
    (E : FiniteExperiment Theta X) (theta0 theta1 : Theta) :
    binaryAnchorRestriction E theta0 theta1 true = E theta1 := rfl

/-- A source-target pair has a common affine coordinate when the same bounded
coefficient interpolates both rows between two named worlds. The named rows
need not occur at coefficients zero and one; this is the literal hypothesis
used by the paper's effective-binary corollary. -/
structure CommonAffine
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) where
  lam : Theta -> Real
  lam_nonneg : forall theta, 0 <= lam theta
  lam_le_one : forall theta, lam theta <= 1
  source_affine : forall theta x,
    E theta x = (1 - lam theta) * E theta0 x + lam theta * E theta1 x
  target_affine : forall theta y,
    F theta y = (1 - lam theta) * F theta0 y + lam theta * F theta1 y

/-- A source-target pair has one common binary-affine signature when the same
coefficient interpolates both rows between two named anchors.  The endpoint
equalities record the paper's named-anchor convention; the reduction proof
uses only the row identities and coefficient bounds. -/
structure CommonBinaryAffine
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) where
  lam : Theta -> Real
  lam_nonneg : forall theta, 0 <= lam theta
  lam_le_one : forall theta, lam theta <= 1
  lam_theta0 : lam theta0 = 0
  lam_theta1 : lam theta1 = 1
  source_affine : forall theta x,
    E theta x = (1 - lam theta) * E theta0 x + lam theta * E theta1 x
  target_affine : forall theta y,
    F theta y = (1 - lam theta) * F theta0 y + lam theta * F theta1 y
/-- Forget the endpoint normalization of a common binary-affine signature. -/
def CommonBinaryAffine.toCommonAffine
    {E : FiniteExperiment Theta X} {F : FiniteExperiment Theta Y}
    {theta0 theta1 : Theta}
    (h : CommonBinaryAffine E F theta0 theta1) :
    CommonAffine E F theta0 theta1 where
  lam := h.lam
  lam_nonneg := h.lam_nonneg
  lam_le_one := h.lam_le_one
  source_affine := h.source_affine
  target_affine := h.target_affine


/-- Matrix post-processing commutes with a common affine interpolation of
source rows. -/
theorem finiteDecisionLaw_affine
    (E : FiniteExperiment Theta X) (G : X -> Y -> Real)
    (theta theta0 theta1 : Theta) (lam : Real)
    (hE : forall x, E theta x = (1 - lam) * E theta0 x + lam * E theta1 x) :
    finiteDecisionLaw E G theta =
      fun y => (1 - lam) * finiteDecisionLaw E G theta0 y +
        lam * finiteDecisionLaw E G theta1 y := by
  funext y
  unfold finiteDecisionLaw
  calc
    (∑ x, E theta x * G x y) =
        ∑ x, ((1 - lam) * (E theta0 x * G x y) +
          lam * (E theta1 x * G x y)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hE x]
      ring
    _ = (1 - lam) * (∑ x, E theta0 x * G x y) +
        lam * (∑ x, E theta1 x * G x y) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
/-- For a fixed decoder, every world's error is bounded by the worse named-row
error whenever source and target use the same bounded affine coordinate. -/
theorem decodeErr_commonAffine_le_max
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (G : X -> Y -> Real) (theta0 theta1 theta : Theta)
    (h : CommonAffine E F theta0 theta1) :
    decodeErr E F G theta <=
      max (decodeErr E F G theta0) (decodeErr E F G theta1) := by
  let lam := h.lam theta
  have hsource :
      finiteDecisionLaw E G theta =
        fun y => (1 - lam) * finiteDecisionLaw E G theta0 y +
          lam * finiteDecisionLaw E G theta1 y :=
    finiteDecisionLaw_affine E G theta theta0 theta1 lam
      (h.source_affine theta)
  have htarget :
      F theta =
        fun y => (1 - lam) * F theta0 y + lam * F theta1 y := by
    funext y
    exact h.target_affine theta y
  change finiteTV (finiteDecisionLaw E G theta) (F theta) <=
    max (finiteTV (finiteDecisionLaw E G theta0) (F theta0))
      (finiteTV (finiteDecisionLaw E G theta1) (F theta1))
  rw [hsource, htarget]
  exact finiteTV_affine_le_max _ _ _ _ lam
    (h.lam_nonneg theta) (h.lam_le_one theta)


/-- For a fixed decoder, every interpolated world's error is bounded by the
worse anchor error. -/
theorem decodeErr_commonBinaryAffine_le_max
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (G : X -> Y -> Real) (theta0 theta1 theta : Theta)
    (h : CommonBinaryAffine E F theta0 theta1) :
    decodeErr E F G theta <=
      max (decodeErr E F G theta0) (decodeErr E F G theta1) := by
  let lam := h.lam theta
  have hsource :
      finiteDecisionLaw E G theta =
        fun y => (1 - lam) * finiteDecisionLaw E G theta0 y +
          lam * finiteDecisionLaw E G theta1 y :=
    finiteDecisionLaw_affine E G theta theta0 theta1 lam
      (h.source_affine theta)
  have htarget :
      F theta =
        fun y => (1 - lam) * F theta0 y + lam * F theta1 y := by
    funext y
    exact h.target_affine theta y
  change finiteTV (finiteDecisionLaw E G theta) (F theta) <=
    max (finiteTV (finiteDecisionLaw E G theta0) (F theta0))
      (finiteTV (finiteDecisionLaw E G theta1) (F theta1))
  rw [hsource, htarget]
  exact finiteTV_affine_le_max _ _ _ _ lam
    (h.lam_nonneg theta) (h.lam_le_one theta)
/-- A number bounds one decoder on the whole class iff it bounds that decoder
on the two named rows; endpoint normalization is unnecessary. -/
theorem decodeErr_le_iff_binaryAnchors_commonAffine
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (G : X -> Y -> Real) (theta0 theta1 : Theta)
    (h : CommonAffine E F theta0 theta1) (c : Real) :
    (forall theta, decodeErr E F G theta <= c) <->
      (forall b : Bool,
        decodeErr (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestriction F theta0 theta1) G b <= c) := by
  constructor
  · intro hall b
    cases b with
    | false =>
        change decodeErr E F G theta0 <= c
        exact hall theta0
    | true =>
        change decodeErr E F G theta1 <= c
        exact hall theta1
  · intro hanchors theta
    have h0 : decodeErr E F G theta0 <= c := by
      have hb := hanchors false
      change decodeErr E F G theta0 <= c at hb
      exact hb
    have h1 : decodeErr E F G theta1 <= c := by
      have hb := hanchors true
      change decodeErr E F G theta1 <= c at hb
      exact hb
    exact (decodeErr_commonAffine_le_max E F G theta0 theta1 theta h).trans
      (max_le h0 h1)


/-- Under a common binary-affine signature, a number bounds one fixed
decoder on the whole class iff it bounds that decoder on the two anchors. -/
theorem decodeErr_le_iff_binaryAnchors
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (G : X -> Y -> Real) (theta0 theta1 : Theta)
    (h : CommonBinaryAffine E F theta0 theta1) (c : Real) :
    (forall theta, decodeErr E F G theta <= c) <->
      (forall b : Bool,
        decodeErr (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestriction F theta0 theta1) G b <= c) := by
  constructor
  · intro hall b
    cases b with
    | false =>
        change decodeErr E F G theta0 <= c
        exact hall theta0
    | true =>
        change decodeErr E F G theta1 <= c
        exact hall theta1
  · intro hanchors theta
    have h0 : decodeErr E F G theta0 <= c := by
      have hb := hanchors false
      change decodeErr E F G theta0 <= c at hb
      exact hb
    have h1 : decodeErr E F G theta1 <= c := by
      have hb := hanchors true
      change decodeErr E F G theta1 <= c at hb
      exact hb
    exact (decodeErr_commonBinaryAffine_le_max E F G theta0 theta1 theta h).trans
      (max_le h0 h1)
/-- The full-class and two-named-row deficiency upper-bound sets are equal
under the paper's unnormalized common-coordinate hypothesis. -/
theorem finiteDeficiencyCandidates_commonAffine
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) (h : CommonAffine E F theta0 theta1) :
    finiteDeficiencyCandidates E F =
      finiteDeficiencyCandidates
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestriction F theta0 theta1) := by
  ext c
  constructor
  · rintro ⟨G, hG, herr⟩
    exact ⟨G, hG,
      (decodeErr_le_iff_binaryAnchors_commonAffine E F G theta0 theta1 h c).1 herr⟩
  · rintro ⟨G, hG, herr⟩
    exact ⟨G, hG,
      (decodeErr_le_iff_binaryAnchors_commonAffine E F G theta0 theta1 h c).2 herr⟩

/-- **Unnormalized affine worst-world reduction for directed deficiency.** -/
theorem finiteDeficiency_commonAffine
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) (h : CommonAffine E F theta0 theta1) :
    finiteDeficiency E F =
      finiteDeficiency
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestriction F theta0 theta1) := by
  unfold finiteDeficiency
  rw [finiteDeficiencyCandidates_commonAffine E F theta0 theta1 h]


/-- The full-class and two-anchor deficiency upper-bound sets are literally
the same.  This is the optimizer-level content hidden by taking an infimum. -/
theorem finiteDeficiencyCandidates_commonBinaryAffine
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) (h : CommonBinaryAffine E F theta0 theta1) :
    finiteDeficiencyCandidates E F =
      finiteDeficiencyCandidates
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestriction F theta0 theta1) := by
  ext c
  constructor
  · rintro ⟨G, hG, herr⟩
    exact ⟨G, hG, (decodeErr_le_iff_binaryAnchors E F G theta0 theta1 h c).1 herr⟩
  · rintro ⟨G, hG, herr⟩
    exact ⟨G, hG, (decodeErr_le_iff_binaryAnchors E F G theta0 theta1 h c).2 herr⟩

/-- **Affine worst-world reduction for directed deficiency.**  A common
binary-affine source-target signature has exactly the deficiency of its two
named anchors. -/
theorem finiteDeficiency_commonBinaryAffine
    (E : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) (h : CommonBinaryAffine E F theta0 theta1) :
    finiteDeficiency E F =
      finiteDeficiency
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestriction F theta0 theta1) := by
  unfold finiteDeficiency
  rw [finiteDeficiencyCandidates_commonBinaryAffine E F theta0 theta1 h]

/-! ## Simultaneous target and coherent-family reduction -/
/-- A family of targets shares one bounded affine coordinate with the source
experiment. The two named rows are not required to have coordinates zero and
one. -/
structure CommonAffineFamily
    (E : FiniteExperiment Theta X)
    (F : I -> FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) where
  lam : Theta -> Real
  lam_nonneg : forall theta, 0 <= lam theta
  lam_le_one : forall theta, lam theta <= 1
  source_affine : forall theta x,
    E theta x = (1 - lam theta) * E theta0 x + lam theta * E theta1 x
  target_affine : forall i theta y,
    F i theta y =
      (1 - lam theta) * F i theta0 y + lam theta * F i theta1 y


/-- A family of targets shares a binary-affine signature with one source
experiment when one coefficient works for every target in the family. -/
structure CommonBinaryAffineFamily
    (E : FiniteExperiment Theta X)
    (F : I -> FiniteExperiment Theta Y)
    (theta0 theta1 : Theta) where
  lam : Theta -> Real
  lam_nonneg : forall theta, 0 <= lam theta
  lam_le_one : forall theta, lam theta <= 1
  lam_theta0 : lam theta0 = 0
  lam_theta1 : lam theta1 = 1
  source_affine : forall theta x,
    E theta x = (1 - lam theta) * E theta0 x + lam theta * E theta1 x
  target_affine : forall i theta y,
    F i theta y =
      (1 - lam theta) * F i theta0 y + lam theta * F i theta1 y
/-- Forget endpoint normalization for every target in a family. -/
def CommonBinaryAffineFamily.toCommonAffineFamily
    {E : FiniteExperiment Theta X} {F : I -> FiniteExperiment Theta Y}
    {theta0 theta1 : Theta}
    (h : CommonBinaryAffineFamily E F theta0 theta1) :
    CommonAffineFamily E F theta0 theta1 where
  lam := h.lam
  lam_nonneg := h.lam_nonneg
  lam_le_one := h.lam_le_one
  source_affine := h.source_affine
  target_affine := h.target_affine


/-- Restrict every target in a family to the same two anchors. -/
def binaryAnchorRestrictionFamily
    (F : I -> FiniteExperiment Theta Y) (theta0 theta1 : Theta) :
    I -> FiniteExperiment Bool Y :=
  fun i => binaryAnchorRestriction (F i) theta0 theta1

/-- Candidate worst-error bounds for a family of decoder tables subject to an
arbitrary world-independent admissibility predicate.  For coherent causal
reconstruction, Admissible G says that all tables G i are marginals of one
decoded causal model. -/
def decoderFamilyCandidates
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (Admissible : (I -> X -> Y -> Real) -> Prop) : Set Real :=
  {c | exists G, Admissible G /\
    forall i theta, decodeErr E (F i) (G i) theta <= c}

/-- The infimum worst-world, worst-target error under a chosen family
constraint. -/
noncomputable def decoderFamilyInf
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (Admissible : (I -> X -> Y -> Real) -> Prop) : Real :=
  sInf (decoderFamilyCandidates E F Admissible)

/-- Package one member of a common affine family as a pair signature. -/
def CommonBinaryAffineFamily.at
    {E : FiniteExperiment Theta X} {F : I -> FiniteExperiment Theta Y}
    {theta0 theta1 : Theta}
    (h : CommonBinaryAffineFamily E F theta0 theta1) (i : I) :
    CommonBinaryAffine E (F i) theta0 theta1 where
  lam := h.lam
  lam_nonneg := h.lam_nonneg
  lam_le_one := h.lam_le_one
  lam_theta0 := h.lam_theta0
  lam_theta1 := h.lam_theta1
  source_affine := h.source_affine
  target_affine := h.target_affine i
/-- Package one member of an unnormalized common affine family. -/
def CommonAffineFamily.at
    {E : FiniteExperiment Theta X} {F : I -> FiniteExperiment Theta Y}
    {theta0 theta1 : Theta}
    (h : CommonAffineFamily E F theta0 theta1) (i : I) :
    CommonAffine E (F i) theta0 theta1 where
  lam := h.lam
  lam_nonneg := h.lam_nonneg
  lam_le_one := h.lam_le_one
  source_affine := h.source_affine
  target_affine := h.target_affine i

/-- Restricting an unnormalized common affine family to its two named rows
does not change the admissible-family candidate set. -/
theorem decoderFamilyCandidates_commonAffine
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (Admissible : (I -> X -> Y -> Real) -> Prop)
    (theta0 theta1 : Theta)
    (h : CommonAffineFamily E F theta0 theta1) :
    decoderFamilyCandidates E F Admissible =
      decoderFamilyCandidates
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestrictionFamily F theta0 theta1) Admissible := by
  ext c
  constructor
  · rintro ⟨G, hG, herr⟩
    refine ⟨G, hG, ?_⟩
    intro i b
    change decodeErr (binaryAnchorRestriction E theta0 theta1)
      (binaryAnchorRestriction (F i) theta0 theta1) (G i) b <= c
    exact (decodeErr_le_iff_binaryAnchors_commonAffine E (F i) (G i)
      theta0 theta1 (h.at i) c).1 (herr i) b
  · rintro ⟨G, hG, herr⟩
    refine ⟨G, hG, ?_⟩
    intro i theta
    have hi : forall b : Bool,
        decodeErr (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestriction (F i) theta0 theta1) (G i) b <= c := by
      intro b
      have hib := herr i b
      change decodeErr (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestriction (F i) theta0 theta1) (G i) b <= c at hib
      exact hib
    exact (decodeErr_le_iff_binaryAnchors_commonAffine E (F i) (G i)
      theta0 theta1 (h.at i) c).2 hi theta

/-- Every world-independent decoder-family optimization reduces to the two
named rows under the paper's unnormalized common-coordinate hypothesis. -/
theorem decoderFamilyInf_commonAffine
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (Admissible : (I -> X -> Y -> Real) -> Prop)
    (theta0 theta1 : Theta)
    (h : CommonAffineFamily E F theta0 theta1) :
    decoderFamilyInf E F Admissible =
      decoderFamilyInf
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestrictionFamily F theta0 theta1) Admissible := by
  unfold decoderFamilyInf
  rw [decoderFamilyCandidates_commonAffine E F Admissible theta0 theta1 h]

/-- Effective-binary transfer without endpoint normalization. -/
theorem effectiveBinary_familyInf_transfer_commonAffine
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (A B : (I -> X -> Y -> Real) -> Prop)
    (theta0 theta1 : Theta)
    (h : CommonAffineFamily E F theta0 theta1)
    (hanchors :
      decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) A =
        decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) B) :
    decoderFamilyInf E F A = decoderFamilyInf E F B := by
  calc
    decoderFamilyInf E F A =
        decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) A :=
      decoderFamilyInf_commonAffine E F A theta0 theta1 h
    _ = decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) B := hanchors
    _ = decoderFamilyInf E F B :=
      (decoderFamilyInf_commonAffine E F B theta0 theta1 h).symm


/-- The admissible-family candidate set is unchanged by restricting a common
binary-affine signature to its anchors. -/
theorem decoderFamilyCandidates_commonBinaryAffine
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (Admissible : (I -> X -> Y -> Real) -> Prop)
    (theta0 theta1 : Theta)
    (h : CommonBinaryAffineFamily E F theta0 theta1) :
    decoderFamilyCandidates E F Admissible =
      decoderFamilyCandidates
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestrictionFamily F theta0 theta1) Admissible := by
  ext c
  constructor
  · rintro ⟨G, hG, herr⟩
    refine ⟨G, hG, ?_⟩
    intro i b
    change decodeErr (binaryAnchorRestriction E theta0 theta1)
      (binaryAnchorRestriction (F i) theta0 theta1) (G i) b <= c
    exact (decodeErr_le_iff_binaryAnchors E (F i) (G i) theta0 theta1
      (h.at i) c).1 (herr i) b
  · rintro ⟨G, hG, herr⟩
    refine ⟨G, hG, ?_⟩
    intro i theta
    have hi : forall b : Bool,
        decodeErr (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestriction (F i) theta0 theta1) (G i) b <= c := by
      intro b
      have hib := herr i b
      change decodeErr (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestriction (F i) theta0 theta1) (G i) b <= c at hib
      exact hib
    exact (decodeErr_le_iff_binaryAnchors E (F i) (G i) theta0 theta1
      (h.at i) c).2 hi theta

/-- Every world-independent decoder-family optimization reduces exactly to
the two anchors under a common binary-affine signature. -/
theorem decoderFamilyInf_commonBinaryAffine
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (Admissible : (I -> X -> Y -> Real) -> Prop)
    (theta0 theta1 : Theta)
    (h : CommonBinaryAffineFamily E F theta0 theta1) :
    decoderFamilyInf E F Admissible =
      decoderFamilyInf
        (binaryAnchorRestriction E theta0 theta1)
        (binaryAnchorRestrictionFamily F theta0 theta1) Admissible := by
  unfold decoderFamilyInf
  rw [decoderFamilyCandidates_commonBinaryAffine E F Admissible theta0 theta1 h]

/-- **Effective-binary transfer theorem.**  If two world-independent decoder
constraints have the same optimum on the two anchors, then they have the same
optimum on the entire common binary-affine class.  Taking the constraints to
be separate test tables and coherent causal-model marginals yields the outer
reduction in the paper's effective-binary coherence theorem. -/
theorem effectiveBinary_familyInf_transfer
    (E : FiniteExperiment Theta X) (F : I -> FiniteExperiment Theta Y)
    (A B : (I -> X -> Y -> Real) -> Prop)
    (theta0 theta1 : Theta)
    (h : CommonBinaryAffineFamily E F theta0 theta1)
    (hanchors :
      decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) A =
        decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) B) :
    decoderFamilyInf E F A = decoderFamilyInf E F B := by
  calc
    decoderFamilyInf E F A =
        decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) A :=
      decoderFamilyInf_commonBinaryAffine E F A theta0 theta1 h
    _ = decoderFamilyInf
          (binaryAnchorRestriction E theta0 theta1)
          (binaryAnchorRestrictionFamily F theta0 theta1) B := hanchors
    _ = decoderFamilyInf E F B :=
      (decoderFamilyInf_commonBinaryAffine E F B theta0 theta1 h).symm

end IdExp
