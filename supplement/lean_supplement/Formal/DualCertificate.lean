import Formal.FiniteTV
import Formal.MixtureDecoder

/-!
# Rational finite-deficiency dual certificates

**Relevance:** direct current-paper support, finite-experiment scope.

The paper's rational dual-certificate lemma lower-bounds deficiency by a number
computed from nonnegative weights `mu`, dominated by a prior `lambda`.  This
file proves its decoder-level statement: every stochastic decoder whose
classwise total-variation errors are at most `c` has certificate value at most
`c`.  Taking the infimum over decoders gives the displayed paper lemma.

The auxiliary vector `b x` is allowed to be any common lower bound on
`sum theta, mu theta y * E theta x` over target signals `y`.  For the paper's
formula, take `b x` to be the finite minimum over `y`.  This formulation is
also exactly what an explicit rational certificate needs to check.
-/

namespace IdExp

open Finset Set

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]

/-- On probability rows, half-l1 decoder error is the sum of the positive
residuals. -/
theorem decodeErr_eq_sum_posPart (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (hE : IsFiniteExperiment E)
    (hF : IsFiniteExperiment F) (G : X → Y → ℝ)
    (hG : G ∈ stochasticRules X Y) (θ : Θ) :
    decodeErr E F G θ =
      ∑ y, max (finiteDecisionLaw E G θ y - F θ y) 0 := by
  change finiteTV (finiteDecisionLaw E G θ) (F θ) = _
  rw [← sum_posPart_eq_finiteTV]
  rw [(finiteDecisionLaw_valid E hE G hG θ).2, (hF θ).2]

/-- **Rational dual certificate, decoder form.**  If every row error of `G` is
at most `c`, every admissible rational certificate has value at most `c`.
Specializing `b x` to the finite minimum over `y` is exactly Lemma
`lem:dual-certificate` in the canonical paper. -/
theorem finiteDualCertificate_le (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (hE : IsFiniteExperiment E)
    (hF : IsFiniteExperiment F) (G : X → Y → ℝ)
    (hG : G ∈ stochasticRules X Y)
    (lambda : Θ → ℝ) (hlambda : IsDist lambda)
    (mu : Θ → Y → ℝ)
    (hmu0 : ∀ θ y, 0 ≤ mu θ y)
    (hmule : ∀ θ y, mu θ y ≤ lambda θ)
    (b : X → ℝ)
    (hb : ∀ x y, b x ≤ ∑ θ, mu θ y * E θ x)
    (c : ℝ) (herr : ∀ θ, decodeErr E F G θ ≤ c) :
    (∑ x, b x) - ∑ θ, ∑ y, mu θ y * F θ y ≤ c := by
  have hweighted : ∑ θ, lambda θ * decodeErr E F G θ ≤ c := by
    calc
      ∑ θ, lambda θ * decodeErr E F G θ ≤ ∑ θ, lambda θ * c :=
        Finset.sum_le_sum fun θ _ =>
          mul_le_mul_of_nonneg_left (herr θ) (hlambda.1 θ)
      _ = c := by rw [← Finset.sum_mul, hlambda.2, one_mul]

  have hterm : ∀ θ y,
      mu θ y * (finiteDecisionLaw E G θ y - F θ y) ≤
        lambda θ * max (finiteDecisionLaw E G θ y - F θ y) 0 := by
    intro θ y
    by_cases hr : 0 ≤ finiteDecisionLaw E G θ y - F θ y
    · rw [max_eq_left hr]
      exact mul_le_mul_of_nonneg_right (hmule θ y) hr
    · have hr' : finiteDecisionLaw E G θ y - F θ y ≤ 0 := le_of_not_ge hr
      rw [max_eq_right hr', mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (hmu0 θ y) hr'

  have hmu :
      ∑ θ, ∑ y, mu θ y * (finiteDecisionLaw E G θ y - F θ y) ≤
        ∑ θ, lambda θ * decodeErr E F G θ := by
    calc
      ∑ θ, ∑ y, mu θ y * (finiteDecisionLaw E G θ y - F θ y) ≤
          ∑ θ, ∑ y, lambda θ *
            max (finiteDecisionLaw E G θ y - F θ y) 0 :=
        Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun y _ => hterm θ y
      _ = ∑ θ, lambda θ * decodeErr E F G θ := by
        apply Finset.sum_congr rfl
        intro θ _
        rw [decodeErr_eq_sum_posPart E F hE hF G hG θ, Finset.mul_sum]

  have hbpoint : ∀ x,
      b x ≤ ∑ y, G x y * ∑ θ, mu θ y * E θ x := by
    intro x
    calc
      b x = ∑ y, G x y * b x := by
        rw [← Finset.sum_mul, (hG x (Set.mem_univ x)).2, one_mul]
      _ ≤ ∑ y, G x y * ∑ θ, mu θ y * E θ x :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hb x y) ((hG x (Set.mem_univ x)).1 y)

  have hsignal :
      ∑ x, b x ≤ ∑ θ, ∑ y, mu θ y * finiteDecisionLaw E G θ y := by
    calc
      ∑ x, b x ≤ ∑ x, ∑ y, G x y * ∑ θ, mu θ y * E θ x :=
        Finset.sum_le_sum fun x _ => hbpoint x
      _ = ∑ x, ∑ y, ∑ θ, G x y * (mu θ y * E θ x) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
      _ = ∑ x, ∑ θ, ∑ y, G x y * (mu θ y * E θ x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = ∑ θ, ∑ x, ∑ y, G x y * (mu θ y * E θ x) := Finset.sum_comm
      _ = ∑ θ, ∑ y, ∑ x, G x y * (mu θ y * E θ x) := by
        apply Finset.sum_congr rfl
        intro θ _
        rw [Finset.sum_comm]
      _ = ∑ θ, ∑ y, mu θ y * finiteDecisionLaw E G θ y := by
        apply Finset.sum_congr rfl
        intro θ _
        apply Finset.sum_congr rfl
        intro y _
        unfold finiteDecisionLaw
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring

  calc
    (∑ x, b x) - ∑ θ, ∑ y, mu θ y * F θ y ≤
        (∑ θ, ∑ y, mu θ y * finiteDecisionLaw E G θ y) -
          ∑ θ, ∑ y, mu θ y * F θ y := sub_le_sub_right hsignal _
    _ = ∑ θ, ∑ y,
        mu θ y * (finiteDecisionLaw E G θ y - F θ y) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro θ _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ ∑ θ, lambda θ * decodeErr E F G θ := hmu
    _ ≤ c := hweighted


/-- The paper's displayed certificate value, with the finite minimum over the
 target signal made literal. -/
noncomputable def finiteDualCertificateValue [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (mu : Θ → Y → ℝ) : ℝ :=
  (∑ x, Finset.univ.inf' Finset.univ_nonempty
      (fun y => ∑ θ, mu θ y * E θ x)) -
    ∑ θ, ∑ y, mu θ y * F θ y

/-- Exact finite-minimum specialization of `finiteDualCertificate_le`. -/
theorem finiteDualCertificateValue_le [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (lambda : Θ → ℝ) (hlambda : IsDist lambda)
    (mu : Θ → Y → ℝ) (hmu0 : ∀ θ y, 0 ≤ mu θ y)
    (hmule : ∀ θ y, mu θ y ≤ lambda θ)
    (c : ℝ) (herr : ∀ θ, decodeErr E F G θ ≤ c) :
    finiteDualCertificateValue E F mu ≤ c := by
  apply finiteDualCertificate_le E F hE hF G hG lambda hlambda mu hmu0 hmule
  intro x y
  exact Finset.inf'_le _ (Finset.mem_univ y)
  exact herr

/-- Upper-bound presentation of the finite deficiency infimum.  A number is a
candidate when one stochastic decoder has every classwise error at most it. -/
def finiteDeficiencyCandidates (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) : Set ℝ :=
  {c | ∃ G ∈ stochasticRules X Y, ∀ θ, decodeErr E F G θ ≤ c}

/-- Finite directed deficiency, expressed as the infimum of decoder upper
bounds.  This is equivalent to the paper's `inf_G max_theta` definition. -/
noncomputable def finiteDeficiency (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) : ℝ :=
  sInf (finiteDeficiencyCandidates E F)

theorem finiteDeficiencyCandidates_nonempty [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    (finiteDeficiencyCandidates E F).Nonempty := by
  classical
  let y0 : Y := Classical.choice inferInstance
  let G : X → Y → ℝ := fun _ y => if y = y0 then 1 else 0
  have hG : G ∈ stochasticRules X Y := by
    intro x _
    constructor
    · intro y
      by_cases h : y = y0 <;> simp [G, h]
    · simp [G, y0]
  refine ⟨∑ θ, decodeErr E F G θ, G, hG, ?_⟩
  intro θ
  exact Finset.single_le_sum (fun θ _ => decodeErr_nonneg E F G θ)
    (Finset.mem_univ θ)

omit [Fintype Θ] in
/-- Candidate upper bounds are bounded below by zero as soon as the world
class is nonempty. No finiteness assumption on the world class is needed. -/
theorem finiteDeficiencyCandidates_bddBelow [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) :
    BddBelow (finiteDeficiencyCandidates E F) := by
  refine ⟨0, ?_⟩
  rintro c ⟨G, _, herr⟩
  let θ0 : Θ := Classical.choice inferInstance
  exact (decodeErr_nonneg E F G θ0).trans (herr θ0)

omit [Fintype Θ] in
/-- For valid experiments, the deficiency candidate set is nonempty even
when the world class is infinite: any stochastic decoder has error at most
one. -/
theorem finiteDeficiencyCandidates_nonempty_of_valid [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    (finiteDeficiencyCandidates E F).Nonempty := by
  classical
  let y0 : Y := Classical.choice inferInstance
  let G : X → Y → ℝ := fun _ y => if y = y0 then 1 else 0
  have hG : G ∈ stochasticRules X Y := by
    intro x _
    constructor
    · intro y
      by_cases h : y = y0 <;> simp [G, h]
    · simp [G, y0]
  exact ⟨1, G, hG, fun θ => decodeErr_le_one E F hE hF G hG θ⟩

omit [Fintype Θ] in
/-- A displayed decoder bound is an upper bound on directed deficiency. -/
theorem finiteDeficiency_le_of_decoder [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (c : ℝ)
    (herr : ∀ θ, decodeErr E F G θ ≤ c) :
    finiteDeficiency E F ≤ c := by
  apply csInf_le (finiteDeficiencyCandidates_bddBelow E F)
  exact ⟨G, hG, herr⟩

omit [Fintype Θ] in
/-- The infimum defining finite deficiency can be approached within every
positive eta by one decoder, uniformly over an arbitrary nonempty world
class. This is the formal eta step used in finite-horizon universality. -/
theorem exists_decoder_le_finiteDeficiency_add
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    {η : ℝ} (hη : 0 < η) :
    ∃ G ∈ stochasticRules X Y,
      ∀ θ, decodeErr E F G θ ≤ finiteDeficiency E F + η := by
  have hnonempty := finiteDeficiencyCandidates_nonempty_of_valid E F hE hF
  have hlt : finiteDeficiency E F < finiteDeficiency E F + η :=
    lt_add_of_pos_right _ hη
  have hinf_lt :
      sInf (finiteDeficiencyCandidates E F) < finiteDeficiency E F + η := by
    change finiteDeficiency E F < finiteDeficiency E F + η
    exact hlt
  obtain ⟨c, hc, hclt⟩ := exists_lt_of_csInf_lt hnonempty hinf_lt
  obtain ⟨G, hG, herr⟩ := hc
  exact ⟨G, hG, fun θ => (herr θ).trans hclt.le⟩

omit [Fintype Θ] in
/-- Garbling the target experiment cannot increase directed deficiency.
The proof approaches the first deficiency within eta, composes the decoder,
and then lets eta decrease to zero. -/
theorem finiteDeficiency_decisionLaw_le
    {Z : Type*} [Fintype Z] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (H : Y → Z → ℝ) (hH : H ∈ stochasticRules Y Z) :
    finiteDeficiency E (finiteDecisionLaw F H) ≤ finiteDeficiency E F := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨G, hG, herr⟩ :=
    exists_decoder_le_finiteDeficiency_add E F hE hF hη
  apply finiteDeficiency_le_of_decoder E (finiteDecisionLaw F H)
    (stochasticRuleComp G H)
    (stochasticRuleComp_mem_stochasticRules hG hH)
    (finiteDeficiency E F + η)
  intro θ
  exact (decodeErr_stochasticRuleComp_le E F G H hH θ).trans (herr θ)

omit [Fintype Θ] in
/-- Deficiency is monotone in its target under finite Blackwell order:
simulating a more informative target is at least as hard. -/
theorem finiteDeficiency_mono_target_of_finiteBlackwellLE
    {Z : Type*} [Fintype Z] [Nonempty Θ] [Nonempty Z]
    (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (D : FiniteExperiment Θ Z)
    (hE : IsFiniteExperiment E) (hD : IsFiniteExperiment D)
    (hFD : FiniteBlackwellLE F D) :
    finiteDeficiency E F ≤ finiteDeficiency E D := by
  obtain ⟨H, hH, hEq⟩ := hFD
  rw [← hEq]
  exact finiteDeficiency_decisionLaw_le E D hE hD H hH

omit [Fintype Θ] in
/-- Blackwell-equivalent encodings of a valid target have exactly the same
directed deficiency from a valid source. -/
theorem finiteDeficiency_eq_of_target_blackwellEquiv
    {Z : Type*} [Fintype Z] [Nonempty Θ] [Nonempty Y] [Nonempty Z]
    (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (D : FiniteExperiment Θ Z)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hD : IsFiniteExperiment D)
    (hFD : FiniteBlackwellLE F D) (hDF : FiniteBlackwellLE D F) :
    finiteDeficiency E F = finiteDeficiency E D := by
  exact le_antisymm
    (finiteDeficiency_mono_target_of_finiteBlackwellLE E F D hE hD hFD)
    (finiteDeficiency_mono_target_of_finiteBlackwellLE E D F hE hF hDF)

/-- **The paper's rational dual-certificate lemma.**  Every admissible
certificate value is a lower bound on finite directed deficiency. -/
theorem finiteDualCertificateValue_le_finiteDeficiency
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (lambda : Θ → ℝ) (hlambda : IsDist lambda)
    (mu : Θ → Y → ℝ) (hmu0 : ∀ θ y, 0 ≤ mu θ y)
    (hmule : ∀ θ y, mu θ y ≤ lambda θ) :
    finiteDualCertificateValue E F mu ≤ finiteDeficiency E F := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty E F)
  intro c hc
  obtain ⟨G, hG, herr⟩ := hc
  exact finiteDualCertificateValue_le E F hE hF G hG lambda hlambda mu hmu0 hmule c herr

/-- An explicit stochastic decoder and an equally valued rational dual
certificate determine the actual infimum, not merely a chosen decoder's error.
This reusable equality principle is instantiated by the seven exact witnesses
in `RandomizedProfileValues.lean`. -/
theorem finiteDeficiency_eq_of_matching_certificate
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (lambda : Θ → ℝ) (hlambda : IsDist lambda)
    (mu : Θ → Y → ℝ)
    (hmu0 : ∀ θ y, 0 ≤ mu θ y)
    (hmule : ∀ θ y, mu θ y ≤ lambda θ)
    (b : X → ℝ)
    (hb : ∀ x y, b x ≤ ∑ θ, mu θ y * E θ x)
    (c : ℝ)
    (hvalue : (∑ x, b x) - ∑ θ, ∑ y, mu θ y * F θ y = c)
    (herr : ∀ θ, decodeErr E F G θ ≤ c) :
    finiteDeficiency E F = c := by
  apply le_antisymm (finiteDeficiency_le_of_decoder E F G hG c herr)
  apply le_csInf (finiteDeficiencyCandidates_nonempty E F)
  rintro d ⟨H, hH, herror⟩
  rw [← hvalue]
  exact finiteDualCertificate_le E F hE hF H hH lambda hlambda mu
    hmu0 hmule b hb d herror

/-- More information in the source cannot increase directed deficiency. -/
theorem finiteDeficiency_mono_source_of_finiteBlackwellLE
    {Θ X Y Z : Type*} [Fintype Θ] [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty Θ] [Nonempty Z]
    (E : FiniteExperiment Θ X) (D : FiniteExperiment Θ Y) (F : FiniteExperiment Θ Z)
    (hDE : FiniteBlackwellLE D E) : finiteDeficiency E F ≤ finiteDeficiency D F := by
  obtain ⟨G, hG, heq⟩ := hDE
  apply le_csInf (finiteDeficiencyCandidates_nonempty D F)
  rintro c ⟨H, hH, herr⟩
  apply finiteDeficiency_le_of_decoder E F (stochasticRuleComp G H)
    (stochasticRuleComp_mem_stochasticRules hG hH) c
  intro θ
  change finiteTV (finiteDecisionLaw E (stochasticRuleComp G H) θ) (F θ) ≤ c
  rw [finiteDecisionLaw_stochasticRuleComp, heq]
  exact herr θ

/-- Replacing a finite source experiment by a Blackwell-equivalent encoding
does not change any directed deficiency. -/
theorem finiteDeficiency_eq_of_source_blackwellEquiv
    {Θ X Y Z : Type*} [Fintype Θ] [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty Θ] [Nonempty Z]
    (E : FiniteExperiment Θ X) (D : FiniteExperiment Θ Y) (F : FiniteExperiment Θ Z)
    (hED : FiniteBlackwellLE E D) (hDE : FiniteBlackwellLE D E) :
    finiteDeficiency E F = finiteDeficiency D F := by
  exact le_antisymm (finiteDeficiency_mono_source_of_finiteBlackwellLE E D F hDE)
    (finiteDeficiency_mono_source_of_finiteBlackwellLE D E F hED)

end IdExp
