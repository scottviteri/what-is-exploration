/-
# Retained finite-POMDP identification and objective theorems

These results use `Hist` from `Basic.lean`, including an initial observation at time zero.
They belong to the attained-full-revelation specialization in the full reader,
not the general definition of exploration or the selected Hellinger reward.
Current support is recorded in `Formal/PAPER_SUPPORT.json`; the causal objective
wrappers are under `thm:finite-objectives`. `Formal/STATEMENTS.md` preserves the
older finite-POMDP draft's theorem numbering and proof-development history.
-/
import Formal.Basic
import Formal.Nonneg
import Formal.Hellinger
import Formal.PathLaw
import Formal.PathLawExists
import Formal.Identification

namespace IdExp

open MeasureTheory

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Fintype Θ]
variable [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Θ]
variable [DecidableEq A] [DecidableEq O]

/-! ## Infrastructure: the path law exists and is unique

These justify parameterizing the finite-POMDP layer by `IsPathLaw`:
Ionescu–Tulcea / `Kernel.traj` supplies existence, and a π-λ argument supplies
uniqueness. The initial observation remains part of the path. -/

omit [DecidableEq A] [DecidableEq O] in
theorem pathLaw_exists [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (π : Policy A O) (hπ : IsPolicy π) (M : POMDP A O) (hM : M.Valid) :
    ∃ μ : Measure (Traj A O), IsPathLaw π M μ := by
  -- Validity forces both types to be inhabited: each sums a distribution to one.
  have hO : Nonempty O := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have h1 := sum_traceLik_nil M hM
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have o : O := Classical.choice hO
  have hA : Nonempty A := by
    by_contra hna
    rw [not_nonempty_iff] at hna
    have h1 := (hπ (o, [])).2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  exact ⟨pathLawMeasure π hπ M hM, isPathLaw_pathLawMeasure π hπ M hM⟩

omit [DecidableEq A] [DecidableEq O] in
theorem pathLaw_unique [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (π : Policy A O) (M : POMDP A O) {μ ν : Measure (Traj A O)}
    (hμ : IsPathLaw π M μ) (hν : IsPathLaw π M ν) : μ = ν := by
  have := hμ.isProb
  have := hν.isProb
  refine ext_of_generate_finite _ generateFrom_range_cyl isPiSystem_range_cyl ?_ ?_
  · rintro _ ⟨h, rfl⟩
    rw [hμ.cylinder, hν.cylinder]
  · rw [measure_univ, measure_univ]

/-! ## Finite-POMDP path-law identification (`pathLaw_identification`)

Stated for a PRE-QUOTIENTED family: the hypothesis `hsep` says the chosen
representatives are pairwise behaviorally inequivalent, using the retained
"choose one POMDP representative per class" convention.  See STATEMENTS.md
(choice C1) for the alternative quotient reading. -/

omit [DecidableEq A] [DecidableEq O] in
theorem pathLaw_identification [MeasurableSingletonClass A]
    [MeasurableSingletonClass O] [MeasurableSingletonClass Θ] [Nonempty Θ]
    (Ms : Θ → POMDP A O) (hV : ∀ θ, (Ms θ).Valid)
    (hsep : Pairwise fun θ θ' => ¬ BehEq (Ms θ) (Ms θ'))
    (π : Policy A O) (hπ : IsPolicy π)
    (μfam : Θ → Measure (Traj A O)) (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) :
    List.TFAE
      [ Pairwise fun θ θ' => μfam θ ⟂ₘ μfam θ',
        ∃ α : Θ → ℝ, IsDist α ∧ FullSupport α ∧ ConcentratesOnTruth α Ms μfam,
        ∀ α : Θ → ℝ, IsDist α → FullSupport α → ConcentratesOnTruth α Ms μfam ] := by
  tfae_have 1 → 3 := fun h1 α hα _ =>
    concentrates_of_pairwise_singular α Ms π μfam hα hV hπ hμ h1
  tfae_have 3 → 2 := by
    intro h3
    obtain ⟨α, hα, hfs⟩ := exists_fullSupport_isDist Θ
    exact ⟨α, hα, hfs, h3 α hα hfs⟩
  tfae_have 2 → 1 := by
    rintro ⟨α, hα, hfs, hconc⟩
    exact pairwise_singular_of_concentrates α Ms μfam hα hfs hV
      (fun c => (hμ c).isProb) hconc
  tfae_finish

/-! ## Terminal mutual information in the attained-revelation specialization

The retained claim `arg max_π I^π_∞ = Π_id, max = H_α(C⋆)` is unfolded into the upper
bound plus the two argmax inclusions (choice C6 in STATEMENTS.md). -/

omit [MeasurableSpace A] [MeasurableSpace O] [MeasurableSpace Θ] in
/-- Upper bound `I^π_∞ ≤ H(C⋆)`. -/
theorem infoInf_le_ent
    (Ms : Θ → POMDP A O) (hV : ∀ θ, (Ms θ).Valid)
    (α : Θ → ℝ) (hα : IsDist α)
    (π : Policy A O) (hπ : IsPolicy π) :
    infoInf α Ms π ≤ ent α := by
  -- Each finite-horizon term is `ent α` minus a nonnegative expectation, and a
  -- real-valued `⨆` bounded termwise is bounded (`ciSup_le`; no `BddAbove`
  -- side condition is needed, cf. STATEMENTS.md C7).
  unfold infoInf
  refine ciSup_le fun T => ?_
  unfold infoAt
  refine sub_le_self _ (Finset.sum_nonneg fun h _ => mul_nonneg ?_ ?_)
  · exact Finset.sum_nonneg fun θ _ =>
      mul_nonneg (hα.1 θ) (traceProb_nonneg π hπ (Ms θ) (hV θ) h)
  · exact ent_posterior_nonneg α hα Ms hV h

/-- Exact completeness: under uniform identifiability and a full-support prior,
a policy attains `I_∞ = H(α)` iff it identifies. -/
theorem mi_exactly_complete [MeasurableSingletonClass A]
    [MeasurableSingletonClass O] [MeasurableSingletonClass Θ]
    (Ms : Θ → POMDP A O) (hV : ∀ θ, (Ms θ).Valid)
    (hsep : Pairwise fun θ θ' => ¬ BehEq (Ms θ) (Ms θ'))
    (hid : UniformlyIdentifiable Ms)
    (α : Θ → ℝ) (hα : IsDist α) (hfull : FullSupport α)
    (π : Policy A O) (hπ : IsPolicy π) :
    Identifies Ms π ↔ infoInf α Ms π = ent α := by
  -- The prior forces `Θ` inhabited, and validity then forces `O` inhabited.
  have hΘ : Nonempty Θ := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have h1 := hα.2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  obtain ⟨θ₀⟩ := hΘ
  have hO : Nonempty O := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have h1 := sum_traceLik_nil (Ms θ₀) (hV θ₀)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  -- A canonical path-law family; by uniqueness it is the only one.
  choose μfam hμ using fun θ => pathLaw_exists π hπ (Ms θ) (hV θ)
  constructor
  · intro hid'
    exact infoInf_eq_ent_of_concentrates α Ms π μfam hα hV hπ hμ
      (concentrates_of_pairwise_singular α Ms π μfam hα hV hπ hμ (hid' μfam hμ))
  · intro hsup
    have hconc := concentrates_of_infoInf_eq_ent α Ms π μfam hα hV hπ hμ hsup
    have hsing := pairwise_singular_of_concentrates α Ms μfam hα hfull hV
      (fun c => (hμ c).isProb) hconc
    intro μfam' hμ'
    have heq : μfam' = μfam := funext fun θ => pathLaw_unique π (Ms θ) (hμ' θ) (hμ θ)
    rw [heq]
    exact hsing

/-! ## Worst-pair terminal Hellinger in the attained-revelation specialization -/

omit [MeasurableSpace Θ] [DecidableEq A] [DecidableEq O] in
/-- Exact completeness of the worst-pair Hellinger criterion: under uniform
identifiability, the induced path-law family of a policy attains the maximal
separation `J_Hel = 1` iff the policy identifies.  (For `|Θ| = 1` the infimum
is `⊤`, so the displayed finite maximum requires `hcard`.
Choice C8 in STATEMENTS.md.) -/
theorem hellinger_exactly_complete
    [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (Ms : Θ → POMDP A O) (hV : ∀ θ, (Ms θ).Valid)
    (hsep : Pairwise fun θ θ' => ¬ BehEq (Ms θ) (Ms θ'))
    (hid : UniformlyIdentifiable Ms) (hcard : 1 < Fintype.card Θ)
    (π : Policy A O) (hπ : IsPolicy π)
    (μfam : Θ → Measure (Traj A O)) (hμ : ∀ θ, IsPathLaw π (Ms θ) (μfam θ)) :
    worstPairHellinger μfam = 1 ↔ Identifies Ms π := by
  have hprob : ∀ θ, IsProbabilityMeasure (μfam θ) := fun θ => (hμ θ).isProb
  -- By uniqueness of path laws, `Identifies` is a statement about THIS family.
  have hiff : Identifies Ms π ↔ Pairwise fun θ θ' => μfam θ ⟂ₘ μfam θ' := by
    constructor
    · intro h
      exact h μfam hμ
    · intro h μfam' hμ' θ θ' hne
      have e : μfam' = μfam := funext fun θ => pathLaw_unique π (Ms θ) (hμ' θ) (hμ θ)
      rw [e]
      exact h hne
  rw [hiff]
  unfold worstPairHellinger
  constructor
  · intro h θ θ' hne
    have hle : 1 ≤ hellingerSq (μfam θ) (μfam θ') := by
      rw [← h]
      exact iInf_le_of_le θ (iInf_le_of_le θ' (iInf_le _ hne))
    have hone : hellingerSq (μfam θ) (μfam θ') = 1 :=
      le_antisymm (by unfold hellingerSq; exact tsub_le_self) hle
    have := hprob θ
    have := hprob θ'
    exact (hellingerSq_eq_one_iff _ _).1 hone
  · intro h
    apply le_antisymm
    · obtain ⟨θ, θ', hne⟩ := Fintype.exists_pair_of_one_lt_card hcard
      have := hprob θ
      have := hprob θ'
      exact iInf_le_of_le θ (iInf_le_of_le θ' (iInf_le_of_le hne
        (((hellingerSq_eq_one_iff _ _).2 (h hne)).le)))
    · refine le_iInf fun θ => le_iInf fun θ' => le_iInf fun hne => ?_
      have := hprob θ
      have := hprob θ'
      exact ((hellingerSq_eq_one_iff _ _).2 (h hne)).symm.le

end IdExp
