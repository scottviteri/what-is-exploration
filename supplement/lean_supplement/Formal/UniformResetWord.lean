import Formal.CausalBlockSplice
import Formal.CausalPartialExecution

/-!
# Uniform reset words: exact finite block extraction on one run

The reset assumption concerns controlled-trace behavior at reachable reset
endpoints, and is invariant under the behavioral quotient. A concrete policy
runs arbitrary prefix acquisition, executes the action word, and then runs
the requested policy using only its local history. Projection of the actual
single-run transcript exactly recovers the requested finite experiment.

This is the finite block-extraction core of reset-word splicing. An infinite
all-tests cycling schedule, iid-replicate localization, and approximate
resets are not claimed here.
-/

namespace IdExp

open Finset Set
open scoped Classical

set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O]

/-- A reset word restores the original behavior after every reachable
controlled prefix ending in that action word. No raw null-history response
coordinates are constrained. -/
def IsUniformCausalResetWord {ℓ : ℕ} (Q : CausalResponse A O) (r : Fin ℓ → A) : Prop :=
  ∀ (pre : CausalHistory A O) (ys : Fin ℓ → O),
    causalResponseProb Q (pre ++ List.ofFn (fun i => (r i, ys i))) ≠ 0 →
      CausalBehEq (causalResponseAfter Q (pre ++ List.ofFn (fun i => (r i, ys i)))) Q

/-- The reset property is a property of behavioral worlds, not raw kernel
coordinates after impossible histories. -/
theorem IsUniformCausalResetWord.of_causalBehEq {ℓ : ℕ}
    {Q Q' : CausalResponse A O} {r : Fin ℓ → A}
    (hr : IsUniformCausalResetWord Q r) (hQQ' : CausalBehEq Q Q') :
    IsUniformCausalResetWord Q' r := by
  intro pre ys hp'
  have hp : causalResponseProb Q (pre ++ List.ofFn (fun i => (r i, ys i))) ≠ 0 := by
    rwa [hQQ' _]
  exact causalBehEq_trans (causalBehEq_symm (causalBehEq_after_of_nonzero hQQ' _ hp))
    (causalBehEq_trans (hr pre ys hp) hQQ')

theorem isUniformCausalResetWord_iff_of_causalBehEq {ℓ : ℕ}
    {Q Q' : CausalResponse A O} (hQQ' : CausalBehEq Q Q') (r : Fin ℓ → A) :
    IsUniformCausalResetWord Q r ↔ IsUniformCausalResetWord Q' r :=
  ⟨fun h => h.of_causalBehEq hQQ', fun h => h.of_causalBehEq (causalBehEq_symm hQQ')⟩

/-- The stronger all-history controlled-reset assumption from the written
reset-word theorem implies the reachable, quotient-safe interface. -/
theorem isUniformCausalResetWord_of_all_histories {ℓ : ℕ}
    (Q : CausalResponse A O) (r : Fin ℓ → A)
    (hr : ∀ (pre : CausalHistory A O) (ys : Fin ℓ → O),
      CausalBehEq (causalResponseAfter Q (pre ++ List.ofFn (fun i => (r i, ys i)))) Q) :
    IsUniformCausalResetWord Q r := fun pre ys _ => hr pre ys

/-- Acquire with `ρ` for `m` steps, then deterministically execute the
specified reset word. Values after the reset are unused by the splice. -/
noncomputable def causalResetPrefixPolicy {ℓ : ℕ} (m : ℕ)
    (ρ : CausalPolicy A O) (r : Fin ℓ → A) : CausalPolicy A O := by
  classical
  exact fun h =>
    if hm : h.length < m then ρ h
    else if hj : h.length < m + ℓ then
      fun a => if a = r ⟨h.length - m, by omega⟩ then 1 else 0
    else ρ h

theorem causalResetPrefixPolicy_valid {ℓ : ℕ} (m : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A) :
    IsCausalPolicy (causalResetPrefixPolicy m ρ r) := by
  classical
  intro h
  simp only [causalResetPrefixPolicy]
  split_ifs
  · exact hρ h
  · constructor
    · intro a
      dsimp
      split_ifs <;> norm_num
    · simp
  · exact hρ h

theorem causalResetPrefixPolicy_reset_row {ℓ : ℕ} (m : ℕ)
    (ρ : CausalPolicy A O) (r : Fin ℓ → A) (j : Fin ℓ)
    (h : CausalHistory A O) (hlen : h.length = m + j.val) (a : A) :
    causalResetPrefixPolicy m ρ r h a = if a = r j then 1 else 0 := by
  classical
  have hnot : ¬ h.length < m := by omega
  have hlt : h.length < m + ℓ := by omega
  simp only [causalResetPrefixPolicy, hnot, dite_false, hlt, dite_true]
  have hj : (⟨h.length - m, by omega⟩ : Fin ℓ) = j := by
    apply Fin.ext
    change h.length - m = j.val
    omega
  rw [hj]

/-- The actual one-run policy: prefix acquisition, reset word, then the
requested policy on its within-block history alone. -/
noncomputable def causalResetSplicePolicy {ℓ : ℕ} (m : ℕ)
    (ρ : CausalPolicy A O) (r : Fin ℓ → A) (π : CausalPolicy A O) : CausalPolicy A O :=
  causalSplicePolicy (m + ℓ) (causalResetPrefixPolicy m ρ r) π

theorem causalResetSplicePolicy_valid {ℓ : ℕ} (m : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π) :
    IsCausalPolicy (causalResetSplicePolicy m ρ r π) :=
  causalSplicePolicy_valid _ _ _ (causalResetPrefixPolicy_valid m ρ hρ r) hπ

/-- Every supported acquisition/reset prefix actually executed the requested
reset actions; this is derived from the single-run policy product. -/
theorem causalResetSplicePolicy_supported_reset_actions {ℓ : ℕ} (m : ℕ)
    (ρ : CausalPolicy A O) (r : Fin ℓ → A) (π : CausalPolicy A O)
    (Q : CausalResponse A O) (pre : CausalFiniteTrace A O (m + ℓ))
    (hp : causalTraceProb (causalResetSplicePolicy m ρ r π) Q (List.ofFn pre) ≠ 0)
    (j : Fin ℓ) : (pre (Fin.natAdd m j)).1 = r j := by
  classical
  let h := (List.ofFn pre).take (m + j.val)
  have hlen : h.length = m + j.val := by
    simp [h, List.length_take]
  have ht := causalTraceProb_policy_ne_zero (causalResetSplicePolicy m ρ r π) Q
    (List.ofFn pre) hp ⟨m + j.val, by simp only [List.length_ofFn]; omega⟩
  have hlt : h.length < m + ℓ := by omega
  simp only [List.getElem_ofFn] at ht
  change causalSplicePolicy (m + ℓ) (causalResetPrefixPolicy m ρ r) π h
    (pre (Fin.natAdd m j)).1 ≠ 0 at ht
  rw [causalSplicePolicy, if_pos hlt,
    causalResetPrefixPolicy_reset_row m ρ r j h hlen] at ht
  by_contra hne
  simp [hne] at ht

/-- A supported reset endpoint has exactly the original continuation world
in the controlled-trace quotient. -/
theorem causalResetSplicePolicy_continuation {ℓ : ℕ} (m : ℕ)
    (ρ : CausalPolicy A O) (r : Fin ℓ → A) (π : CausalPolicy A O)
    (Q : CausalResponse A O) (hr : IsUniformCausalResetWord Q r)
    (pre : CausalFiniteTrace A O (m + ℓ))
    (hp : causalTraceProb (causalResetSplicePolicy m ρ r π) Q (List.ofFn pre) ≠ 0) :
    CausalBehEq (causalResponseAfter Q (List.ofFn pre)) Q := by
  let ys : Fin ℓ → O := fun j => (pre (Fin.natAdd m j)).2
  have heq : List.ofFn pre =
      List.ofFn (fun i : Fin m => pre (Fin.castAdd ℓ i)) ++
        List.ofFn (fun j => (r j, ys j)) := by
    rw [List.ofFn_add]
    congr 1
    apply congrArg List.ofFn
    funext j
    exact Prod.ext (causalResetSplicePolicy_supported_reset_actions m ρ r π Q pre hp j) rfl
  have hresp : causalResponseProb Q (List.ofFn pre) ≠ 0 := by
    have hx := hp
    rw [causalTraceProb_factor] at hx
    exact (mul_ne_zero_iff.mp hx).2
  rw [heq] at hresp ⊢
  exact hr _ ys hresp

/-- **Uniform-reset finite block law.** After arbitrary prefix acquisition,
executing a uniform reset word and following `π` produces an exactly fresh
`π` experiment as the recorded final block of the same physical run. -/
theorem uniformResetWord_block_projection_exact {ℓ : ℕ} (m n : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) :
    finiteDecisionLaw
      (causalFiniteExperiment (causalResetSplicePolicy m ρ r π) Qs ((m + ℓ) + n))
      (finiteMapRule (causalBlockProjection (m + ℓ) n)) = causalFiniteExperiment π Qs n :=
  causalSplice_block_projection_exact (m + ℓ) n _ π
    (causalResetPrefixPolicy_valid m ρ hρ r) hπ Qs hQ
    (fun θ pre hp => causalResetSplicePolicy_continuation m ρ r π (Qs θ) (hr θ) pre hp)

/-- Exact stochastic comparison with an explicit deterministic block decoder. -/
theorem uniformResetWord_block_blackwell {ℓ : ℕ} (m n : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment (causalResetSplicePolicy m ρ r π) Qs ((m + ℓ) + n)) :=
  ⟨finiteMapRule (causalBlockProjection (m + ℓ) n), finiteMapRule_mem _,
    uniformResetWord_block_projection_exact m n ρ hρ r π hπ Qs hQ hr⟩

/-- Zero actual directed deficiency; the world class need not be finite. -/
theorem uniformResetWord_block_deficiency_zero [Nonempty Θ] [Nonempty A] [Nonempty O]
    {ℓ : ℕ} (m n : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) :
    finiteDeficiency
      (causalFiniteExperiment (causalResetSplicePolicy m ρ r π) Qs ((m + ℓ) + n))
      (causalFiniteExperiment π Qs n) = 0 :=
  finiteDeficiency_eq_zero_of_blackwellLE _ _
    (causalFiniteExperiment_valid _ (causalResetSplicePolicy_valid m ρ hρ r π hπ) Qs hQ _)
    (causalFiniteExperiment_valid π hπ Qs hQ n)
    (uniformResetWord_block_blackwell m n ρ hρ r π hπ Qs hQ hr)

end IdExp
