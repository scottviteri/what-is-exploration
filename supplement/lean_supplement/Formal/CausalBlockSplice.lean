import Formal.ControlledHankel
import Formal.CausalEpisodicCoverage

/-!
# Actual one-run block splicing and exact extraction

A policy first runs an arbitrary acquisition prefix, then feeds only the
within-block history to another policy. When every supported prefix leaves
the same controlled-trace behavior, projection onto the later block is an
exact decoder of that policy's original experiment. The joint law and the
projection identity are proved from causal trace products, not assumed.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O]

/-- The causal continuation after an arbitrary chronological history. -/
def causalResponseAfter (Q : CausalResponse A O) (pre : CausalHistory A O) :
    CausalResponse A O := fun h => Q (pre ++ h)

theorem causalResponseAfter_valid (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (pre : CausalHistory A O) : IsCausalResponse (causalResponseAfter Q pre) :=
  fun h a => hQ (pre ++ h) a

theorem causalResponseProbFrom_after (Q : CausalResponse A O)
    (pre h rest : CausalHistory A O) :
    causalResponseProbFrom (causalResponseAfter Q pre) h rest =
      causalResponseProbFrom Q (pre ++ h) rest := by
  induction rest generalizing h with
  | nil => rfl
  | cons ao rest ih =>
      simp only [causalResponseProbFrom, causalResponseAfter, ih, List.append_assoc]

theorem causalResponseProb_after (Q : CausalResponse A O)
    (pre rest : CausalHistory A O) :
    causalResponseProb (causalResponseAfter Q pre) rest =
      causalResponseProbFrom Q pre rest := by
  simpa [causalResponseProb] using causalResponseProbFrom_after Q pre [] rest

/-- Continuation behavior is quotient-invariant at a reachable prefix. -/
theorem causalBehEq_after_of_nonzero {Q Q' : CausalResponse A O}
    (hQQ' : CausalBehEq Q Q') (pre : CausalHistory A O)
    (hpre : causalResponseProb Q pre ≠ 0) :
    CausalBehEq (causalResponseAfter Q pre) (causalResponseAfter Q' pre) := by
  intro rest
  simp only [causalResponseProb_after]
  apply mul_left_cancel₀ hpre
  have heq := hQQ' (pre ++ rest)
  have hfactor (R : CausalResponse A O) :
      causalResponseProb R (pre ++ rest) =
        causalResponseProb R pre * causalResponseProbFrom R pre rest :=
    controlledHankel_eq_prefix_mul R pre rest
  rw [hfactor Q, hfactor Q', ← hQQ' pre] at heq
  exact heq

/-- Follow `ρ` for `k` steps, then follow `π` on the within-block history. -/
noncomputable def causalSplicePolicy (k : ℕ) (ρ π : CausalPolicy A O) :
    CausalPolicy A O :=
  fun h => if h.length < k then ρ h else π (h.drop k)

theorem causalSplicePolicy_valid (k : ℕ) (ρ π : CausalPolicy A O)
    (hρ : IsCausalPolicy ρ) (hπ : IsCausalPolicy π) :
    IsCausalPolicy (causalSplicePolicy k ρ π) := by
  intro h
  simp only [causalSplicePolicy]
  split_ifs
  · exact hρ h
  · exact hπ _

/-- Every action of a supported trace has positive policy support at its
actual preceding prefix. -/
theorem causalTraceProb_policy_ne_zero (π : CausalPolicy A O) (Q : CausalResponse A O)
    (h : CausalHistory A O) (hh : causalTraceProb π Q h ≠ 0) (i : Fin h.length) :
    π (h.take i.val) (h[i.val]).1 ≠ 0 := by
  have hprod : causalTraceProb π Q (h.take i.val) *
      causalTraceProbFrom π Q (h.take i.val) (h.drop i.val) ≠ 0 := by
    rwa [← causalTraceProb_append, List.take_append_drop]
  have htail := (mul_ne_zero_iff.mp hprod).2
  rw [List.drop_eq_getElem_cons i.isLt] at htail
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htail).1).1

theorem causalTraceProbFrom_splice_after (k : ℕ) (ρ π : CausalPolicy A O)
    (Q : CausalResponse A O) (pre : CausalHistory A O) (hpre : pre.length = k)
    (h rest : CausalHistory A O) :
    causalTraceProbFrom (causalSplicePolicy k ρ π) Q (pre ++ h) rest =
      causalTraceProbFrom π (causalResponseAfter Q pre) h rest := by
  induction rest generalizing h with
  | nil => rfl
  | cons ao rest ih =>
      have hlen : ¬ (pre ++ h).length < k := by simp [hpre]
      simp only [causalTraceProbFrom, causalSplicePolicy, hlen, if_false,
        List.drop_left' hpre, causalResponseAfter]
      rw [List.append_assoc, ih]

/-- The conditional post-cut trace product uses only the within-block policy
and the actual continuation world. -/
theorem causalTraceProb_splice_append (k : ℕ) (ρ π : CausalPolicy A O)
    (Q : CausalResponse A O) (pre rest : CausalHistory A O) (hpre : pre.length = k) :
    causalTraceProb (causalSplicePolicy k ρ π) Q (pre ++ rest) =
      causalTraceProb (causalSplicePolicy k ρ π) Q pre *
        causalTraceProb π (causalResponseAfter Q pre) rest := by
  rw [causalTraceProb_append]
  congr 1
  simpa [causalTraceProb] using
    causalTraceProbFrom_splice_after k ρ π Q pre hpre [] rest

/-- Concatenate two finite signals in chronological order. -/
def causalBlockAppendEquiv (k n : ℕ) :
    CausalFiniteTrace A O k × CausalFiniteTrace A O n ≃ CausalFiniteTrace A O (k + n) where
  toFun w := Fin.append w.1 w.2
  invFun w := (fun i => w (Fin.castAdd n i), fun i => w (Fin.natAdd k i))
  left_inv w := by ext i <;> simp
  right_inv w := Fin.append_castAdd_natAdd

/-- The recorded final block, retaining its actions and observations. -/
def causalBlockProjection (k n : ℕ) :
    CausalFiniteTrace A O (k + n) → CausalFiniteTrace A O n :=
  fun w i => w (Fin.natAdd k i)

@[simp] theorem causalBlockProjection_append (k n : ℕ)
    (pre : CausalFiniteTrace A O k) (w : CausalFiniteTrace A O n) :
    causalBlockProjection k n (Fin.append pre w) = w := by
  funext i
  simp [causalBlockProjection]

/-- **Exact block extraction from an actual one-run experiment.** Suppose
every supported cut-prefix has the original continuation behavior. The
deterministic projection of the spliced experiment is precisely the target
policy experiment, with no independence or joint-law premise. -/
theorem causalSplice_block_projection_exact (k n : ℕ)
    (ρ π : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hreset : ∀ θ (pre : CausalFiniteTrace A O k),
      causalTraceProb (causalSplicePolicy k ρ π) (Qs θ) (List.ofFn pre) ≠ 0 →
        CausalBehEq (causalResponseAfter (Qs θ) (List.ofFn pre)) (Qs θ)) :
    finiteDecisionLaw
      (causalFiniteExperiment (causalSplicePolicy k ρ π) Qs (k + n))
      (finiteMapRule (causalBlockProjection k n)) = causalFiniteExperiment π Qs n := by
  classical
  have hπs := causalSplicePolicy_valid k ρ π hρ hπ
  have hfactor (θ : Θ) (pre : CausalFiniteTrace A O k) (w : CausalFiniteTrace A O n) :
      causalFiniteExperiment (causalSplicePolicy k ρ π) Qs (k + n) θ
        (Fin.append pre w) =
      causalFiniteExperiment (causalSplicePolicy k ρ π) Qs k θ pre *
        causalFiniteExperiment π Qs n θ w := by
    change causalTraceProb _ _ (List.ofFn (Fin.append pre w)) = _
    rw [List.ofFn_add]
    simp only [Fin.append_left', Fin.append_right]
    rw [causalTraceProb_splice_append k ρ π (Qs θ) _ _ (by simp)]
    by_cases hp : causalTraceProb (causalSplicePolicy k ρ π) (Qs θ) (List.ofFn pre) = 0
    · simp [causalFiniteExperiment, hp]
    · rw [causalTraceProb_eq_of_causalBehEq π (hreset θ pre hp)]
      rfl
  funext θ w
  unfold finiteDecisionLaw
  rw [← (causalBlockAppendEquiv (A := A) (O := O) k n).sum_comp,
    Fintype.sum_prod_type]
  simp only [causalBlockAppendEquiv, Equiv.coe_fn_mk, finiteMapRule,
    causalBlockProjection_append, hfactor, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, (causalFiniteExperiment_valid _ hπs Qs hQ k θ).2, one_mul]

theorem causalSplice_block_blackwell (k n : ℕ)
    (ρ π : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hreset : ∀ θ (pre : CausalFiniteTrace A O k),
      causalTraceProb (causalSplicePolicy k ρ π) (Qs θ) (List.ofFn pre) ≠ 0 →
        CausalBehEq (causalResponseAfter (Qs θ) (List.ofFn pre)) (Qs θ)) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment (causalSplicePolicy k ρ π) Qs (k + n)) :=
  ⟨finiteMapRule (causalBlockProjection k n), finiteMapRule_mem _,
    causalSplice_block_projection_exact k n ρ π hρ hπ Qs hQ hreset⟩

end IdExp
