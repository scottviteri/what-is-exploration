import Formal.UniformResetSchedule
import Formal.PredictiveTransport
import Formal.NativeDistance

/-!
# Approximate reset words on actual causal transcripts

Block projection is the mixture of the actual continuation experiments at
the cut. Consequently, a native-depth bound on supported reset endpoints
bounds the output TV and directed deficiency by the same constant. Null
histories require no reset condition, and the decoder is the deterministic
projection of the recorded block, independent of the world.
-/

namespace IdExp

open Finset Set Filter Topology
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- Projection of a spliced run is exactly the mixture of its genuine
continuation laws, before imposing any reset or independence assumption. -/
theorem causalSplice_block_projection_mixture (k n : ℕ)
    (ρ π : CausalPolicy A O) (Qs : Θ → CausalResponse A O) (θ : Θ)
    (w : CausalFiniteTrace A O n) :
    finiteDecisionLaw
      (causalFiniteExperiment (causalSplicePolicy k ρ π) Qs (k + n))
      (finiteMapRule (causalBlockProjection k n)) θ w =
    ∑ pre : CausalFiniteTrace A O k,
      causalFiniteExperiment (causalSplicePolicy k ρ π) Qs k θ pre *
        causalTraceProb π (causalResponseAfter (Qs θ) (List.ofFn pre)) (List.ofFn w) := by
  classical
  have hfactor (pre : CausalFiniteTrace A O k) (v : CausalFiniteTrace A O n) :
      causalFiniteExperiment (causalSplicePolicy k ρ π) Qs (k + n) θ
        (Fin.append pre v) =
      causalFiniteExperiment (causalSplicePolicy k ρ π) Qs k θ pre *
        causalTraceProb π (causalResponseAfter (Qs θ) (List.ofFn pre)) (List.ofFn v) := by
    change causalTraceProb _ _ (List.ofFn (Fin.append pre v)) = _
    rw [List.ofFn_add]
    simp only [Fin.append_left', Fin.append_right]
    exact causalTraceProb_splice_append k ρ π (Qs θ) _ _ (by simp)
  unfold finiteDecisionLaw
  rw [← (causalBlockAppendEquiv (A := A) (O := O) k n).sum_comp,
    Fintype.sum_prod_type]
  simp only [causalBlockAppendEquiv, Equiv.coe_fn_mk, finiteMapRule,
    causalBlockProjection_append, hfactor, mul_ite, mul_one, mul_zero]
  simp

/-- An error bound at every supported continuation survives averaging over
the actual world-dependent prefix law. Unsupported continuations are ignored. -/
theorem causalSplice_block_projection_tv_le (k n : ℕ)
    (ρ π : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (δ : ℝ)
    (hlocal : ∀ θ (pre : CausalFiniteTrace A O k),
      causalTraceProb (causalSplicePolicy k ρ π) (Qs θ) (List.ofFn pre) ≠ 0 →
      finiteTV
        (fun w : CausalFiniteTrace A O n =>
          causalTraceProb π (causalResponseAfter (Qs θ) (List.ofFn pre)) (List.ofFn w))
        (causalFiniteExperiment π Qs n θ) ≤ δ) (θ : Θ) :
    finiteTV
      (finiteDecisionLaw
        (causalFiniteExperiment (causalSplicePolicy k ρ π) Qs (k + n))
        (finiteMapRule (causalBlockProjection k n)) θ)
      (causalFiniteExperiment π Qs n θ) ≤ δ := by
  let p := causalFiniteExperiment (causalSplicePolicy k ρ π) Qs k θ
  let G (pre : CausalFiniteTrace A O k) (w : CausalFiniteTrace A O n) :=
    causalTraceProb π (causalResponseAfter (Qs θ) (List.ofFn pre)) (List.ofFn w)
  let T := causalFiniteExperiment π Qs n θ
  have hp : IsDist p := causalFiniteExperiment_valid _
    (causalSplicePolicy_valid k ρ π hρ hπ) Qs hQ k θ
  have hmix : finiteDecisionLaw
      (causalFiniteExperiment (causalSplicePolicy k ρ π) Qs (k + n))
      (finiteMapRule (causalBlockProjection k n)) θ = PredictiveTransport.finiteBind p G := by
    funext w
    exact causalSplice_block_projection_mixture k n ρ π Qs θ w
  have hconst : PredictiveTransport.finiteBind p (fun _ => T) = T := by
    funext w
    simp only [PredictiveTransport.finiteBind]
    rw [← Finset.sum_mul, hp.2, one_mul]
  change finiteTV _ T ≤ δ
  rw [hmix, ← hconst]
  calc
    finiteTV (PredictiveTransport.finiteBind p G)
        (PredictiveTransport.finiteBind p (fun _ => T)) ≤
      ∑ pre, p pre * finiteTV (G pre) T :=
      PredictiveTransport.finiteTV_finiteBind_same_source_le_sum p hp G (fun _ => T)
    _ ≤ ∑ pre, p pre * δ := by
      apply Finset.sum_le_sum
      intro pre _
      by_cases hpre : p pre = 0
      · simp [hpre]
      · exact mul_le_mul_of_nonneg_left (hlocal θ pre hpre) (hp.1 pre)
    _ = δ := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- A quotient-safe depth-`n` approximate reset condition. The error is
native TV distance between the reachable continuation world and the initial
world, not a bound on raw response coordinates at impossible histories. -/
def IsCausalResetWordAtDepth {ℓ : ℕ} (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (r : Fin ℓ → A) (n : ℕ) (δ : ℝ) : Prop := by
  classical
  exact ∀ (pre : CausalHistory A O) (ys : Fin ℓ → O),
    causalResponseProb Q (pre ++ List.ofFn (fun i => (r i, ys i))) ≠ 0 →
      nativeDepthDist n
        ⟨causalResponseAfter Q (pre ++ List.ofFn (fun i => (r i, ys i))),
          causalResponseAfter_valid Q hQ _⟩ ⟨Q, hQ⟩ ≤ δ

/-- Native control of the supported reset endpoints bounds the actual
randomized target-policy continuation at the reset cut. -/
theorem approximateResetWord_supported_continuation_tv_le {ℓ : ℕ} (m n : ℕ)
    (ρ : CausalPolicy A O) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) (δ : ℝ)
    (hr : IsCausalResetWordAtDepth Q hQ r n δ)
    (pre : CausalFiniteTrace A O (m + ℓ))
    (hp : causalTraceProb (causalResetSplicePolicy m ρ r π) Q (List.ofFn pre) ≠ 0) :
    finiteTV
      (fun w : CausalFiniteTrace A O n =>
        causalTraceProb π (causalResponseAfter Q (List.ofFn pre)) (List.ofFn w))
      (fun w : CausalFiniteTrace A O n => causalTraceProb π Q (List.ofFn w)) ≤ δ := by
  classical
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
    rw [causalTraceProb_factor] at hp
    exact (mul_ne_zero_iff.mp hp).2
  have hdist : nativeDepthDist n
      ⟨causalResponseAfter Q (List.ofFn pre), causalResponseAfter_valid Q hQ _⟩
      ⟨Q, hQ⟩ ≤ δ := by
    rw [heq] at hresp ⊢
    exact hr _ ys hresp
  exact (causalPolicy_tv_le_nativeDepthDist π hπ n
    ⟨causalResponseAfter Q (List.ofFn pre), causalResponseAfter_valid Q hQ _⟩
    ⟨Q, hQ⟩).trans hdist

/-- Actual deterministic projection after an approximate reset has error
at most `δ`, uniformly over the declared (possibly infinite) world class. -/
theorem approximateResetWord_block_projection_tv_le {ℓ : ℕ} (m n : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (δ : ℝ)
    (hr : ∀ θ, IsCausalResetWordAtDepth (Qs θ) (hQ θ) r n δ) (θ : Θ) :
    finiteTV
      (finiteDecisionLaw
        (causalFiniteExperiment (causalResetSplicePolicy m ρ r π) Qs ((m + ℓ) + n))
        (finiteMapRule (causalBlockProjection (m + ℓ) n)) θ)
      (causalFiniteExperiment π Qs n θ) ≤ δ :=
  causalSplice_block_projection_tv_le (m + ℓ) n _ π
    (causalResetPrefixPolicy_valid m ρ hρ r) hπ Qs hQ δ
    (fun θ pre hp => approximateResetWord_supported_continuation_tv_le
      m n ρ r π hπ (Qs θ) (hQ θ) δ (hr θ) pre hp) θ

theorem approximateResetWord_block_deficiency_le {ℓ : ℕ} (m n : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (δ : ℝ)
    (hr : ∀ θ, IsCausalResetWordAtDepth (Qs θ) (hQ θ) r n δ) :
    finiteDeficiency
      (causalFiniteExperiment (causalResetSplicePolicy m ρ r π) Qs ((m + ℓ) + n))
      (causalFiniteExperiment π Qs n) ≤ δ :=
  finiteDeficiency_le_of_decoder _ _
    (finiteMapRule (causalBlockProjection (m + ℓ) n)) (finiteMapRule_mem _) δ
    (approximateResetWord_block_projection_tv_le m n ρ hρ r π hπ Qs hQ δ hr)

end
end IdExp
