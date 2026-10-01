import Formal.PolicyBehavior
import Formal.CausalProcess
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countable mixtures of history policies

A once-drawn policy index can be hidden inside an ordinary randomized history
policy. The mixture uses action-propensity masses, so its conditional weights
are independent of the world. Rows at histories with zero mixture propensity
are supplied by the existing policy-behavior reconstruction.
-/

namespace IdExp
noncomputable section
open scoped ENNReal

variable {A O I : Type*} [Fintype A] [Fintype O]

namespace PolicyBehavior

/-- Countable weights times policy-behavior masses form a summable family. -/
theorem summable_weighted_mass (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (ps : I → PolicyBehavior A O) (h : CausalHistory A O) :
    Summable (fun i => w i * (ps i).mass h) := by
  apply Summable.of_nonneg_of_le
    (fun i => mul_nonneg (hw i) ((ps i).nonneg h)) _ hs
  intro i
  exact mul_le_of_le_one_right (hw i) ((ps i).mass_le_one h)

/-- A countable once-drawn mixture at the action-propensity level. -/
def countableMix (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (ht : ∑' i, w i = 1) (ps : I → PolicyBehavior A O) :
    PolicyBehavior A O where
  mass h := ∑' i, w i * (ps i).mass h
  root := by simpa using ht
  nonneg h := tsum_nonneg fun i => mul_nonneg (hw i) ((ps i).nonneg h)
  obs_indep h a o o' := by simp_rw [(ps _).obs_indep h a o o']
  consistent h o := by
    rw [← Summable.tsum_finsetSum]
    · simp_rw [← Finset.mul_sum, (ps _).consistent h o]
    · intro a _
      exact summable_weighted_mass w hw hs ps _

@[simp]
theorem countableMix_mass (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (ht : ∑' i, w i = 1) (ps : I → PolicyBehavior A O)
    (h : CausalHistory A O) :
    (countableMix w hw hs ht ps).mass h = ∑' i, w i * (ps i).mass h := rfl

theorem weighted_mass_le_countableMix (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (ht : ∑' i, w i = 1) (ps : I → PolicyBehavior A O)
    (i : I) (h : CausalHistory A O) :
    w i * (ps i).mass h ≤ (countableMix w hw hs ht ps).mass h := by
  exact (summable_weighted_mass w hw hs ps h).le_tsum i
    (fun j _ => mul_nonneg (hw j) ((ps j).nonneg h))

end PolicyBehavior

/-- The mixture is an actual valid randomized history policy. -/
def countablePolicyMixture [Nonempty A] [Nonempty O]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (ht : ∑' i, w i = 1)
    (π : I → ValidCausalPolicy A O) : ValidCausalPolicy A O :=
  let c := PolicyBehavior.countableMix w hw hs ht
    (fun i => PolicyBehavior.ofPolicy (π i).1 (π i).2)
  ⟨c.toPolicy, c.toPolicy_valid⟩

theorem countablePolicyMixture_prob [Nonempty A] [Nonempty O]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (ht : ∑' i, w i = 1)
    (π : I → ValidCausalPolicy A O) (h : CausalHistory A O) :
    causalPolicyProb (countablePolicyMixture w hw hs ht π).1 h =
      ∑' i, w i * causalPolicyProb (π i).1 h := by
  let c := PolicyBehavior.countableMix w hw hs ht
    (fun i => PolicyBehavior.ofPolicy (π i).1 (π i).2)
  change (PolicyBehavior.ofPolicy c.toPolicy c.toPolicy_valid).mass h = c.mass h
  rw [PolicyBehavior.ofPolicy_toPolicy]

/-- Exact mixture of finite record laws in every response environment. -/
theorem countablePolicyMixture_trace [Nonempty A] [Nonempty O]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (ht : ∑' i, w i = 1)
    (π : I → ValidCausalPolicy A O) (Q : CausalResponse A O) (h : CausalHistory A O) :
    causalTraceProb (countablePolicyMixture w hw hs ht π).1 Q h =
      ∑' i, w i * causalTraceProb (π i).1 Q h := by
  simp_rw [causalTraceProb_factor]
  rw [countablePolicyMixture_prob, ← tsum_mul_right]
  simp_rw [mul_assoc]

theorem countablePolicyMixture_root_zero [Nonempty A] [Nonempty O]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (ht : ∑' i, w i = 1)
    (π : I → ValidCausalPolicy A O) (a : A) (hroot : ∀ i, (π i).1 [] a = 0) :
    (countablePolicyMixture w hw hs ht π).1 [] a = 0 := by
  have hp := countablePolicyMixture_prob w hw hs ht π [(a, Classical.arbitrary O)]
  simpa [causalPolicyProb, causalPolicyProbFrom, hroot] using hp

/-- Each weighted component is bounded by the mixed finite record law. -/
theorem weighted_trace_le_countablePolicyMixture [Nonempty A] [Nonempty O]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (ht : ∑' i, w i = 1)
    (π : I → ValidCausalPolicy A O) (i : I)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) (h : CausalHistory A O) :
    w i * causalTraceProb (π i).1 Q h ≤
      causalTraceProb (countablePolicyMixture w hw hs ht π).1 Q h := by
  simp only [causalTraceProb_factor, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (causalResponseProbFrom_nonneg Q hQ [] h)
  rw [countablePolicyMixture_prob]
  exact PolicyBehavior.weighted_mass_le_countableMix w hw hs ht
    (fun i => PolicyBehavior.ofPolicy (π i).1 (π i).2) i h

end
end IdExp
