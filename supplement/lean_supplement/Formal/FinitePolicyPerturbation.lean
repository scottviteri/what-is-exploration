import Formal.CausalResponsePerturbation
import Formal.DeficiencyTriangle

/-!
# Finite-policy perturbation and source stability of deficiency

This module checks the two Lipschitz lemmas used by the approach-case note.
First, directed finite deficiency is one-Lipschitz in its source experiment
under a uniform rowwise total-variation bound.  Second, changing the action
row of a behavioral causal policy at depth `k` by at most `delta k` changes
the complete recorded horizon-`n` experiment by at most
`sum k in range n, delta k`, uniformly over the response world.

The causal bound retains actions in the acquired signal.  At one extension
step, the observation kernel therefore cancels exactly and the row distance
is the total variation between the two action distributions.  The full bound
then follows by the finite-bind telescope.
-/

namespace IdExp

open Finset Set

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Deficiency is one-Lipschitz in its source -/

variable {Theta X Y : Type*} [Fintype X] [Fintype Y]

/-- The identity decoder witnesses source-to-source deficiency at most any
uniform rowwise total-variation bound. -/
theorem finiteDeficiency_le_of_rowTV [Nonempty Theta]
    (E E' : FiniteExperiment Theta X) (d : Real)
    (hrow : forall theta, finiteTV (E theta) (E' theta) <= d) :
    finiteDeficiency E E' <= d := by
  classical
  let ident : X -> X -> Real := fun x y => if x = y then 1 else 0
  have hident : ident ∈ stochasticRules X X := identity_mem_stochasticRules X
  apply finiteDeficiency_le_of_decoder E E' ident hident d
  intro theta
  have hlaw : finiteDecisionLaw E ident theta = E theta := by
    funext y
    simp [finiteDecisionLaw, ident]
  change finiteTV (finiteDecisionLaw E ident theta) (E' theta) <= d
  rw [hlaw]
  exact hrow theta

/-- **Source Lipschitz lemma.**  For valid experiments on a common finite
signal space, a uniform rowwise TV bound controls the absolute change in
directed deficiency to every fixed valid target.  The parameter class may be
arbitrary and nonempty. -/
theorem abs_finiteDeficiency_sub_le_of_rowTV [Nonempty Theta]
    (E E' : FiniteExperiment Theta X) (F : FiniteExperiment Theta Y)
    (hE : IsFiniteExperiment E) (hE' : IsFiniteExperiment E')
    (hF : IsFiniteExperiment F) (d : Real)
    (hrow : forall theta, finiteTV (E theta) (E' theta) <= d) :
    |finiteDeficiency E F - finiteDeficiency E' F| <= d := by
  have hEE' : finiteDeficiency E E' <= d :=
    finiteDeficiency_le_of_rowTV E E' d hrow
  have hE'E : finiteDeficiency E' E <= d :=
    finiteDeficiency_le_of_rowTV E' E d fun theta => by
      rw [finiteTV_symm]
      exact hrow theta
  have hforward := finiteDeficiency_triangle E E' F hE hE' hF
  have hreverse := finiteDeficiency_triangle E' E F hE' hE hF
  rw [abs_le]
  constructor <;> linarith

/-! ## Behavioral-policy perturbation -/

variable {A O : Type*} [Fintype A] [Fintype O]

/-- With the response row fixed and the appended action retained in the
signal, TV between two one-step causal extension rules is exactly TV between
the two behavioral action rows. -/
theorem causalSharedTailRule_policy_tv_eq
    (pi rho : CausalPolicy A O) (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (n : Nat) (u : CausalFiniteTrace A O n) :
    finiteTV (causalSharedTailRule pi Q n u)
        (causalSharedTailRule rho Q n u) =
      finiteTV (pi (List.ofFn u)) (rho (List.ofFn u)) := by
  classical
  unfold finiteTV
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)).sum_comp,
    Fintype.sum_prod_type]
  have hsnoc (ao : A × O) (v : CausalFiniteTrace A O n) :
      (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)) (ao, v) =
        Fin.snoc v ao := by
    funext i
    exact Fin.snocEquiv_apply _ _ i
  simp_rw [hsnoc, causalSharedTailRule_snoc]
  have hd (ao : A × O) (v : CausalFiniteTrace A O n) :
      |(if u = v then pi (List.ofFn u) ao.1 * Q (List.ofFn u) ao.1 ao.2 else 0) -
        (if u = v then rho (List.ofFn u) ao.1 * Q (List.ofFn u) ao.1 ao.2 else 0)| =
      if u = v then
        |pi (List.ofFn u) ao.1 - rho (List.ofFn u) ao.1| *
          Q (List.ofFn u) ao.1 ao.2
      else 0 := by
    by_cases huv : u = v
    · subst v
      simp only [if_true]
      rw [← sub_mul, abs_mul,
        abs_of_nonneg ((hQ _ _).1 _)]
    · simp only [if_neg huv, sub_self, abs_zero]
  simp_rw [hd]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, (hQ _ _).2, mul_one]

/-- A depth-dependent uniform bound on policy-row TV telescopes through the
actual recorded causal experiment.  This is the note's policy perturbation
lemma in a slightly more reusable majorant form. -/
theorem causalFiniteExperiment_policy_tv_le_sum
    (pi rho : CausalPolicy A O) (hpi : IsCausalPolicy pi)
    (hrho : IsCausalPolicy rho) (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (delta : Nat -> Real)
    (hlocal : forall k (u : CausalFiniteTrace A O k),
      finiteTV (pi (List.ofFn u)) (rho (List.ofFn u)) <= delta k) :
    forall n,
      finiteTV
          (causalFiniteExperiment pi (fun _ : Unit => Q) n ())
          (causalFiniteExperiment rho (fun _ : Unit => Q) n ()) <=
        (∑ k ∈ Finset.range n, delta k)
  | 0 => by
      simp [finiteTV, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  | n + 1 => by
      have hstep (sigma : CausalPolicy A O) :
          causalFiniteExperiment sigma (fun _ : Unit => Q) (n + 1) () =
            PredictiveTransport.finiteBind
              (causalFiniteExperiment sigma (fun _ : Unit => Q) n ())
              (causalSharedTailRule sigma Q n) := by
        exact (congrFun (causalFiniteExperiment_sharedTail_step sigma
          (fun _ : Unit => Q) Q 0 n (fun _ _ _ _ _ => rfl) (Nat.zero_le n)) ()).symm
      rw [hstep pi, hstep rho]
      have hbind := PredictiveTransport.finiteTV_finiteBind_le
        (causalFiniteExperiment pi (fun _ : Unit => Q) n ())
        (causalFiniteExperiment rho (fun _ : Unit => Q) n ())
        ((causalFiniteExperiment_valid pi hpi _ (fun _ => hQ) n) ())
        (causalSharedTailRule pi Q n) (causalSharedTailRule rho Q n)
        (causalSharedTailRule_valid rho hrho Q hQ n)
        (fun u => by
          rw [causalSharedTailRule_policy_tv_eq pi rho Q hQ n u]
          exact hlocal n u)
      rw [Finset.sum_range_succ]
      calc
        _ <= delta n + finiteTV
            (causalFiniteExperiment pi (fun _ : Unit => Q) n ())
            (causalFiniteExperiment rho (fun _ : Unit => Q) n ()) := hbind
        _ = finiteTV
              (causalFiniteExperiment pi (fun _ : Unit => Q) n ())
              (causalFiniteExperiment rho (fun _ : Unit => Q) n ()) + delta n :=
            add_comm _ _
        _ <= (∑ k ∈ Finset.range n, delta k) + delta n :=
          add_le_add
            (causalFiniteExperiment_policy_tv_le_sum
              pi rho hpi hrho Q hQ delta hlocal n) le_rfl

variable [Nonempty A] [Nonempty O]

/-- The largest behavioral-row TV discrepancy on histories of exact length
`k`.  This is the finite maximum appearing in the paper's displayed policy
perturbation bound. -/
noncomputable def causalPolicyDepthTV
    (pi rho : CausalPolicy A O) (k : Nat) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun u : CausalFiniteTrace A O k =>
    finiteTV (pi (List.ofFn u)) (rho (List.ofFn u))

theorem causalPolicyRowTV_le_depthTV
    (pi rho : CausalPolicy A O) (k : Nat)
    (u : CausalFiniteTrace A O k) :
    finiteTV (pi (List.ofFn u)) (rho (List.ofFn u)) <=
      causalPolicyDepthTV pi rho k := by
  unfold causalPolicyDepthTV
  exact Finset.le_sup'
    (fun v : CausalFiniteTrace A O k =>
      finiteTV (pi (List.ofFn v)) (rho (List.ofFn v)))
    (Finset.mem_univ u)

/-- **Policy perturbation lemma, displayed form.**  At every world, the TV
distance between two horizon-`n` acquired experiments is bounded by the sum
over depths of the largest TV discrepancy between their action rows on a
history of that depth. -/
theorem causalFiniteExperiment_policy_tv_le_sum_depthTV
    (pi rho : CausalPolicy A O) (hpi : IsCausalPolicy pi)
    (hrho : IsCausalPolicy rho) (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (n : Nat) :
    finiteTV
        (causalFiniteExperiment pi (fun _ : Unit => Q) n ())
        (causalFiniteExperiment rho (fun _ : Unit => Q) n ()) <=
      ∑ k ∈ Finset.range n, causalPolicyDepthTV pi rho k :=
  causalFiniteExperiment_policy_tv_le_sum pi rho hpi hrho Q hQ
    (causalPolicyDepthTV pi rho)
    (fun k u => causalPolicyRowTV_le_depthTV pi rho k u) n

end

end IdExp
