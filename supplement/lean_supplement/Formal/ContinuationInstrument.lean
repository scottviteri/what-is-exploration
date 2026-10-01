import Formal.CausalSubbehavior
import Formal.CausalBehaviorExperiment
import Formal.FiniteBlackwell

/-!
# Finite continuation instruments

An ordinary finite experiment records only the probability of each signal.
For sequential use, a signal can carry more: its unnormalized controlled
continuation behavior.  A `ContinuationInstrument` packages a finite family
of such outcome-labelled subbehaviors whose root masses sum to one in every
world.

Taking roots recovers an ordinary finite statistical experiment.  A finite
stochastic garbling acts on the complete subbehaviors, not only their roots;
the root experiment of the result is exactly the usual Blackwell garbling.
The canonical fixed-horizon policy instrument attaches to a history `h` the
subbehavior with mass

`causalPolicyProb pi h * p.mass (h ++ rest)`.

This module is structural.  It does not claim that preserving these complete
continuations is necessary for any particular exploration objective, nor
does it define an adapted continuation-sufficiency order.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {A O Theta X Y Z : Type*}
  [Fintype A] [Fintype O] [Fintype X]

/-- A finite signal whose every outcome carries an unnormalized controlled
continuation behavior.  Root masses form a probability vector in each world.
The parameter type need not be finite. -/
structure ContinuationInstrument (Theta X A O : Type*)
    [Fintype X] [Fintype O] where
  /-- The unnormalized continuation attached to an outcome. -/
  branch : Theta -> X -> CausalSubbehavior A O
  /-- Outcome root masses sum to one in each world. -/
  root_sum : ∀ theta, ∑ x, (branch theta x).mass [] = 1

namespace ContinuationInstrument

@[ext]
theorem ext {I J : ContinuationInstrument Theta X A O}
    (h : I.branch = J.branch) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- Forget continuation coordinates and retain only outcome probabilities. -/
def rootExperiment (I : ContinuationInstrument Theta X A O) :
    FiniteExperiment Theta X :=
  fun theta x => (I.branch theta x).mass []

@[simp]
theorem rootExperiment_apply (I : ContinuationInstrument Theta X A O)
    (theta : Theta) (x : X) :
    I.rootExperiment theta x = (I.branch theta x).mass [] :=
  rfl

/-- The roots of a continuation instrument form a genuine finite
statistical experiment. -/
theorem rootExperiment_valid (I : ContinuationInstrument Theta X A O) :
    IsFiniteExperiment I.rootExperiment := by
  intro theta
  exact ⟨fun x => (I.branch theta x).nonneg [], I.root_sum theta⟩

/-- Every branch root is at most one because all branch roots are
nonnegative and their finite sum is one. -/
theorem branch_root_le_one (I : ContinuationInstrument Theta X A O)
    (theta : Theta) (x : X) : (I.branch theta x).mass [] <= 1 := by
  rw [<- I.root_sum theta]
  exact Finset.single_le_sum
    (fun y _ => (I.branch theta y).nonneg []) (Finset.mem_univ x)

/-- The complete continuation branch obtained after stochastically merging
the source outcomes through `G`. -/
noncomputable def garbledBranch [Fintype Y]
    (I : ContinuationInstrument Theta X A O)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y)
    (theta : Theta) (y : Y) : CausalSubbehavior A O where
  mass := fun rest => ∑ x, (I.branch theta x).mass rest * G x y
  nonneg := by
    intro rest
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg ((I.branch theta x).nonneg rest)
        ((hG x (Set.mem_univ x)).1 y)
  consistent := by
    intro rest a
    rw [Finset.sum_comm]
    calc
      ∑ x, ∑ o,
          (I.branch theta x).mass (rest ++ [(a, o)]) * G x y =
          ∑ x, (∑ o,
            (I.branch theta x).mass (rest ++ [(a, o)])) * G x y := by
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.sum_mul]
      _ = ∑ x, (I.branch theta x).mass rest * G x y := by
            apply Finset.sum_congr rfl
            intro x _
            rw [(I.branch theta x).consistent rest a]

@[simp]
theorem garbledBranch_mass [Fintype Y]
    (I : ContinuationInstrument Theta X A O)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y)
    (theta : Theta) (y : Y) (rest : CausalHistory A O) :
    (I.garbledBranch G hG theta y).mass rest =
      ∑ x, (I.branch theta x).mass rest * G x y :=
  rfl

/-- Garble complete outcome-labelled subbehaviors by a finite stochastic
matrix. -/
noncomputable def garble [Fintype Y]
    (I : ContinuationInstrument Theta X A O)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y) :
    ContinuationInstrument Theta Y A O where
  branch := I.garbledBranch G hG
  root_sum := by
    intro theta
    change (∑ y, ∑ x, (I.branch theta x).mass [] * G x y) = 1
    rw [Finset.sum_comm]
    calc
      ∑ x, ∑ y, (I.branch theta x).mass [] * G x y =
          ∑ x, (I.branch theta x).mass [] * (∑ y, G x y) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
      _ = ∑ x, (I.branch theta x).mass [] := by
            apply Finset.sum_congr rfl
            intro x _
            rw [(hG x (Set.mem_univ x)).2, mul_one]
      _ = 1 := I.root_sum theta

@[simp]
theorem garble_branch_mass [Fintype Y]
    (I : ContinuationInstrument Theta X A O)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y)
    (theta : Theta) (y : Y) (rest : CausalHistory A O) :
    ((I.garble G hG).branch theta y).mass rest =
      ∑ x, (I.branch theta x).mass rest * G x y :=
  rfl

/-- Taking roots after instrument garbling is exactly ordinary finite
Blackwell post-processing. -/
theorem rootExperiment_garble [Fintype Y]
    (I : ContinuationInstrument Theta X A O)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y) :
    (I.garble G hG).rootExperiment =
      finiteDecisionLaw I.rootExperiment G := by
  rfl

/-- Garbling by the identity stochastic matrix preserves the complete
continuation instrument, not merely its root experiment. -/
theorem garble_identity [DecidableEq X]
    (I : ContinuationInstrument Theta X A O) :
    I.garble (fun x x' => if x = x' then 1 else 0)
        (identity_mem_stochasticRules X) = I := by
  apply ContinuationInstrument.ext
  funext theta x
  apply CausalSubbehavior.ext
  funext rest
  simp [garble]

/-- Successive finite garblings compose on complete continuation branches. -/
theorem garble_garble [Fintype Y] [Fintype Z]
    (I : ContinuationInstrument Theta X A O)
    (G : X -> Y -> Real) (hG : G ∈ stochasticRules X Y)
    (H : Y -> Z -> Real) (hH : H ∈ stochasticRules Y Z) :
    (I.garble G hG).garble H hH =
      I.garble (stochasticRuleComp G H)
        (stochasticRuleComp_mem_stochasticRules hG hH) := by
  apply ContinuationInstrument.ext
  funext theta z
  apply CausalSubbehavior.ext
  funext rest
  have hcomp := finiteDecisionLaw_stochasticRuleComp
    (E := fun (_ : Unit) x => (I.branch theta x).mass rest) G H
  exact congrFun (congrFun hcomp.symm ()) z

end ContinuationInstrument

/-! ## Canonical policy-history instrument -/

/-- A valid causal policy assigns a nonnegative product weight to every
finite controlled history. -/
theorem causalPolicyProb_nonneg_of_valid (pi : CausalPolicy A O)
    (hpi : IsCausalPolicy pi) (h : CausalHistory A O) :
    0 <= causalPolicyProb pi h := by
  have aux (pre rest : CausalHistory A O) :
      0 <= causalPolicyProbFrom pi pre rest := by
    induction rest generalizing pre with
    | nil => simp [causalPolicyProbFrom]
    | cons ao tail ih =>
        simp only [causalPolicyProbFrom]
        exact mul_nonneg ((hpi pre).1 ao.1) (ih (pre ++ [ao]))
  exact aux [] h

/-- The policy-weighted unnormalized continuation attached to one finite
history.  Future actions in `rest` remain controlled inputs; only the already
realized prefix receives policy propensity. -/
noncomputable def policyHistoryBranch (pi : CausalPolicy A O)
    (hpi : IsCausalPolicy pi) (p : CausalBehavior A O)
    (h : CausalHistory A O) : CausalSubbehavior A O where
  mass := fun rest => causalPolicyProb pi h * p.mass (h ++ rest)
  nonneg := fun rest => mul_nonneg
    (causalPolicyProb_nonneg_of_valid pi hpi h) (p.nonneg (h ++ rest))
  consistent := by
    intro rest a
    rw [<- Finset.mul_sum]
    simpa only [List.append_assoc] using
      congrArg (fun r : Real => causalPolicyProb pi h * r)
        (p.consistent (h ++ rest) a)

@[simp]
theorem policyHistoryBranch_mass (pi : CausalPolicy A O)
    (hpi : IsCausalPolicy pi) (p : CausalBehavior A O)
    (h rest : CausalHistory A O) :
    (policyHistoryBranch pi hpi p h).mass rest =
      causalPolicyProb pi h * p.mass (h ++ rest) :=
  rfl

@[simp]
theorem policyHistoryBranch_root (pi : CausalPolicy A O)
    (hpi : IsCausalPolicy pi) (p : CausalBehavior A O)
    (h : CausalHistory A O) :
    (policyHistoryBranch pi hpi p h).mass [] =
      causalBehaviorTraceProb pi p h := by
  simp [policyHistoryBranch, causalBehaviorTraceProb]

/-- The canonical exact-horizon policy instrument.  Its signal is the full
length-`n` history, and its branch is the policy weight of that history times
the world's Hankel subbehavior at the same history. -/
noncomputable def policyHistoryInstrument [Nonempty O]
    (pi : CausalPolicy A O) (hpi : IsCausalPolicy pi)
    (ps : Theta -> CausalBehavior A O) (n : Nat) :
    ContinuationInstrument Theta (CausalFiniteTrace A O n) A O where
  branch := fun theta w =>
    policyHistoryBranch pi hpi (ps theta) (List.ofFn w)
  root_sum := by
    intro theta
    simpa only [policyHistoryBranch_root, causalBehaviorFiniteExperiment] using
      (causalBehaviorFiniteExperiment_valid pi hpi ps n theta).2

@[simp]
theorem policyHistoryInstrument_branch_mass [Nonempty O]
    (pi : CausalPolicy A O) (hpi : IsCausalPolicy pi)
    (ps : Theta -> CausalBehavior A O) (n : Nat)
    (theta : Theta) (w : CausalFiniteTrace A O n)
    (rest : CausalHistory A O) :
    ((policyHistoryInstrument pi hpi ps n).branch theta w).mass rest =
      causalPolicyProb pi (List.ofFn w) *
        (ps theta).mass (List.ofFn w ++ rest) :=
  rfl

/-- Forgetting continuation coordinates from the canonical policy instrument
recovers exactly the ordinary fixed-horizon acquired experiment. -/
theorem policyHistoryInstrument_rootExperiment [Nonempty O]
    (pi : CausalPolicy A O) (hpi : IsCausalPolicy pi)
    (ps : Theta -> CausalBehavior A O) (n : Nat) :
    (policyHistoryInstrument pi hpi ps n).rootExperiment =
      causalBehaviorFiniteExperiment pi ps n := by
  funext theta w
  exact policyHistoryBranch_root pi hpi (ps theta) (List.ofFn w)

end IdExp
