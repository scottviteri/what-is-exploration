import Formal.WaitProxyStoppingExperiment
import Formal.CausalEpisodicCoverage

/-!
# Recorded causal traces for the hidden wait/proxy class

This module proves that the literal finite action--observation trace generated
by `waitProxyResponse` is Blackwell-equivalent to its canonical first-test
stopping experiment.  The forward map deterministically retains the first-test
depth, coordinate, and bit.  The reverse map conditions a fixed reference-world
trace law on that stopping atom; a cross-likelihood identity proves that this
world-independent decoder reconstructs every world's complete trace law.
-/

namespace IdExp

open Finset Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Canonical first-test summary of a finite recorded trace.  Malformed trace
prefixes are sent to `none`; they have probability zero under
`waitProxyResponse`. -/
def waitProxyTraceSummary :
    (n : ℕ) →
      CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n →
        WaitProxyStoppingSignal A n
  | 0, _ => none
  | n + 1, w =>
      match w 0 with
      | (WaitProxyAction.wait, WaitProxyObservation.silent) =>
          match waitProxyTraceSummary n (fun i => w i.succ) with
          | none => none
          | some (s, a, b) => some (s.succ, a, b)
      | (WaitProxyAction.test a, WaitProxyObservation.bit b) =>
          some (0, a, b)
      | _ => none

/-- The deterministic first-test summary as a stochastic rule. -/
def waitProxyTraceSummaryRule (n : ℕ) :
    CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n →
      WaitProxyStoppingSignal A n → ℝ :=
  finiteMapRule (waitProxyTraceSummary n)

omit [DecidableEq A] [Nonempty A] in
theorem waitProxyTraceSummaryRule_mem (n : ℕ) :
    waitProxyTraceSummaryRule (A := A) n ∈
      stochasticRules
        (CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n)
        (WaitProxyStoppingSignal A n) :=
  finiteMapRule_mem _

/-- The canonical prefix consisting of `s` silent waits and one test result. -/
def waitProxyTestPrefix (s : ℕ) (a : A) (b : Bool) :
    CausalHistory (WaitProxyAction A) WaitProxyObservation :=
  waitProxySilentHistory s ++
    [(WaitProxyAction.test a, WaitProxyObservation.bit b)]

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem waitProxyLiftSummary_eq_some_iff {n : ℕ}
    (x : Option (Fin n × A × Bool)) (s : Fin n) (a : A) (b : Bool) :
    (match x with
      | none => none
      | some (r, c, d) => some (r.succ, c, d)) = some (s.succ, a, b) ↔
      x = some (s, a, b) := by
  cases x with
  | none => simp
  | some z =>
      rcases z with ⟨r, c, d⟩
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hrs, hca, hdb⟩
        exact ⟨(Fin.succ_injective n) hrs, hca, hdb⟩
      · rintro ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, rfl⟩

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem waitProxyTraceSummary_eq_some_iff {n : ℕ}
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n)
    (s : Fin n) (a : A) (b : Bool) :
    waitProxyTraceSummary n w = some (s, a, b) ↔
      (∀ r : Fin s.val,
        w (Fin.castLT r (lt_trans r.isLt s.isLt)) =
          (WaitProxyAction.wait, WaitProxyObservation.silent)) ∧
      w s = (WaitProxyAction.test a, WaitProxyObservation.bit b) := by
  induction n generalizing a b with
  | zero => exact Fin.elim0 s
  | succ n ih =>
      refine Fin.cases ?_ (fun s' => ?_) s
      · simp only [waitProxyTraceSummary]
        cases hw : w 0 with
        | mk act obs =>
          cases act with
          | wait =>
              cases obs with
              | silent =>
                  cases htail : waitProxyTraceSummary n (fun i => w i.succ) <;>
                    simp [htail, hw]
              | bit x => simp [hw]
          | test x => cases obs <;> simp [hw]
      · simp only [waitProxyTraceSummary]
        cases hw : w 0 with
        | mk act obs =>
          cases act with
          | wait =>
              cases obs with
              | silent =>
                  simp only [hw]
                  refine (waitProxyLiftSummary_eq_some_iff
                    (waitProxyTraceSummary n (fun i => w i.succ)) s' a b).trans ?_
                  rw [ih (fun i => w i.succ) s']
                  constructor
                  · rintro ⟨hbefore, hat⟩
                    constructor
                    · intro r
                      refine Fin.cases ?_ (fun q => ?_) r
                      · exact (congrArg w (Fin.ext rfl)).trans hw
                      · exact hbefore q
                    · exact hat
                  · rintro ⟨hbefore, hat⟩
                    constructor
                    · intro r
                      exact hbefore r.succ
                    · exact hat
              | bit x =>
                  constructor
                  · simp
                  · rintro ⟨hbefore, _⟩
                    let r0 : Fin s'.succ.val := ⟨0, Nat.succ_pos _⟩
                    have hzero := hbefore r0
                    have hi : Fin.castLT r0
                        (lt_trans r0.isLt s'.succ.isLt) = (0 : Fin (n + 1)) :=
                      Fin.ext rfl
                    rw [hi, hw] at hzero
                    cases hzero
          | test x =>
              cases obs with
              | silent =>
                  constructor
                  · simp
                  · rintro ⟨hbefore, _⟩
                    let r0 : Fin s'.succ.val := ⟨0, Nat.succ_pos _⟩
                    have hzero := hbefore r0
                    have hi : Fin.castLT r0
                        (lt_trans r0.isLt s'.succ.isLt) = (0 : Fin (n + 1)) :=
                      Fin.ext rfl
                    rw [hi, hw] at hzero
                    cases hzero
              | bit y =>
                  constructor
                  · intro h
                    have hval := congrArg
                      (fun z : WaitProxyStoppingSignal A (n + 1) =>
                        Option.map (fun q => q.1.val) z) h
                    simp at hval
                  · rintro ⟨hbefore, _⟩
                    let r0 : Fin s'.succ.val := ⟨0, Nat.succ_pos _⟩
                    have hzero := hbefore r0
                    have hi : Fin.castLT r0
                        (lt_trans r0.isLt s'.succ.isLt) = (0 : Fin (n + 1)) :=
                      Fin.ext rfl
                    rw [hi, hw] at hzero
                    cases hzero

/-- The probability of all fixed-length continuations of a prefix is its
prefix probability. -/
theorem sum_causalTraceProb_append_ofFn
    {Act Obs : Type*} [Fintype Act] [Fintype Obs]
    (π : CausalPolicy Act Obs) (hπ : IsCausalPolicy π)
    (Q : CausalResponse Act Obs) (hQ : IsCausalResponse Q)
    (pre : CausalHistory Act Obs) (k : ℕ) :
    ∑ rest : CausalFiniteTrace Act Obs k,
      causalTraceProb π Q (pre ++ List.ofFn rest) =
        causalTraceProb π Q pre := by
  simp_rw [causalTraceProb_append]
  rw [← Finset.mul_sum, sum_causalTraceProbFrom π hπ Q hQ pre k, mul_one]

/-- Splitting a finite trace into its first `m` entries and remaining `k`
entries. -/
def causalTraceAppendEquiv (X : Type*) (m k : ℕ) :
    ((Fin m → X) × (Fin k → X)) ≃ (Fin (m + k) → X) where
  toFun p := Fin.append p.1 p.2
  invFun w :=
    (fun i => w (Fin.castAdd k i), fun j => w (Fin.natAdd m j))
  left_inv p := by
    rcases p with ⟨u, v⟩
    apply Prod.ext
    · funext i
      exact Fin.append_left u v i
    · funext j
      exact Fin.append_right u v j
  right_inv w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ j
    · exact Fin.append_right _ _ j

/-- Exact probability of a finite prefix cylinder, expressed entirely in the
finite matrix calculus. -/
theorem sum_causalTraceProb_prefix_indicator
    {Act Obs : Type*} [Fintype Act] [Fintype Obs]
    [DecidableEq Act] [DecidableEq Obs]
    (π : CausalPolicy Act Obs) (hπ : IsCausalPolicy π)
    (Q : CausalResponse Act Obs) (hQ : IsCausalResponse Q)
    (u : CausalFiniteTrace Act Obs m) (k : ℕ) :
    ∑ w : CausalFiniteTrace Act Obs (m + k),
      causalTraceProb π Q (List.ofFn w) *
        (if (fun i => w (Fin.castAdd k i)) = u then 1 else 0) =
      causalTraceProb π Q (List.ofFn u) := by
  classical
  rw [← (causalTraceAppendEquiv (Act × Obs) m k).sum_comp]
  rw [Fintype.sum_prod_type]
  have hequiv (p : (Fin m → Act × Obs) × (Fin k → Act × Obs)) :
      causalTraceAppendEquiv (Act × Obs) m k p = Fin.append p.1 p.2 := rfl
  simp_rw [hequiv]
  simp only [Fin.append_left]
  rw [Finset.sum_eq_single u]
  · simp only [if_true, mul_one, List.ofFn_fin_append]
    exact sum_causalTraceProb_append_ofFn π hπ Q hQ (List.ofFn u) k
  · intro v _ hv
    simp [hv]
  · simp

/-- The canonical length-`s+1` trace prefix ending in the first test. -/
def waitProxyTestPrefixTrace (s : ℕ) (a : A) (b : Bool) :
    CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation (s + 1) :=
  Fin.snoc (fun _ => (WaitProxyAction.wait, WaitProxyObservation.silent))
    (WaitProxyAction.test a, WaitProxyObservation.bit b)

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem waitProxyTestPrefixTrace_castSucc
    (s : ℕ) (a : A) (b : Bool) (r : Fin s) :
    waitProxyTestPrefixTrace s a b r.castSucc =
      (WaitProxyAction.wait, WaitProxyObservation.silent) := by
  simp [waitProxyTestPrefixTrace]

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem waitProxyTestPrefixTrace_last
    (s : ℕ) (a : A) (b : Bool) :
    waitProxyTestPrefixTrace s a b (Fin.last s) =
      (WaitProxyAction.test a, WaitProxyObservation.bit b) := by
  simp [waitProxyTestPrefixTrace]

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem list_ofFn_waitProxyTestPrefixTrace (s : ℕ) (a : A) (b : Bool) :
    List.ofFn (waitProxyTestPrefixTrace s a b) =
      waitProxyTestPrefix s a b := by
  rw [List.ofFn_succ_last]
  simp [waitProxyTestPrefixTrace, waitProxyTestPrefix,
    waitProxySilentHistory, List.ofFn_const]

omit [Fintype A] [DecidableEq A] [Nonempty A] in
/-- A stopping atom is exactly the cylinder determined by its canonical
silent-wait/test prefix. -/
theorem waitProxyTraceSummary_eq_some_iff_prefix
    (s k : ℕ) (a : A) (b : Bool)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation
      ((s + 1) + k)) :
    waitProxyTraceSummary ((s + 1) + k) w =
        some (Fin.castAdd k (Fin.last s), a, b) ↔
      (fun i => w (Fin.castAdd k i)) = waitProxyTestPrefixTrace s a b := by
  rw [waitProxyTraceSummary_eq_some_iff]
  constructor
  · rintro ⟨hbefore, hat⟩
    funext i
    refine Fin.lastCases ?_ (fun r => ?_) i
    · simpa using hat
    · have hi : Fin.castLT r
          (lt_trans r.isLt (Fin.castAdd k (Fin.last s)).isLt) =
          Fin.castAdd k r.castSucc := Fin.ext rfl
      rw [← hi]
      simpa using hbefore r
  · intro hpref
    constructor
    · intro r
      have hi : Fin.castLT r
          (lt_trans r.isLt (Fin.castAdd k (Fin.last s)).isLt) =
          Fin.castAdd k r.castSucc := Fin.ext rfl
      rw [hi]
      have h := congrFun hpref r.castSucc
      simpa using h
    · have h := congrFun hpref (Fin.last s)
      simpa using h

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem waitProxyHasTest_silentHistory (s : ℕ) :
    waitProxyHasTest (waitProxySilentHistory (A := A) s) = false := by
  simp [waitProxyHasTest, waitProxySilentHistory]

@[simp] theorem waitProxyWaitCount_silentHistory (s : ℕ) :
    waitProxyWaitCount (waitProxySilentHistory (A := A) s) = s := by
  induction s with
  | zero => simp [waitProxyWaitCount, waitProxySilentHistory]
  | succ s ih =>
      rw [waitProxySilentHistory_succ]
      unfold waitProxyWaitCount at ih ⊢
      simp [ih]

@[simp] theorem waitProxyResponseProb_silentHistory
    (c : ℕ → ℝ) (theta : A → Bool) (s : ℕ) :
    causalResponseProb (waitProxyResponse c theta)
      (waitProxySilentHistory s) = 1 := by
  induction s with
  | zero => simp [causalResponseProb, causalResponseProbFrom,
      waitProxySilentHistory]
  | succ s ih =>
      rw [waitProxySilentHistory_succ,
        causalResponseProb_append_singleton, ih]
      simp [waitProxyResponse]

/-- Exact likelihood of the canonical first-test prefix. -/
theorem causalTraceProb_waitProxyTestPrefix
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (theta : A → Bool) (s : ℕ) (a : A) (b : Bool) :
    causalTraceProb π (waitProxyResponse c theta)
        (waitProxyTestPrefix s a b) =
      waitProxyFirstTestMass π s a *
        (if b = theta a then 1 / 2 + c s else 1 / 2 - c s) := by
  rw [waitProxyTestPrefix, causalTraceProb_append_singleton,
    causalTraceProb_factor]
  rw [waitProxyResponseProb_silentHistory]
  simp [waitProxyFirstTestMass, waitProxySurvival, waitProxyResponse]

/-- Every nonempty stopping atom has exactly the probability prescribed by
the canonical stopping experiment when it is obtained from the literal
recorded causal trace. -/
theorem finiteDecisionLaw_waitProxyTraceSummaryRule_some
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (s k : ℕ) (a : A) (b : Bool) (theta : A → Bool) :
    finiteDecisionLaw
        (causalFiniteExperiment π (waitProxyResponse c) ((s + 1) + k))
        (waitProxyTraceSummaryRule ((s + 1) + k)) theta
        (some (Fin.castAdd k (Fin.last s), a, b)) =
      waitProxyStoppingExperiment π c ((s + 1) + k) theta
        (some (Fin.castAdd k (Fin.last s), a, b)) := by
  classical
  unfold finiteDecisionLaw waitProxyTraceSummaryRule finiteMapRule
  have hsummary (w : CausalFiniteTrace (WaitProxyAction A)
      WaitProxyObservation ((s + 1) + k)) :
      (some (Fin.castAdd k (Fin.last s), a, b) =
          waitProxyTraceSummary ((s + 1) + k) w) ↔
        (fun i => w (Fin.castAdd k i)) = waitProxyTestPrefixTrace s a b := by
    rw [eq_comm, waitProxyTraceSummary_eq_some_iff_prefix]
  simp_rw [hsummary]
  unfold causalFiniteExperiment
  rw [sum_causalTraceProb_prefix_indicator π hπ
    (waitProxyResponse c theta) (waitProxyResponse_valid c hc0 hchalf theta)
    (waitProxyTestPrefixTrace s a b) k]
  rw [list_ofFn_waitProxyTestPrefixTrace,
    causalTraceProb_waitProxyTestPrefix]
  rfl

/-- Transport a stopping-atom identity along an equality of finite horizons,
including the dependent signal index. -/
theorem waitProxyStoppingAtom_transport
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) {m n : ℕ} (hmn : m = n) (s : Fin m)
    (a : A) (b : Bool) (theta : A → Bool)
    (h : finiteDecisionLaw
        (causalFiniteExperiment π (waitProxyResponse c) m)
        (waitProxyTraceSummaryRule m) theta (some (s, a, b)) =
      waitProxyStoppingExperiment π c m theta (some (s, a, b))) :
    finiteDecisionLaw
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTraceSummaryRule n) theta
        (some (Fin.cast hmn s, a, b)) =
      waitProxyStoppingExperiment π c n theta
        (some (Fin.cast hmn s, a, b)) := by
  subst n
  simpa

/-- The nonempty-atom identity at an arbitrary horizon/index. -/
theorem finiteDecisionLaw_waitProxyTraceSummaryRule_some'
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) (s : Fin n) (a : A) (b : Bool) (theta : A → Bool) :
    finiteDecisionLaw
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTraceSummaryRule n) theta (some (s, a, b)) =
      waitProxyStoppingExperiment π c n theta (some (s, a, b)) := by
  let k := n - (s.val + 1)
  have hsle : s.val + 1 ≤ n := Nat.succ_le_of_lt s.isLt
  have hn : (s.val + 1) + k = n := Nat.add_sub_of_le hsle
  have h := finiteDecisionLaw_waitProxyTraceSummaryRule_some
    π hπ c hc0 hchalf s.val k a b theta
  have hcast := waitProxyStoppingAtom_transport π c hn
    (Fin.castAdd k (Fin.last s.val)) a b theta h
  have hs : Fin.cast hn (Fin.castAdd k (Fin.last s.val)) = s := Fin.ext rfl
  simpa [hs] using hcast

/-- **Literal trace-to-stopping garbling.**  Deterministically retaining the
first test depth, coordinate, and bit sends the actual recorded causal trace
exactly to the canonical stopping experiment. -/
theorem finiteDecisionLaw_waitProxyTraceSummaryRule
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) :
    finiteDecisionLaw
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTraceSummaryRule n) =
      waitProxyStoppingExperiment π c n := by
  funext theta sig
  cases sig with
  | some sab =>
      rcases sab with ⟨s, a, b⟩
      exact finiteDecisionLaw_waitProxyTraceSummaryRule_some'
        π hπ c hc0 hchalf n s a b theta
  | none =>
      have hsource := causalFiniteExperiment_valid π hπ
        (waitProxyResponse c) (waitProxyResponse_valid c hc0 hchalf) n
      have hdecoded := (finiteDecisionLaw_valid _ hsource _
        (waitProxyTraceSummaryRule_mem n) theta).2
      have hstop := (waitProxyStoppingExperiment_valid
        π hπ c hc0 hchalf n theta).2
      rw [Fintype.sum_option] at hdecoded hstop
      have hsome :
          (∑ x : Fin n × A × Bool,
              finiteDecisionLaw
                (causalFiniteExperiment π (waitProxyResponse c) n)
                (waitProxyTraceSummaryRule n) theta (some x)) =
            ∑ x : Fin n × A × Bool,
              waitProxyStoppingExperiment π c n theta (some x) := by
        apply Finset.sum_congr rfl
        rintro ⟨s, a, b⟩ _
        exact finiteDecisionLaw_waitProxyTraceSummaryRule_some'
          π hπ c hc0 hchalf n s a b theta
      linarith

/-- The canonical stopping experiment is an exact deterministic garbling of
an arbitrary policy's literal finite recorded trace. -/
theorem waitProxyStopping_blackwellLE_causalFiniteExperiment
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) :
    FiniteBlackwellLE (waitProxyStoppingExperiment π c n)
      (causalFiniteExperiment π (waitProxyResponse c) n) :=
  ⟨waitProxyTraceSummaryRule n, waitProxyTraceSummaryRule_mem n,
    finiteDecisionLaw_waitProxyTraceSummaryRule π hπ c hc0 hchalf n⟩

/-- The literal trace separates the coordinate-flipped world pair by at
least the finite effective weight already visible in the stopping summary. -/
theorem waitProxyEffectiveWeightFinite_le_causalTrace_pair_tv
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) (a : A) :
    waitProxyEffectiveWeightFinite π c n a ≤
      finiteTV
        (causalFiniteExperiment π (waitProxyResponse c) n zeroWorld)
        (causalFiniteExperiment π (waitProxyResponse c) n (flipWorld a)) := by
  rw [← waitProxyStopping_pair_tv π hπ c hc0 hchalf n a]
  rw [← finiteDecisionLaw_waitProxyTraceSummaryRule
    π hπ c hc0 hchalf n]
  exact finiteTV_decisionLaw_le
    (causalFiniteExperiment π (waitProxyResponse c) n)
    (waitProxyTraceSummaryRule n) (waitProxyTraceSummaryRule_mem n)
    zeroWorld (flipWorld a)

/-- The exact stopping-profile value is a certified upper bound for the
literal causal trace's deficiency to every noisy coordinate target. -/
theorem causalFiniteExperiment_waitProxy_deficiency_le
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) {targetStrength : ℝ}
    (ht0 : 0 ≤ targetStrength) (hthalf : targetStrength ≤ 1 / 2)
    (a : A) :
    finiteDeficiency
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTarget targetStrength a) ≤
      max (targetStrength -
        waitProxyEffectiveWeightFinite π c n a / 2) 0 := by
  calc
    finiteDeficiency
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTarget targetStrength a) ≤
      finiteDeficiency (waitProxyStoppingExperiment π c n)
        (waitProxyTarget targetStrength a) :=
      finiteDeficiency_mono_source_of_blackwellLE_arbitrary
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyStoppingExperiment π c n)
        (waitProxyTarget targetStrength a)
        (waitProxyStoppingExperiment_valid π hπ c hc0 hchalf n)
        (waitProxyTarget_valid ht0 hthalf a)
        (waitProxyStopping_blackwellLE_causalFiniteExperiment
          π hπ c hc0 hchalf n)
    _ = max (targetStrength -
        waitProxyEffectiveWeightFinite π c n a / 2) 0 :=
      waitProxyStopping_deficiency π hπ c hc0 hchalf n ht0 hthalf a

/-- A reference world for each stopping atom.  On a nonempty atom it
matches the recorded bit at every coordinate, so its BSC factor is strictly
positive. -/
def waitProxyStoppingReferenceWorld {n : ℕ}
    (sig : WaitProxyStoppingSignal A n) : A → Bool :=
  match sig with
  | none => zeroWorld
  | some (_s, _a, b) => fun _ => b

/-- The unique well-formed trace with no test through horizon `n`. -/
def waitProxyAllWaitTrace (n : ℕ) :
    CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n :=
  fun _ => (WaitProxyAction.wait, WaitProxyObservation.silent)

/-- Once a first test has occurred, the wait/proxy response is independent of
which world generated the trace. -/
theorem waitProxyResponse_eq_of_hasTest
    (c : ℕ → ℝ) (theta eta : A → Bool)
    (pre : CausalHistory (WaitProxyAction A) WaitProxyObservation)
    (hpre : waitProxyHasTest pre = true) (act : WaitProxyAction A)
    (o : WaitProxyObservation) :
    waitProxyResponse c theta pre act o =
      waitProxyResponse c eta pre act o := by
  simp [waitProxyResponse, hpre]

omit [Fintype A] [Nonempty A] in
theorem waitProxyHasTest_append_singleton_of_true
    (pre : CausalHistory (WaitProxyAction A) WaitProxyObservation)
    (ao : WaitProxyAction A × WaitProxyObservation)
    (hpre : waitProxyHasTest pre = true) :
    waitProxyHasTest (pre ++ [ao]) = true := by
  unfold waitProxyHasTest at hpre ⊢
  rw [List.any_append, hpre]
  rfl

/-- Conditional trace laws after the first test are world-independent. -/
theorem causalTraceProbFrom_waitProxy_eq_of_hasTest
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (theta eta : A → Bool)
    (pre rest : CausalHistory (WaitProxyAction A) WaitProxyObservation)
    (hpre : waitProxyHasTest pre = true) :
    causalTraceProbFrom π (waitProxyResponse c theta) pre rest =
      causalTraceProbFrom π (waitProxyResponse c eta) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
      simp only [causalTraceProbFrom]
      rw [waitProxyResponse_eq_of_hasTest c theta eta pre hpre]
      rw [ih (pre ++ [ao])
        (waitProxyHasTest_append_singleton_of_true pre ao hpre)]

omit [Fintype A] [Nonempty A] in
@[simp] theorem waitProxyHasTest_testPrefix
    (s : ℕ) (a : A) (b : Bool) :
    waitProxyHasTest (waitProxyTestPrefix s a b) = true := by
  simp [waitProxyTestPrefix, waitProxyHasTest, List.any_append]

/-- If a trace summary is `none`, then its controlled response likelihood is
world-independent.  Malformed no-summary traces have zero likelihood in every
world; the all-wait trace has likelihood one in every world. -/
theorem causalResponseProbFrom_waitProxy_eq_of_summary_none
    (c : ℕ → ℝ) (theta eta : A → Bool)
    (pre : CausalHistory (WaitProxyAction A) WaitProxyObservation)
    (hpre : waitProxyHasTest pre = false)
    {n : ℕ}
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n)
    (hsum : waitProxyTraceSummary n w = none) :
    causalResponseProbFrom (waitProxyResponse c theta) pre (List.ofFn w) =
      causalResponseProbFrom (waitProxyResponse c eta) pre (List.ofFn w) := by
  induction n generalizing pre with
  | zero => simp [causalResponseProbFrom]
  | succ n ih =>
      rw [List.ofFn_succ]
      cases hw : w 0 with
      | mk act obs =>
        cases act with
        | wait =>
            cases obs with
            | silent =>
                simp only [waitProxyTraceSummary, hw] at hsum
                have htail : waitProxyTraceSummary n (fun i => w i.succ) = none := by
                  cases h : waitProxyTraceSummary n (fun i => w i.succ) <;>
                    simp [h] at hsum ⊢
                simp only [causalResponseProbFrom]
                rw [show waitProxyResponse c theta pre WaitProxyAction.wait
                    WaitProxyObservation.silent = 1 by
                  simp [waitProxyResponse, hpre]]
                rw [show waitProxyResponse c eta pre WaitProxyAction.wait
                    WaitProxyObservation.silent = 1 by
                  simp [waitProxyResponse, hpre]]
                simp only [one_mul]
                apply ih (pre ++ [(WaitProxyAction.wait,
                  WaitProxyObservation.silent)])
                · unfold waitProxyHasTest at hpre ⊢
                  rw [List.any_append, hpre]
                  rfl
                · exact htail
            | bit x =>
                simp [causalResponseProbFrom, waitProxyResponse, hpre]
        | test a =>
            cases obs with
            | silent =>
                simp [causalResponseProbFrom, waitProxyResponse, hpre]
            | bit b =>
                simp [waitProxyTraceSummary, hw] at hsum

/-- On a nonempty summary fiber, changing the world only changes the common
prefix BSC factor; the conditional tail law is identical. -/
theorem causalTraceProb_waitProxy_cross_of_summary_some
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (theta eta : A → Bool)
    (s k : ℕ) (a : A) (b : Bool)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation
      ((s + 1) + k))
    (hsum : waitProxyTraceSummary ((s + 1) + k) w =
      some (Fin.castAdd k (Fin.last s), a, b)) :
    causalTraceProb π (waitProxyResponse c theta) (List.ofFn w) *
        waitProxyStoppingExperiment π c ((s + 1) + k) eta
          (some (Fin.castAdd k (Fin.last s), a, b)) =
      causalTraceProb π (waitProxyResponse c eta) (List.ofFn w) *
        waitProxyStoppingExperiment π c ((s + 1) + k) theta
          (some (Fin.castAdd k (Fin.last s), a, b)) := by
  have hpref := (waitProxyTraceSummary_eq_some_iff_prefix s k a b w).mp hsum
  let e := causalTraceAppendEquiv
    (WaitProxyAction A × WaitProxyObservation) (s + 1) k
  let v := (e.symm w).2
  have hinv : e.symm w = (waitProxyTestPrefixTrace s a b, v) := by
    apply Prod.ext
    · simpa [e, causalTraceAppendEquiv] using hpref
    · rfl
  have hw : w = Fin.append (waitProxyTestPrefixTrace s a b) v := by
    have happ := e.apply_symm_apply w
    rw [hinv] at happ
    exact happ.symm
  rw [hw]
  simp only [List.ofFn_fin_append]
  rw [causalTraceProb_append, causalTraceProb_append]
  rw [list_ofFn_waitProxyTestPrefixTrace]
  rw [causalTraceProb_waitProxyTestPrefix,
    causalTraceProb_waitProxyTestPrefix]
  have htail := causalTraceProbFrom_waitProxy_eq_of_hasTest
    π c theta eta (waitProxyTestPrefix s a b) (List.ofFn v)
    (waitProxyHasTest_testPrefix s a b)
  simp only [waitProxyStoppingExperiment]
  have hval : (Fin.castAdd k (Fin.last s)).val = s := rfl
  rw [hval, htail]
  ring

omit [Fintype A] [DecidableEq A] [Nonempty A] in
/-- The recursive trace summary commutes with transport of its finite horizon. -/
theorem waitProxyTraceSummary_cast {m n : ℕ} (hmn : m = n)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation m) :
    waitProxyTraceSummary n
        (Equiv.cast (congrArg (fun q => Fin q →
          WaitProxyAction A × WaitProxyObservation) hmn) w) =
      Option.map (fun x => (Fin.cast hmn x.1, x.2.1, x.2.2))
        (waitProxyTraceSummary m w) := by
  cases hmn
  simp [Equiv.cast]

/-- Transport the cross-likelihood identity together with its dependent trace
and stopping index. -/
theorem waitProxyCrossIdentity_transport
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (theta eta : A → Bool)
    {m n : ℕ} (hmn : m = n) (s : Fin m) (a : A) (b : Bool)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation m)
    (h : causalFiniteExperiment π (waitProxyResponse c) m theta w *
        waitProxyStoppingExperiment π c m eta (some (s, a, b)) =
      causalFiniteExperiment π (waitProxyResponse c) m eta w *
        waitProxyStoppingExperiment π c m theta (some (s, a, b))) :
    causalFiniteExperiment π (waitProxyResponse c) n theta
        (Equiv.cast (congrArg (fun q => Fin q →
          WaitProxyAction A × WaitProxyObservation) hmn) w) *
      waitProxyStoppingExperiment π c n eta
        (some (Fin.cast hmn s, a, b)) =
    causalFiniteExperiment π (waitProxyResponse c) n eta
        (Equiv.cast (congrArg (fun q => Fin q →
          WaitProxyAction A × WaitProxyObservation) hmn) w) *
      waitProxyStoppingExperiment π c n theta
        (some (Fin.cast hmn s, a, b)) := by
  subst n
  simpa

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem waitProxyTraceCast_symm {m n : ℕ} (hmn : m = n)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n) :
    Equiv.cast (congrArg (fun q => Fin q →
        WaitProxyAction A × WaitProxyObservation) hmn)
      (Equiv.cast (congrArg (fun q => Fin q →
        WaitProxyAction A × WaitProxyObservation) hmn.symm) w) = w := by
  cases hmn
  simp [Equiv.cast]

/-- Arbitrary-horizon form of the nonempty-fiber cross-likelihood identity. -/
theorem causalTraceProb_waitProxy_cross_of_summary_some'
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (theta eta : A → Bool)
    (n : ℕ) (s : Fin n) (a : A) (b : Bool)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n)
    (hsum : waitProxyTraceSummary n w = some (s, a, b)) :
    causalFiniteExperiment π (waitProxyResponse c) n theta w *
        waitProxyStoppingExperiment π c n eta (some (s, a, b)) =
      causalFiniteExperiment π (waitProxyResponse c) n eta w *
        waitProxyStoppingExperiment π c n theta (some (s, a, b)) := by
  let k := n - (s.val + 1)
  have hsle : s.val + 1 ≤ n := Nat.succ_le_of_lt s.isLt
  have hn : (s.val + 1) + k = n := Nat.add_sub_of_le hsle
  let idx : Fin ((s.val + 1) + k) := Fin.castAdd k (Fin.last s.val)
  let w0 : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation
      ((s.val + 1) + k) := Equiv.cast
        (congrArg (fun q => Fin q →
          WaitProxyAction A × WaitProxyObservation) hn.symm) w
  have hidx : Fin.cast hn idx = s := Fin.ext rfl
  have htransport := waitProxyTraceSummary_cast hn.symm w
  have hsum0 : waitProxyTraceSummary ((s.val + 1) + k) w0 =
      some (idx, a, b) := by
    rw [htransport, hsum]
    have hcast : Fin.cast hn.symm s = idx := Fin.ext rfl
    simp [hcast]
  have h := causalTraceProb_waitProxy_cross_of_summary_some
    π c theta eta s.val k a b w0 hsum0
  have ht := waitProxyCrossIdentity_transport π c theta eta hn idx a b w0 h
  have hw : Equiv.cast
      (congrArg (fun q => Fin q →
        WaitProxyAction A × WaitProxyObservation) hn) w0 = w := by
    exact waitProxyTraceCast_symm hn w
  simpa [hidx, hw] using ht

/-- On the `none` summary fiber, the literal finite trace law is independent
of the world. -/
theorem causalFiniteExperiment_waitProxy_eq_of_summary_none
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (theta eta : A → Bool) (n : ℕ)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n)
    (hsum : waitProxyTraceSummary n w = none) :
    causalFiniteExperiment π (waitProxyResponse c) n theta w =
      causalFiniteExperiment π (waitProxyResponse c) n eta w := by
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor, causalTraceProb_factor]
  apply congrArg (causalPolicyProb π (List.ofFn w) * ·)
  exact causalResponseProbFrom_waitProxy_eq_of_summary_none
    c theta eta [] rfl w hsum

/-- A zero-probability stopping atom in its matching reference world is zero
in every world. -/
theorem waitProxyStopping_zero_of_reference_zero
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r) (n : ℕ)
    (sig : WaitProxyStoppingSignal A n)
    (href : waitProxyStoppingExperiment π c n
      (waitProxyStoppingReferenceWorld sig) sig = 0)
    (theta : A → Bool) :
    waitProxyStoppingExperiment π c n theta sig = 0 := by
  cases sig with
  | none => simpa [waitProxyStoppingExperiment] using href
  | some sab =>
      rcases sab with ⟨s, a, b⟩
      simp only [waitProxyStoppingExperiment,
        waitProxyStoppingReferenceWorld] at href ⊢
      have hpos : 0 < (1 / 2 : ℝ) + c s.val := by linarith [hc0 s.val]
      have hmass : waitProxyFirstTestMass π s.val a = 0 := by
        rcases mul_eq_zero.mp href with h | h
        · exact h
        · exfalso
          simpa using hpos.ne' h
      simp [hmass]

/-- Reverse decoder: condition a matching reference-world trace row on the
given stopping atom.  Zero-mass atoms may use an arbitrary Dirac row because
they have zero probability in every world. -/
def waitProxyStoppingToTraceRule
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (n : ℕ) :
    WaitProxyStoppingSignal A n →
      CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n → ℝ := by
  classical
  exact fun sig w =>
    let eta := waitProxyStoppingReferenceWorld sig
    let z := waitProxyStoppingExperiment π c n eta sig
    if z = 0 then
      if w = waitProxyAllWaitTrace n then 1 else 0
    else if waitProxyTraceSummary n w = sig then
      causalFiniteExperiment π (waitProxyResponse c) n eta w / z
    else 0

/-- The conditional reverse decoder is row-stochastic. -/
theorem waitProxyStoppingToTraceRule_mem
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) :
    waitProxyStoppingToTraceRule π c n ∈
      stochasticRules (WaitProxyStoppingSignal A n)
        (CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n) := by
  classical
  intro sig _
  let eta := waitProxyStoppingReferenceWorld sig
  let z := waitProxyStoppingExperiment π c n eta sig
  have hE := causalFiniteExperiment_valid π hπ
    (waitProxyResponse c) (waitProxyResponse_valid c hc0 hchalf) n
  have hS := waitProxyStoppingExperiment_valid π hπ c hc0 hchalf n
  constructor
  · intro w
    unfold waitProxyStoppingToTraceRule
    simp only
    split_ifs with hz hw hsum
    · norm_num
    · norm_num
    · exact div_nonneg ((hE eta).1 w) (le_of_lt
        (lt_of_le_of_ne ((hS eta).1 sig) (Ne.symm hz)))
    · norm_num
  · change ∑ w : CausalFiniteTrace (WaitProxyAction A)
        WaitProxyObservation n,
      (if z = 0 then
        if w = waitProxyAllWaitTrace n then 1 else 0
      else if waitProxyTraceSummary n w = sig then
        causalFiniteExperiment π (waitProxyResponse c) n eta w / z
      else 0) = 1
    by_cases hz : z = 0
    · simp [hz]
    · simp only [hz, if_false]
      have hpush := congrFun (congrFun
        (finiteDecisionLaw_waitProxyTraceSummaryRule
          π hπ c hc0 hchalf n) eta) sig
      unfold finiteDecisionLaw waitProxyTraceSummaryRule finiteMapRule at hpush
      have hsum :
          ∑ w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n,
            (if waitProxyTraceSummary n w = sig then
              causalFiniteExperiment π (waitProxyResponse c) n eta w / z
            else 0) = 1 := by
        have heq :
            (∑ w, if waitProxyTraceSummary n w = sig then
                causalFiniteExperiment π (waitProxyResponse c) n eta w else 0) = z := by
          change _ = waitProxyStoppingExperiment π c n eta sig
          rw [← hpush]
          apply Finset.sum_congr rfl
          intro w _
          by_cases h : waitProxyTraceSummary n w = sig
          · simp [h, eq_comm]
          · simp [h, Ne.symm h]
        calc
          _ = ∑ w, (if waitProxyTraceSummary n w = sig then
                causalFiniteExperiment π (waitProxyResponse c) n eta w else 0) / z := by
              apply Finset.sum_congr rfl
              intro w _
              by_cases h : waitProxyTraceSummary n w = sig <;> simp [h]
          _ = (∑ w, if waitProxyTraceSummary n w = sig then
                causalFiniteExperiment π (waitProxyResponse c) n eta w else 0) / z := by
              rw [Finset.sum_div]
          _ = 1 := by rw [heq, div_self hz]
      simpa using hsum

/-- A trace in a zero-probability stopping fiber itself has zero probability.
This isolates the only subtlety in conditioning on the canonical statistic. -/
theorem causalFiniteExperiment_waitProxy_eq_zero_of_summary_stopping_eq_zero
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) (theta : A → Bool)
    (sig : WaitProxyStoppingSignal A n)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n)
    (hsum : waitProxyTraceSummary n w = sig)
    (hzero : waitProxyStoppingExperiment π c n theta sig = 0) :
    causalFiniteExperiment π (waitProxyResponse c) n theta w = 0 := by
  classical
  have hE := causalFiniteExperiment_valid π hπ
    (waitProxyResponse c) (waitProxyResponse_valid c hc0 hchalf) n
  have hpush := congrFun (congrFun
    (finiteDecisionLaw_waitProxyTraceSummaryRule
      π hπ c hc0 hchalf n) theta) sig
  unfold finiteDecisionLaw at hpush
  let f := fun x : CausalFiniteTrace (WaitProxyAction A)
      WaitProxyObservation n =>
    causalFiniteExperiment π (waitProxyResponse c) n theta x *
      waitProxyTraceSummaryRule n x sig
  have hRule := waitProxyTraceSummaryRule_mem (A := A) n
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x
    exact mul_nonneg ((hE theta).1 x)
      ((hRule x (Set.mem_univ x)).1 sig)
  have hle : f w ≤ ∑ x, f x :=
    Finset.single_le_sum (fun x _ => hf0 x) (Finset.mem_univ w)
  have hfw : f w =
      causalFiniteExperiment π (waitProxyResponse c) n theta w := by
    simp [f, waitProxyTraceSummaryRule, finiteMapRule, hsum]
  have hsum0 : (∑ x, f x) = 0 := by
    change (∑ x,
      causalFiniteExperiment π (waitProxyResponse c) n theta x *
        waitProxyTraceSummaryRule n x sig) = 0
    exact hpush.trans hzero
  rw [hfw, hsum0] at hle
  exact le_antisymm hle ((hE theta).1 w)

/-- The matching stopping atom, followed by the conditional reverse decoder,
reproduces the probability of every literal trace in that atom's fiber. -/
theorem waitProxyStopping_mul_waitProxyStoppingToTraceRule_of_summary
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) (theta : A → Bool)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n) :
    waitProxyStoppingExperiment π c n theta (waitProxyTraceSummary n w) *
        waitProxyStoppingToTraceRule π c n (waitProxyTraceSummary n w) w =
      causalFiniteExperiment π (waitProxyResponse c) n theta w := by
  classical
  let sig := waitProxyTraceSummary n w
  let eta := waitProxyStoppingReferenceWorld sig
  let z := waitProxyStoppingExperiment π c n eta sig
  have hsum : waitProxyTraceSummary n w = sig := rfl
  unfold waitProxyStoppingToTraceRule
  change waitProxyStoppingExperiment π c n theta sig *
    (if z = 0 then
      if w = waitProxyAllWaitTrace n then 1 else 0
    else if waitProxyTraceSummary n w = sig then
      causalFiniteExperiment π (waitProxyResponse c) n eta w / z
    else 0) =
      causalFiniteExperiment π (waitProxyResponse c) n theta w
  by_cases hz : z = 0
  · have hs0 := waitProxyStopping_zero_of_reference_zero
      π c hc0 n sig hz theta
    have hE0 :=
      causalFiniteExperiment_waitProxy_eq_zero_of_summary_stopping_eq_zero
        π hπ c hc0 hchalf n theta sig w hsum hs0
    simp [hz, hs0, hE0]
  · rw [if_neg hz, if_pos hsum]
    cases hsig : sig with
    | none =>
        have hw := causalFiniteExperiment_waitProxy_eq_of_summary_none
          π c theta eta n w (hsum.trans hsig)
        have hs :
            waitProxyStoppingExperiment π c n theta sig = z := by
          simp [z, eta, hsig, waitProxyStoppingExperiment]
        have hsnone :
            waitProxyStoppingExperiment π c n theta none = z := by
          simpa [hsig] using hs
        rw [hsnone, hw]
        exact mul_div_cancel₀ _ hz
    | some sab =>
        rcases sab with ⟨s, a, b⟩
        have hsum' : waitProxyTraceSummary n w = some (s, a, b) := by
          simpa [hsig] using hsum
        have hcross := causalTraceProb_waitProxy_cross_of_summary_some'
          π c theta eta n s a b w hsum'
        have hz' :
            waitProxyStoppingExperiment π c n eta (some (s, a, b)) ≠ 0 := by
          simpa [z, hsig] using hz
        have hzEq :
            z = waitProxyStoppingExperiment π c n eta (some (s, a, b)) := by
          simp [z, hsig]
        rw [hzEq, ← mul_div_assoc]
        apply (div_eq_iff hz').2
        nlinarith [hcross]

/-- A nonmatching stopping atom contributes zero to the decoded probability
of a fixed trace. -/
theorem waitProxyStopping_mul_waitProxyStoppingToTraceRule_of_ne
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (n : ℕ) (theta : A → Bool)
    (sig : WaitProxyStoppingSignal A n)
    (w : CausalFiniteTrace (WaitProxyAction A) WaitProxyObservation n)
    (hne : sig ≠ waitProxyTraceSummary n w) :
    waitProxyStoppingExperiment π c n theta sig *
        waitProxyStoppingToTraceRule π c n sig w = 0 := by
  classical
  let eta := waitProxyStoppingReferenceWorld sig
  let z := waitProxyStoppingExperiment π c n eta sig
  unfold waitProxyStoppingToTraceRule
  change waitProxyStoppingExperiment π c n theta sig *
    (if z = 0 then
      if w = waitProxyAllWaitTrace n then 1 else 0
    else if waitProxyTraceSummary n w = sig then
      causalFiniteExperiment π (waitProxyResponse c) n eta w / z
    else 0) = 0
  by_cases hz : z = 0
  · have hs0 := waitProxyStopping_zero_of_reference_zero
      π c hc0 n sig hz theta
    simp [hz, hs0]
  · have hne' : waitProxyTraceSummary n w ≠ sig := Ne.symm hne
    simp [hz, hne']

/-- The conditional decoder reconstructs the complete finite recorded trace
law, not merely the canonical stopping statistic. -/
theorem finiteDecisionLaw_waitProxyStoppingToTraceRule
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) :
    finiteDecisionLaw (waitProxyStoppingExperiment π c n)
        (waitProxyStoppingToTraceRule π c n) =
      causalFiniteExperiment π (waitProxyResponse c) n := by
  classical
  funext theta w
  unfold finiteDecisionLaw
  rw [Finset.sum_eq_single (waitProxyTraceSummary n w)]
  · exact waitProxyStopping_mul_waitProxyStoppingToTraceRule_of_summary
      π hπ c hc0 hchalf n theta w
  · intro sig _ hne
    exact waitProxyStopping_mul_waitProxyStoppingToTraceRule_of_ne
      π c hc0 n theta sig w hne
  · simp


/-- The complete literal finite trace is an exact garbling of the canonical
stopping experiment.  The decoder uses only the stopping atom and the fixed
policy, never the unknown world. -/
theorem causalFiniteExperiment_blackwellLE_waitProxyStopping
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) :
    FiniteBlackwellLE
      (causalFiniteExperiment π (waitProxyResponse c) n)
      (waitProxyStoppingExperiment π c n) :=
  ⟨waitProxyStoppingToTraceRule π c n,
    waitProxyStoppingToTraceRule_mem π hπ c hc0 hchalf n,
    finiteDecisionLaw_waitProxyStoppingToTraceRule
      π hπ c hc0 hchalf n⟩

/-- At every finite horizon, the canonical first-test stopping experiment and
the actual action--observation trace are Blackwell-equivalent. -/
theorem waitProxyStopping_causalFiniteExperiment_blackwellEquiv
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) :
    FiniteBlackwellLE (waitProxyStoppingExperiment π c n)
        (causalFiniteExperiment π (waitProxyResponse c) n) ∧
      FiniteBlackwellLE
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyStoppingExperiment π c n) :=
  ⟨waitProxyStopping_blackwellLE_causalFiniteExperiment
      π hπ c hc0 hchalf n,
    causalFiniteExperiment_blackwellLE_waitProxyStopping
      π hπ c hc0 hchalf n⟩

/-- The literal finite causal trace has exactly the canonical stopping
experiment's pairwise total variation for a coordinate flip. -/
theorem causalFiniteExperiment_waitProxy_pair_tv
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) (a : A) :
    finiteTV
        (causalFiniteExperiment π (waitProxyResponse c) n zeroWorld)
        (causalFiniteExperiment π (waitProxyResponse c) n (flipWorld a)) =
      waitProxyEffectiveWeightFinite π c n a := by
  apply le_antisymm
  · rw [← waitProxyStopping_pair_tv π hπ c hc0 hchalf n a]
    rw [← finiteDecisionLaw_waitProxyStoppingToTraceRule
      π hπ c hc0 hchalf n]
    exact finiteTV_decisionLaw_le
      (waitProxyStoppingExperiment π c n)
      (waitProxyStoppingToTraceRule π c n)
      (waitProxyStoppingToTraceRule_mem π hπ c hc0 hchalf n)
      zeroWorld (flipWorld a)
  · exact waitProxyEffectiveWeightFinite_le_causalTrace_pair_tv
      π hπ c hc0 hchalf n a

/-- **Exact literal causal coordinate deficiency.**  Replacing the canonical
stopping signal by the entire recorded trace changes no decision problem, so
the optimized noisy-coordinate deficiency has exactly the same formula. -/
theorem causalFiniteExperiment_waitProxy_deficiency
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    (n : ℕ) {targetStrength : ℝ}
    (ht0 : 0 ≤ targetStrength) (hthalf : targetStrength ≤ 1 / 2)
    (a : A) :
    finiteDeficiency
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTarget targetStrength a) =
      max (targetStrength -
        waitProxyEffectiveWeightFinite π c n a / 2) 0 := by
  rw [finiteDeficiency_eq_of_source_blackwellEquiv
    (causalFiniteExperiment π (waitProxyResponse c) n)
    (waitProxyStoppingExperiment π c n)
    (waitProxyTarget targetStrength a)
    (causalFiniteExperiment_blackwellLE_waitProxyStopping
      π hπ c hc0 hchalf n)
    (waitProxyStopping_blackwellLE_causalFiniteExperiment
      π hπ c hc0 hchalf n)]
  exact waitProxyStopping_deficiency
    π hπ c hc0 hchalf n ht0 hthalf a

/-- Literal finite-trace coordinate deficiencies converge to the checked
infinite effective-weight profile. -/
theorem tendsto_causalFiniteExperiment_waitProxy_deficiency
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ r, 0 ≤ c r) (hchalf : ∀ r, c r ≤ 1 / 2)
    {targetStrength : ℝ}
    (ht0 : 0 ≤ targetStrength) (hthalf : targetStrength ≤ 1 / 2)
    (a : A) :
    Filter.Tendsto
      (fun n => finiteDeficiency
        (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTarget targetStrength a))
      Filter.atTop
      (𝓝 (max (targetStrength -
        waitProxyEffectiveWeight π c a / 2) 0)) := by
  refine (tendsto_waitProxyStopping_deficiency
    π hπ c hc0 hchalf ht0 hthalf a).congr' ?_
  exact Filter.Eventually.of_forall fun n => by
    change finiteDeficiency (waitProxyStoppingExperiment π c n)
        (waitProxyTarget targetStrength a) =
      finiteDeficiency (causalFiniteExperiment π (waitProxyResponse c) n)
        (waitProxyTarget targetStrength a)
    rw [causalFiniteExperiment_waitProxy_deficiency
      π hπ c hc0 hchalf n ht0 hthalf a,
      waitProxyStopping_deficiency
        π hπ c hc0 hchalf n ht0 hthalf a]

end

end IdExp
