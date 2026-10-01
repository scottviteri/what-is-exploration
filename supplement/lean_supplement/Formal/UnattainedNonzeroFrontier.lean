import Formal.CausalKernel
import Formal.CausalUniversality
import Formal.ThreeDoorValues
import Formal.Unrestricted

/-!
# The hidden wait/proxy example: checked core

This module begins the missing Lean support for paper Proposition
`prop:unattained-nonzero`.  It keeps three logically different claims separate.

* `waitProxyResponse` is the actual finite-interface causal response law: waiting is
  silent, a first test of coordinate `a` returns a noisy copy of the world bit
  `θ a`, and every later response is silent.
* `waitProxyLimit_deficiency` computes the literal decoder-infimum deficiency
  from the limiting experiment which reveals one randomly selected coordinate
  exactly to a noisy coordinate test.
* `waitProxyProfile_*` proves the algebra responsible for the nonzero antichain
  and for strict improvement whenever the effective coordinate budget is below
  one.

The module now also reduces every arbitrary valid policy to its
world-independent first-test stopping masses, proves that the resulting
infinite effective vector is a strict subprobability, and realizes every
strict vector by a one-shot causal policy.  `WaitProxyCausalTrace.lean`
supplies the signal-level Blackwell equivalence between recorded traces and
the stopping experiment. `WaitProxyCausalProfile.lean` completes the literal
causal assembly: native-plan classification, exact profile coordinates, raw
range, closure, Pareto frontier, nonzero frontier, and policy nonattainment.
-/

namespace IdExp

open Filter Finset Set Topology

noncomputable section

/-! ## A finite causal class -/

/-- One silent wait action and one irreversible test action per coordinate. -/
inductive WaitProxyAction (A : Type*)
  | wait
  | test (a : A)
deriving DecidableEq, Fintype

/-- The silent symbol or a returned proxy bit. -/
inductive WaitProxyObservation
  | silent
  | bit (b : Bool)
deriving DecidableEq, Fintype

instance : Nonempty WaitProxyObservation := ⟨WaitProxyObservation.silent⟩

theorem sum_waitProxyObservation (f : WaitProxyObservation → ℝ) :
    ∑ o, f o = f WaitProxyObservation.silent +
      f (WaitProxyObservation.bit false) + f (WaitProxyObservation.bit true) := by
  have huniv : (Finset.univ : Finset WaitProxyObservation) =
      {WaitProxyObservation.silent, WaitProxyObservation.bit false,
        WaitProxyObservation.bit true} := by
    ext o
    cases o with
    | silent => simp
    | bit b => cases b <;> simp
  rw [huniv]
  simp
  ring

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Whether an irreversible test has already occurred in a history. -/
def waitProxyHasTest
    (h : CausalHistory (WaitProxyAction A) WaitProxyObservation) : Bool :=
  h.any fun ao => match ao.1 with
    | WaitProxyAction.wait => false
    | WaitProxyAction.test _ => true

/-- The number of silent waits in a history.  Before the first test every
realizable past action is a wait, so this is the proxy-repair depth. -/
def waitProxyWaitCount
    (h : CausalHistory (WaitProxyAction A) WaitProxyObservation) : ℕ :=
  h.countP fun ao => ao.1 = WaitProxyAction.wait

/-- A causal response law whose first test after `s` waits has binary strength
`c s`.  Taking `c s = (1-(1-λ)^s)/2` gives the paper's latent repair model after
integrating out its hidden proxy bits. -/
def waitProxyResponse (c : ℕ → ℝ) (θ : A → Bool) :
    CausalResponse (WaitProxyAction A) WaitProxyObservation :=
  fun h act o =>
    if waitProxyHasTest h then
      if o = WaitProxyObservation.silent then 1 else 0
    else
      match act with
      | WaitProxyAction.wait =>
          if o = WaitProxyObservation.silent then 1 else 0
      | WaitProxyAction.test a =>
          match o with
          | WaitProxyObservation.silent => 0
          | WaitProxyObservation.bit b =>
              if b = θ a then 1 / 2 + c (waitProxyWaitCount h)
              else 1 / 2 - c (waitProxyWaitCount h)

/-- The integrated hidden-proxy response is a valid causal kernel whenever
each binary strength lies in `[0,1/2]`. -/
theorem waitProxyResponse_valid (c : ℕ → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hchalf : ∀ s, c s ≤ 1 / 2) (θ : A → Bool) :
    IsCausalResponse (waitProxyResponse c θ) := by
  intro h act
  constructor
  · intro o
    by_cases ht : waitProxyHasTest h
    · by_cases ho : o = WaitProxyObservation.silent <;>
        simp [waitProxyResponse, ht, ho]
    · cases act with
      | wait =>
          by_cases ho : o = WaitProxyObservation.silent <;>
            simp [waitProxyResponse, ht, ho]
      | test a =>
          cases o with
          | silent => simp [waitProxyResponse, ht]
          | bit b =>
              by_cases hb : b = θ a <;>
                simp [waitProxyResponse, ht, hb] <;>
                linarith [hc0 (waitProxyWaitCount h), hchalf (waitProxyWaitCount h)]
  · unfold waitProxyResponse
    by_cases ht : waitProxyHasTest h
    · simp [ht]
    · simp only [ht, if_false]
      cases act with
      | wait => simp
      | test a =>
          rw [sum_waitProxyObservation]
          cases hθ : θ a <;> simp [hθ] <;> ring

/-- The paper's geometric repair strength after `s` waits. -/
def waitProxyStrength (lam : ℝ) (s : ℕ) : ℝ :=
  (1 - (1 - lam) ^ s) / 2

theorem waitProxyStrength_nonneg {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (s : ℕ) :
    0 ≤ waitProxyStrength lam s := by
  unfold waitProxyStrength
  have hq0 : 0 ≤ 1 - lam := by linarith
  have hq1 : 1 - lam ≤ 1 := by linarith
  have hp := pow_le_one₀ hq0 hq1 (n := s)
  linarith

theorem waitProxyStrength_le_half {lam : ℝ} (hlam1 : lam ≤ 1) (s : ℕ) :
    waitProxyStrength lam s ≤ 1 / 2 := by
  unfold waitProxyStrength
  have hp : 0 ≤ (1 - lam) ^ s := pow_nonneg (by linarith) s
  linarith

theorem waitProxyStrength_lt_half {lam : ℝ} (hlam1 : lam < 1) (s : ℕ) :
    waitProxyStrength lam s < 1 / 2 := by
  unfold waitProxyStrength
  have hp : 0 < (1 - lam) ^ s := pow_pos (by linarith) s
  linarith

/-- Geometric repair strengths converge upward to perfect binary strength. -/
theorem waitProxyStrength_tendsto_half {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    Filter.Tendsto (waitProxyStrength lam) Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  have hpow : Filter.Tendsto (fun s : ℕ => (1 - lam) ^ s) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) :=
    tendsto_const_nhds
  have h := (hone.sub hpow).div_const (2 : ℝ)
  change Filter.Tendsto (fun s : ℕ => (1 - (1 - lam) ^ s) / 2)
    Filter.atTop (𝓝 (1 / 2 : ℝ))
  simpa only [sub_zero] using h

theorem waitProxyStrength_cofinal {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    ∀ x < (1 / 2 : ℝ), ∃ s, x < waitProxyStrength lam s := by
  intro x hx
  have hev := (tendsto_order.1 (waitProxyStrength_tendsto_half hlam0 hlam1)).1 x hx
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨N, hN N le_rfl⟩

/-! ## Exact deficiency of the limiting coordinate experiment -/

/-- The limiting experiment: draw and record `b ∼ v`, then reveal `θ b`
exactly. -/
abbrev waitProxyLimitExperiment (v : A → ℝ) :
    FiniteExperiment (A → Bool) (A × Bool) :=
  rootAcquired v

/-- The native noisy test of coordinate `a` with binary strength `c`. -/
def waitProxyTarget (c : ℝ) (a : A) :
    FiniteExperiment (A → Bool) Bool :=
  fun θ o => if o = θ a then 1 / 2 + c else 1 / 2 - c

theorem waitProxyTarget_valid {c : ℝ} (hc0 : 0 ≤ c) (hchalf : c ≤ 1 / 2)
    (a : A) : IsFiniteExperiment (waitProxyTarget c a) := by
  intro θ
  constructor
  · intro o
    unfold waitProxyTarget
    split_ifs <;> linarith
  · cases h : θ a <;> simp [waitProxyTarget, h] <;> ring

/-- On the selected branch, emit a BSC of strength `d`; on every other
branch emit a fair bit. -/
def waitProxyLimitDecoder (a : A) (d : ℝ) :
    (A × Bool) → Bool → ℝ :=
  fun bo o =>
    if bo.1 = a then
      if o = bo.2 then 1 / 2 + d else 1 / 2 - d
    else 1 / 2

theorem waitProxyLimitDecoder_valid (a : A) {d : ℝ}
    (hd0 : 0 ≤ d) (hdhalf : d ≤ 1 / 2) :
    waitProxyLimitDecoder a d ∈ stochasticRules (A × Bool) Bool := by
  intro bo _
  constructor
  · intro o
    unfold waitProxyLimitDecoder
    split_ifs <;> linarith
  · by_cases hba : bo.1 = a
    · cases hb : bo.2 <;> simp [waitProxyLimitDecoder, hba, hb] <;> ring
    · simp [waitProxyLimitDecoder, hba]

/-- The decoder produces a binary experiment of strength `v a * d`. -/
theorem waitProxyLimitDecoder_law (v : A → ℝ) (hv : IsDist v)
    (a : A) (d : ℝ) (θ : A → Bool) (o : Bool) :
    finiteDecisionLaw (waitProxyLimitExperiment v)
        (waitProxyLimitDecoder a d) θ o =
      if o = θ a then 1 / 2 + v a * d else 1 / 2 - v a * d := by
  unfold finiteDecisionLaw waitProxyLimitExperiment rootAcquired
  rw [Fintype.sum_prod_type]
  have hrow (b : A) :
      ∑ x : Bool, (if x = θ b then v b else 0) *
          waitProxyLimitDecoder a d (b, x) o =
        if b = a then
          v b * (if o = θ a then 1 / 2 + d else 1 / 2 - d)
        else v b / 2 := by
    by_cases hba : b = a
    · subst b
      cases hθ : θ a <;> cases ho : o <;>
        simp [waitProxyLimitDecoder, hθ, ho]
    · cases hθ : θ b <;>
        simp [waitProxyLimitDecoder, hba, hθ] <;> ring
  simp_rw [hrow]
  rw [Finset.sum_ite]
  simp only [Finset.filter_eq', Finset.sum_filter, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hsumother : ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), v b = 1 - v a := by
    have hfilter : Finset.univ.filter (fun b => b ≠ a) = Finset.univ.erase a := by
      ext b
      simp [and_comm]
    rw [hfilter]
    have heq := Finset.sum_erase_add (s := (Finset.univ : Finset A)) v
      (Finset.mem_univ a)
    rw [hv.2] at heq
    linarith
  have hsumother_div :
      ∑ b, (if ¬b = a then v b / 2 else 0) = (1 - v a) / 2 := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_div, hsumother]
  by_cases hoa : o = θ a
  · simp only [hoa, if_true]
    simp only [Finset.sum_singleton]
    rw [hsumother_div]
    ring
  · simp only [hoa, if_false]
    simp only [Finset.sum_singleton]
    rw [hsumother_div]
    ring

/-- The explicit decoder's worst-world error is the absolute strength gap. -/
theorem waitProxyLimitDecoder_error (v : A → ℝ) (hv : IsDist v)
    (a : A) (c d : ℝ) (θ : A → Bool) :
    decodeErr (waitProxyLimitExperiment v) (waitProxyTarget c a)
      (waitProxyLimitDecoder a d) θ = |c - v a * d| := by
  change (1 / 2 : ℝ) * ∑ o : Bool,
    |finiteDecisionLaw (waitProxyLimitExperiment v)
        (waitProxyLimitDecoder a d) θ o - waitProxyTarget c a θ o| = _
  rw [Fintype.sum_bool]
  simp only [waitProxyLimitDecoder_law v hv a d]
  cases hθ : θ a <;> simp [waitProxyTarget, hθ] <;>
    rw [abs_sub_comm (v a * d) c] <;>
    ring

/-- A pair differing only at coordinate `a` has target separation `2c`. -/
theorem waitProxyTarget_pair_tv {c : ℝ} (hc0 : 0 ≤ c) (a : A) :
    finiteTV (waitProxyTarget c a zeroWorld)
      (waitProxyTarget c a (flipWorld a)) = 2 * c := by
  unfold finiteTV waitProxyTarget zeroWorld flipWorld
  rw [Fintype.sum_bool]
  simp
  ring_nf
  rw [abs_neg, abs_of_nonneg (mul_nonneg hc0 (by norm_num))]
  ring

/-- There is an admissible branch-decoder strength whose residual gap is
exactly the positive part of `c-v/2`. -/
theorem exists_waitProxy_decoder_strength {w c : ℝ}
    (hw0 : 0 ≤ w) (hc0 : 0 ≤ c) (hchalf : c ≤ 1 / 2) :
    ∃ d, 0 ≤ d ∧ d ≤ 1 / 2 ∧ |c - w * d| = max (c - w / 2) 0 := by
  by_cases hcw : c ≤ w / 2
  · by_cases hw : w = 0
    · subst w
      have hc : c = 0 := by linarith
      subst c
      exact ⟨0, by norm_num, by norm_num, by norm_num⟩
    · refine ⟨c / w, div_nonneg hc0 hw0, ?_, ?_⟩
      · exact (div_le_iff₀ (lt_of_le_of_ne hw0 (Ne.symm hw))).2 (by linarith)
      · rw [mul_div_cancel₀ c hw]
        simp [max_eq_right (sub_nonpos.2 hcw)]
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    rw [max_eq_left (a := c - w / 2) (b := 0) (by linarith)]
    have : 0 ≤ c - w * (1 / 2) := by linarith
    rw [abs_of_nonneg this]
    ring

/-- **Exact limiting-profile coordinate.**  The optimized Le Cam deficiency
from `I_v` to a noisy coordinate test is
`max (c - v a / 2) 0`.  This is the paper's displayed formula, proved from
one decoder and one world-pair certificate. -/
theorem waitProxyLimit_deficiency (v : A → ℝ) (hv : IsDist v)
    {c : ℝ} (hc0 : 0 ≤ c) (hchalf : c ≤ 1 / 2) (a : A) :
    finiteDeficiency (waitProxyLimitExperiment v) (waitProxyTarget c a) =
      max (c - v a / 2) 0 := by
  obtain ⟨d, hd0, hdhalf, hd⟩ :=
    exists_waitProxy_decoder_strength (hv.1 a) hc0 hchalf
  apply le_antisymm
  · exact finiteDeficiency_le_of_decoder _ _ (waitProxyLimitDecoder a d)
      (waitProxyLimitDecoder_valid a hd0 hdhalf) _
      (fun θ => (waitProxyLimitDecoder_error v hv a c d θ).trans hd |>.le)
  · apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
      (rootAcquired_valid v hv) (waitProxyTarget_valid hc0 hchalf a))
    rintro q ⟨G, hG, herr⟩
    have hpair := finiteTV_pairwise_decoder_lower
      (waitProxyLimitExperiment v) (waitProxyTarget c a) G hG
      zeroWorld (flipWorld a) q (herr zeroWorld) (herr (flipWorld a))
    rw [waitProxyTarget_pair_tv hc0 a, rootAcquired_pair_tv v hv a] at hpair
    have hq0 : 0 ≤ q :=
      (decodeErr_nonneg (waitProxyLimitExperiment v) (waitProxyTarget c a) G zeroWorld).trans
        (herr zeroWorld)
    rcases le_total (v a / 2) c with hvc | hcv
    · rw [max_eq_left (sub_nonneg.2 hvc)]
      linarith
    · rw [max_eq_right (sub_nonpos.2 hcv)]
      exact hq0

/-! ## The profile antichain and raw strict improvement -/

abbrev WaitProxyCoordinate (A : Type*) := ℕ × A

/-- The exact profile formula, now viewed independently of the decoder LP. -/
def waitProxyProfile (c : ℕ → ℝ) (z : A → ℝ) :
    WaitProxyCoordinate A → ℝ :=
  fun sa => max (c sa.1 - z sa.2 / 2) 0

theorem continuous_waitProxyProfile (c : ℕ → ℝ) :
    Continuous (waitProxyProfile c : (A → ℝ) → WaitProxyCoordinate A → ℝ) := by
  apply continuous_pi
  rintro ⟨s, a⟩
  unfold waitProxyProfile
  fun_prop

/-- Larger effective coordinate weights weakly improve every deficiency. -/
theorem waitProxyProfile_antitone (c : ℕ → ℝ) {z u : A → ℝ}
    (hzu : ∀ a, z a ≤ u a) :
    ∀ j, waitProxyProfile c u j ≤ waitProxyProfile c z j := by
  rintro ⟨s, a⟩
  unfold waitProxyProfile
  exact max_le_max_right 0 (by linarith [hzu a])

/-- If the strengths approach one half from below, profile dominance recovers
coordinatewise dominance of the effective weights. -/
theorem weight_le_of_waitProxyProfile_le (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    {u v : A → ℝ} (hu0 : ∀ a, 0 ≤ u a) (hv1 : ∀ a, v a ≤ 1)
    (hprof : ∀ j, waitProxyProfile c u j ≤ waitProxyProfile c v j) :
    ∀ a, v a ≤ u a := by
  intro a
  by_contra hnot
  have huv : u a < v a := lt_of_not_ge hnot
  have huhalf : u a / 2 < (1 / 2 : ℝ) := by linarith [hv1 a]
  obtain ⟨s, hs⟩ := hcofinal (u a / 2) huhalf
  have hleft : max (c s - u a / 2) 0 = c s - u a / 2 :=
    max_eq_left (by linarith)
  have hp := hprof (s, a)
  unfold waitProxyProfile at hp
  rw [hleft] at hp
  by_cases hright : 0 ≤ c s - v a / 2
  · rw [max_eq_left hright] at hp
    linarith
  · rw [max_eq_right (le_of_not_ge hright)] at hp
    linarith

/-- Probability weights therefore give an antichain of limiting profiles. -/
theorem waitProxyProfile_probability_antichain (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    {u v : A → ℝ} (hu : IsDist u) (hv : IsDist v)
    (hprof : ∀ j, waitProxyProfile c u j ≤ waitProxyProfile c v j) :
    u = v := by
  have hvleu : ∀ a, v a ≤ u a :=
    weight_le_of_waitProxyProfile_le c hcofinal hu.1 (fun a => by
      rw [← hv.2]
      exact Finset.single_le_sum (fun b _ => hv.1 b) (Finset.mem_univ a)) hprof
  apply funext
  have hall := (Finset.sum_eq_sum_iff_of_le
    (s := (Finset.univ : Finset A)) (fun a _ => hvleu a)).mp
      (by rw [hv.2, hu.2])
  exact fun a => (hall a (Finset.mem_univ a)).symm

/-- The probability-simplex parametrization has no duplicate profiles. -/
theorem waitProxyProfile_injectiveOn_probability (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s) :
    Set.InjOn (waitProxyProfile c)
      {v : A → ℝ | IsDist v} := by
  intro u hu v hv heq
  exact waitProxyProfile_probability_antichain c hcofinal hu hv
    (fun j => by rw [heq])

/-- A profile is nonzero as soon as one coordinate weight is strictly below
one; a sufficiently deep noisy target witnesses it. -/
theorem waitProxyProfile_ne_zero_of_lt_one (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (v : A → ℝ) {a : A} (ha : v a < 1) :
    waitProxyProfile c v ≠ 0 := by
  intro hzero
  obtain ⟨s, hs⟩ := hcofinal (v a / 2) (by linarith)
  have h := congrFun hzero (s, a)
  unfold waitProxyProfile at h
  rw [max_eq_left (by linarith)] at h
  simp at h
  linarith

/-- An effective subprobability weight vector.  Strict total mass below one
is the exact algebraic trace of finite waiting: every tested component has
strength strictly below perfect revelation, and never-testing mass contributes
zero. -/
def IsStrictSubprobability (z : A → ℝ) : Prop :=
  (∀ a, 0 ≤ z a) ∧ ∑ a, z a < 1

/-- The closed effective-weight region underlying the completed algebraic
profile model. -/
def IsSubprobability (z : A → ℝ) : Prop :=
  (∀ a, 0 ≤ z a) ∧ ∑ a, z a ≤ 1

/-- Every strict subprobability profile has a coordinatewise larger strict
subprobability profile, with a strict deficiency improvement somewhere. -/
theorem exists_strictly_improving_waitProxyProfile (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (z : A → ℝ) (hz : IsStrictSubprobability z) :
    ∃ u, IsStrictSubprobability u ∧
      (∀ j, waitProxyProfile c u j ≤ waitProxyProfile c z j) ∧
      (∃ j, waitProxyProfile c u j < waitProxyProfile c z j) := by
  let a0 : A := Classical.choice inferInstance
  let d : ℝ := (1 - ∑ a, z a) / 2
  let u : A → ℝ := fun a => if a = a0 then z a + d else z a
  have hd : 0 < d := by unfold d; linarith [hz.2]
  have hu0 : ∀ a, 0 ≤ u a := by
    intro a
    simp only [u]
    split_ifs <;> linarith [hz.1 a]
  have hsumu : ∑ a, u a = (∑ a, z a) + d := by
    calc
      ∑ a, u a = ∑ a, (z a + if a = a0 then d else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a = a0 <;> simp [u, ha]
      _ = (∑ a, z a) + ∑ a, (if a = a0 then d else 0) :=
        Finset.sum_add_distrib
      _ = (∑ a, z a) + d := by
        rw [Finset.sum_ite_eq' Finset.univ a0]
        simp
  have husub : IsStrictSubprobability u := by
    refine ⟨hu0, ?_⟩
    rw [hsumu]
    unfold d
    linarith [hz.2]
  have hzu : ∀ a, z a ≤ u a := by
    intro a
    simp only [u]
    split_ifs <;> linarith
  have hua0lt : u a0 < 1 := by
    have hsingle : u a0 ≤ ∑ a, u a :=
      Finset.single_le_sum (fun a _ => hu0 a) (Finset.mem_univ a0)
    exact hsingle.trans_lt husub.2
  obtain ⟨s, hs⟩ := hcofinal (u a0 / 2) (by linarith)
  refine ⟨u, husub, waitProxyProfile_antitone c hzu, ⟨(s, a0), ?_⟩⟩
  unfold waitProxyProfile
  rw [max_eq_left (by linarith)]
  have hza : z a0 < u a0 := by simp [u, hd]
  have hzpos : 0 ≤ c s - z a0 / 2 := by linarith
  rw [max_eq_left hzpos]
  linarith

/-- Every subprobability vector can spend its remaining mass on one
coordinate, producing a probability vector and weakly improving the whole
profile. -/
theorem exists_probability_dominating_waitProxyProfile (c : ℕ → ℝ)
    (z : A → ℝ) (hz : IsSubprobability z) :
    ∃ u, IsDist u ∧ ∀ j, waitProxyProfile c u j ≤ waitProxyProfile c z j := by
  let a0 : A := Classical.choice inferInstance
  let d : ℝ := 1 - ∑ a, z a
  let u : A → ℝ := fun a => if a = a0 then z a + d else z a
  have hd : 0 ≤ d := by unfold d; linarith [hz.2]
  have hu0 : ∀ a, 0 ≤ u a := by
    intro a
    simp only [u]
    split_ifs <;> linarith [hz.1 a]
  have hsumu : ∑ a, u a = (∑ a, z a) + d := by
    calc
      ∑ a, u a = ∑ a, (z a + if a = a0 then d else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a = a0 <;> simp [u, ha]
      _ = (∑ a, z a) + ∑ a, (if a = a0 then d else 0) :=
        Finset.sum_add_distrib
      _ = (∑ a, z a) + d := by
        rw [Finset.sum_ite_eq' Finset.univ a0]
        simp
  have hu : IsDist u := by
    refine ⟨hu0, ?_⟩
    rw [hsumu]
    unfold d
    ring
  have hzu : ∀ a, z a ≤ u a := by
    intro a
    simp only [u]
    split_ifs <;> linarith
  exact ⟨u, hu, waitProxyProfile_antitone c hzu⟩

/-- The explicitly completed algebraic profile set: profiles indexed by
closed subprobability weights. -/
def waitProxyCompletedProfiles (c : ℕ → ℝ) :
    Set (WaitProxyCoordinate A → ℝ) :=
  {p | ∃ z, IsSubprobability z ∧ p = waitProxyProfile c z}

/-- The corresponding raw algebraic set, before completing the strict
effective-weight budget. -/
def waitProxyRawProfiles (c : ℕ → ℝ) :
    Set (WaitProxyCoordinate A → ℝ) :=
  {p | ∃ z, IsStrictSubprobability z ∧ p = waitProxyProfile c z}

/-- Shrink a closed subprobability vector by a factor tending to one. -/
def shrinkWaitProxyWeight (n : ℕ) (z : A → ℝ) : A → ℝ :=
  fun a => (1 - 1 / ((n : ℝ) + 1)) * z a

theorem shrinkWaitProxyWeight_strict (n : ℕ) (z : A → ℝ)
    (hz : IsSubprobability z) :
    IsStrictSubprobability (shrinkWaitProxyWeight n z) := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hfactor0 : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    linarith
  have hfactor1 : 1 - 1 / ((n : ℝ) + 1) < 1 := by
    have : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hden
    linarith
  constructor
  · intro a
    exact mul_nonneg hfactor0 (hz.1 a)
  · unfold shrinkWaitProxyWeight
    rw [← Finset.mul_sum]
    calc
      (1 - 1 / ((n : ℝ) + 1)) * ∑ a, z a ≤
          (1 - 1 / ((n : ℝ) + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hz.2 hfactor0
      _ < 1 := by simpa using hfactor1

theorem shrinkWaitProxyWeight_tendsto (z : A → ℝ) :
    Filter.Tendsto (fun n => shrinkWaitProxyWeight n z) Filter.atTop (𝓝 z) := by
  rw [tendsto_pi_nhds]
  intro a
  have hrecip : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) :=
    tendsto_const_nhds
  have hfactor := hone.sub hrecip
  simpa [shrinkWaitProxyWeight] using hfactor.mul_const (z a)

theorem shrinkWaitProxyProfile_tendsto (c : ℕ → ℝ) (z : A → ℝ) :
    Filter.Tendsto (fun n => waitProxyProfile c (shrinkWaitProxyWeight n z))
      Filter.atTop (𝓝 (waitProxyProfile c z)) := by
  rw [tendsto_pi_nhds]
  rintro ⟨s, a⟩
  have hz := (tendsto_pi_nhds.1 (shrinkWaitProxyWeight_tendsto z)) a
  have hc : Filter.Tendsto (fun _ : ℕ => c s) Filter.atTop (𝓝 (c s)) :=
    tendsto_const_nhds
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds
  change Filter.Tendsto
    (fun n => max (c s - shrinkWaitProxyWeight n z a / 2) 0)
      Filter.atTop (𝓝 (max (c s - z a / 2) 0))
  exact (hc.sub (hz.div_const 2)).max hzero

/-- Every profile in the explicit closed model is the pointwise limit of a
sequence of strict raw profiles.  This proves the difficult inclusion from
the proposed completion into the actual closure of the algebraic raw set. -/
theorem waitProxyCompletedProfiles_subset_closure_raw (c : ℕ → ℝ) :
    waitProxyCompletedProfiles (A := A) c ⊆
      closure (waitProxyRawProfiles (A := A) c) := by
  intro p hp
  rcases hp with ⟨z, hz, rfl⟩
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => waitProxyProfile c (shrinkWaitProxyWeight n z), ?_,
    shrinkWaitProxyProfile_tendsto c z⟩
  intro n
  exact ⟨shrinkWaitProxyWeight n z, shrinkWaitProxyWeight_strict n z hz, rfl⟩

/-- Compactness of the finite weight cube gives the reverse inclusion: no
other pointwise profile limits are introduced. -/
theorem closure_waitProxyRawProfiles_subset_completed (c : ℕ → ℝ) :
    closure (waitProxyRawProfiles (A := A) c) ⊆
      waitProxyCompletedProfiles (A := A) c := by
  intro p hp
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨pseq, hpraw, hptend⟩ := hp
  choose z hz hzp using hpraw
  have hzle (n : ℕ) (a : A) : z n a ≤ 1 := by
    have hsingle : z n a ≤ ∑ b, z n b :=
      Finset.single_le_sum (fun b _ => (hz n).1 b) (Finset.mem_univ a)
    exact hsingle.trans (hz n).2.le
  let zcube : ℕ → (A → Set.Icc (0 : ℝ) 1) :=
    fun n a => ⟨z n a, (hz n).1 a, hzle n a⟩
  obtain ⟨w, -, phi, hphi, hlim⟩ :=
    isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (zcube n))
  let zlim : A → ℝ := fun a => (w a : ℝ)
  have hzlim : Filter.Tendsto (fun n => z (phi n)) Filter.atTop (𝓝 zlim) := by
    rw [tendsto_pi_nhds]
    intro a
    have hcoord := ((continuous_subtype_val.comp (continuous_apply a)).tendsto w).comp hlim
    simpa [Function.comp_def, zcube, zlim] using hcoord
  have hsumlim : Filter.Tendsto (fun n => ∑ a, z (phi n) a) Filter.atTop
      (𝓝 (∑ a, zlim a)) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset A)
      (fun a _ => (tendsto_pi_nhds.1 hzlim) a)
  have hzlimSub : IsSubprobability zlim := by
    constructor
    · intro a
      exact (w a).property.1
    · exact le_of_tendsto hsumlim
        (Filter.Eventually.of_forall fun n => (hz (phi n)).2.le)
  have hpseqSub : Filter.Tendsto (fun n => pseq (phi n)) Filter.atTop (𝓝 p) :=
    hptend.comp hphi.tendsto_atTop
  have hpseqEq : (fun n => pseq (phi n)) =
      (fun n => waitProxyProfile c (z (phi n))) := by
    funext n
    exact hzp (phi n)
  rw [hpseqEq] at hpseqSub
  have hprofileLim : Filter.Tendsto (fun n => waitProxyProfile c (z (phi n)))
      Filter.atTop (𝓝 (waitProxyProfile c zlim)) :=
    ((continuous_waitProxyProfile c).tendsto zlim).comp hzlim
  have heq : p = waitProxyProfile c zlim :=
    tendsto_nhds_unique hpseqSub hprofileLim
  exact ⟨zlim, hzlimSub, heq⟩

/-- The explicit closed subprobability model is exactly the pointwise closure
of the strict raw algebraic profiles. -/
theorem closure_waitProxyRawProfiles_eq_completed (c : ℕ → ℝ) :
    closure (waitProxyRawProfiles (A := A) c) =
      waitProxyCompletedProfiles (A := A) c := by
  apply Set.Subset.antisymm
  · exact closure_waitProxyRawProfiles_subset_completed c
  · exact waitProxyCompletedProfiles_subset_closure_raw c

/-- Its proposed frontier: profiles indexed by probability weights. -/
def waitProxyFrontierProfiles (c : ℕ → ℝ) :
    Set (WaitProxyCoordinate A → ℝ) :=
  {p | ∃ v, IsDist v ∧ p = waitProxyProfile c v}

/-- Every explicitly completed profile is dominated by a proposed frontier
profile. -/
theorem exists_waitProxyFrontierProfile_le (c : ℕ → ℝ)
    {p : WaitProxyCoordinate A → ℝ} (hp : p ∈ waitProxyCompletedProfiles c) :
    ∃ m ∈ waitProxyFrontierProfiles c, ∀ j, m j ≤ p j := by
  rcases hp with ⟨z, hz, rfl⟩
  obtain ⟨u, hu, hdom⟩ := exists_probability_dominating_waitProxyProfile c z hz
  exact ⟨waitProxyProfile c u, ⟨u, hu, rfl⟩, hdom⟩

/-- Probability profiles are minimal in the completed set.  Combined with
`exists_waitProxyFrontierProfile_le`, this identifies the whole Pareto
frontier of the explicit closed weight model. -/
theorem waitProxyFrontierProfile_minimal (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    {m : WaitProxyCoordinate A → ℝ} (hm : m ∈ waitProxyFrontierProfiles c) :
    m ∈ waitProxyCompletedProfiles c ∧
      ∀ q ∈ waitProxyCompletedProfiles c,
        (∀ j, q j ≤ m j) → ∀ j, m j ≤ q j := by
  rcases hm with ⟨v, hv, rfl⟩
  have hvsub : IsSubprobability v := ⟨hv.1, hv.2.le⟩
  refine ⟨⟨v, hvsub, rfl⟩, ?_⟩
  rintro q ⟨z, hz, rfl⟩ hdom
  have hvlez : ∀ a, v a ≤ z a :=
    weight_le_of_waitProxyProfile_le c hcofinal hz.1 (fun a => by
      rw [← hv.2]
      exact Finset.single_le_sum (fun b _ => hv.1 b) (Finset.mem_univ a)) hdom
  have hsumz : ∑ a, z a = 1 := by
    apply le_antisymm hz.2
    rw [← hv.2]
    exact Finset.sum_le_sum fun a _ => hvlez a
  have hzv : z = v := by
    apply funext
    have hall := (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset A)) (fun a _ => hvlez a)).mp
        (by rw [hsumz, hv.2])
    exact fun a => (hall a (Finset.mem_univ a)).symm
  subst z
  exact fun _ => le_rfl

/-- Conversely every minimal completed profile is a probability profile, so
the proposed family is exactly the Pareto frontier. -/
theorem waitProxy_paretoFrontier_eq (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s) :
    ({m : WaitProxyCoordinate A → ℝ | m ∈ waitProxyCompletedProfiles c ∧
      ∀ q ∈ waitProxyCompletedProfiles c,
        (∀ j, q j ≤ m j) → ∀ j, m j ≤ q j} :
      Set (WaitProxyCoordinate A → ℝ)) =
      waitProxyFrontierProfiles c := by
  ext m
  constructor
  · rintro ⟨hm, hmin⟩
    obtain ⟨f, hf, hfm⟩ := exists_waitProxyFrontierProfile_le c hm
    have hmf := hmin f
      (waitProxyFrontierProfile_minimal c hcofinal hf).1 hfm
    have heq : m = f := funext fun j => le_antisymm (hmf j) (hfm j)
    exact heq ▸ hf
  · intro hm
    exact waitProxyFrontierProfile_minimal c hcofinal hm

/-- On a nontrivial coordinate set, every probability vector leaves some
coordinate weight strictly below one. -/
theorem exists_probability_weight_lt_one [Nontrivial A]
    (v : A → ℝ) (hv : IsDist v) : ∃ a, v a < 1 := by
  by_contra h
  push_neg at h
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have hva_le (x : A) : v x ≤ 1 := by
    rw [← hv.2]
    exact Finset.single_le_sum (fun y _ => hv.1 y) (Finset.mem_univ x)
  have hva : v a = 1 := le_antisymm (hva_le a) (h a)
  have hvb : v b = 1 := le_antisymm (hva_le b) (h b)
  have hpair : v a + v b ≤ ∑ x, v x := by
    rw [← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _)
      (fun x _ _ => hv.1 x)
  rw [hva, hvb, hv.2] at hpair
  norm_num at hpair

/-- Every frontier profile is nonzero when there are at least two
coordinates. -/
theorem waitProxyFrontierProfiles_nonzero [Nontrivial A] (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    {p : WaitProxyCoordinate A → ℝ} (hp : p ∈ waitProxyFrontierProfiles c) :
    p ≠ 0 := by
  rcases hp with ⟨v, hv, rfl⟩
  obtain ⟨a, ha⟩ := exists_probability_weight_lt_one v hv
  exact waitProxyProfile_ne_zero_of_lt_one c hcofinal v ha

/-- No strict-subprobability profile is Pareto-minimal in the explicit
completion.  This is the algebraic no-attainment statement used by the causal
proof once each policy is reduced to its effective strict-subprobability
vector. -/
theorem strictSubprobability_not_pareto (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (z : A → ℝ) (hz : IsStrictSubprobability z) :
    ¬(∀ q ∈ waitProxyCompletedProfiles c,
      (∀ j, q j ≤ waitProxyProfile c z j) →
        ∀ j, waitProxyProfile c z j ≤ q j) := by
  intro hmin
  obtain ⟨u, hu, hdom, j, hj⟩ :=
    exists_strictly_improving_waitProxyProfile c hcofinal z hz
  have huclosed : IsSubprobability u := ⟨hu.1, hu.2.le⟩
  have hback := hmin (waitProxyProfile c u) ⟨u, huclosed, rfl⟩ hdom j
  exact (not_le_of_gt hj) hback

/-! ## Finite-horizon first-test stopping masses

The algebra above is parametrized by an effective subprobability vector.  We
now connect an arbitrary behavioral causal policy to that vector at every
finite horizon.  Before the irreversible test, the only realizable observation
is `silent`, hence the probability of first testing coordinate `a` after `s`
waits is a world-independent policy quantity.  The following identities are
the finite telescoping core of the remaining infinite-horizon wrapper.
-/

/-- The unique realizable length-`s` history on which no test has yet occurred. -/
def waitProxySilentHistory (s : ℕ) :
    CausalHistory (WaitProxyAction A) WaitProxyObservation :=
  List.replicate s (WaitProxyAction.wait, WaitProxyObservation.silent)

/-- Policy probability of surviving for `s` silent waits without testing. -/
noncomputable def waitProxySurvival
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation) (s : ℕ) : ℝ :=
  causalPolicyProb π (waitProxySilentHistory s)

/-- World-independent probability of first testing coordinate `a` immediately
after `s` silent waits. -/
noncomputable def waitProxyFirstTestMass
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (s : ℕ) (a : A) : ℝ :=
  waitProxySurvival π s *
    π (waitProxySilentHistory s) (WaitProxyAction.test a)

@[simp]
theorem waitProxySilentHistory_zero :
    waitProxySilentHistory (A := A) 0 = [] := rfl

theorem waitProxySilentHistory_succ (s : ℕ) :
    waitProxySilentHistory (A := A) (s + 1) =
      waitProxySilentHistory s ++
        [(WaitProxyAction.wait, WaitProxyObservation.silent)] := by
  simpa [waitProxySilentHistory] using
    (List.replicate_add s 1
      (WaitProxyAction.wait, WaitProxyObservation.silent))

@[simp]
theorem waitProxySurvival_zero
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation) :
    waitProxySurvival π 0 = 1 := by
  simp [waitProxySurvival, waitProxySilentHistory, causalPolicyProb,
    causalPolicyProbFrom]

theorem waitProxySurvival_succ
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation) (s : ℕ) :
    waitProxySurvival π (s + 1) =
      waitProxySurvival π s *
        π (waitProxySilentHistory s) WaitProxyAction.wait := by
  rw [waitProxySurvival, waitProxySilentHistory_succ,
    causalPolicyProb_append_singleton]
  rfl

/-- Split a policy row into the wait action and the `A` test actions. -/
theorem sum_waitProxyAction
    (f : WaitProxyAction A → ℝ) :
    ∑ act, f act = f WaitProxyAction.wait + ∑ a, f (WaitProxyAction.test a) := by
  rw [show (Finset.univ : Finset (WaitProxyAction A)) =
      {WaitProxyAction.wait} ∪ Finset.univ.image WaitProxyAction.test by
    ext act
    cases act <;> simp]
  rw [Finset.sum_union]
  · simp
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => WaitProxyAction.test.inj h
  · simp

/-- At each silent prefix, survival mass is partitioned between one more wait
and first-testing one of the coordinates. -/
theorem waitProxySurvival_partition
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (s : ℕ) :
    waitProxySurvival π (s + 1) + ∑ a, waitProxyFirstTestMass π s a =
      waitProxySurvival π s := by
  rw [waitProxySurvival_succ]
  simp only [waitProxyFirstTestMass]
  rw [← Finset.mul_sum]
  rw [← mul_add]
  have hrow := (hπ (waitProxySilentHistory s)).2
  rw [sum_waitProxyAction] at hrow
  rw [hrow, mul_one]

/-- Exact finite telescoping identity: mass that first tests before horizon
`n`, plus mass that has waited throughout, is one. -/
theorem sum_waitProxyFirstTestMass_add_survival
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    (∑ s ∈ Finset.range n, ∑ a, waitProxyFirstTestMass π s a) +
        waitProxySurvival π n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hpart := waitProxySurvival_partition π hπ n
      linarith

theorem waitProxySurvival_nonneg
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (s : ℕ) :
    0 ≤ waitProxySurvival π s := by
  unfold waitProxySurvival causalPolicyProb
  have hnonneg : ∀ (pre rest : CausalHistory (WaitProxyAction A) WaitProxyObservation),
      0 ≤ causalPolicyProbFrom π pre rest := by
    intro pre rest
    induction rest generalizing pre with
    | nil => simp [causalPolicyProbFrom]
    | cons ao rest ih =>
        simp only [causalPolicyProbFrom]
        exact mul_nonneg ((hπ pre).1 ao.1) (ih (pre ++ [ao]))
  exact hnonneg [] (waitProxySilentHistory s)

theorem waitProxyFirstTestMass_nonneg
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (s : ℕ) (a : A) :
    0 ≤ waitProxyFirstTestMass π s a :=
  mul_nonneg (waitProxySurvival_nonneg π hπ s)
    ((hπ (waitProxySilentHistory s)).1 (WaitProxyAction.test a))

/-- The vector of probabilities of first testing each coordinate before a
fixed horizon is a subprobability vector. -/
theorem finiteFirstTestMass_isSubprobability
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    IsSubprobability
      (fun a => ∑ s ∈ Finset.range n, waitProxyFirstTestMass π s a) := by
  constructor
  · intro a
    exact Finset.sum_nonneg fun s _ => waitProxyFirstTestMass_nonneg π hπ s a
  · rw [Finset.sum_comm]
    have htel := sum_waitProxyFirstTestMass_add_survival π hπ n
    linarith [waitProxySurvival_nonneg π hπ n]

/-- Finite-horizon effective binary-separation weight. -/
noncomputable def waitProxyEffectiveWeightFinite
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (n : ℕ) (a : A) : ℝ :=
  2 * ∑ s ∈ Finset.range n, waitProxyFirstTestMass π s a * c s

theorem waitProxyEffectiveWeightFinite_nonneg
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ) (hc0 : ∀ s, 0 ≤ c s)
    (n : ℕ) (a : A) :
    0 ≤ waitProxyEffectiveWeightFinite π c n a := by
  unfold waitProxyEffectiveWeightFinite
  exact mul_nonneg (by norm_num) <|
    Finset.sum_nonneg fun s _ =>
      mul_nonneg (waitProxyFirstTestMass_nonneg π hπ s a) (hc0 s)

/-- A horizon-uniform strict strength bound turns the policy's finite stopping
law into the strict effective subprobability required by the profile algebra.
For the geometric schedule one may take any bound above its first `n`
strengths and below `1/2`. -/
theorem finiteEffectiveWeight_strictSubprobability_of_bound
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ) (hc0 : ∀ s, 0 ≤ c s)
    (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcq : ∀ s < n, 2 * c s ≤ q) :
    IsStrictSubprobability (waitProxyEffectiveWeightFinite π c n) := by
  constructor
  · exact waitProxyEffectiveWeightFinite_nonneg π hπ c hc0 n
  · unfold waitProxyEffectiveWeightFinite
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      ∑ s ∈ Finset.range n,
          ∑ a, 2 * (waitProxyFirstTestMass π s a * c s) ≤
          ∑ s ∈ Finset.range n,
            q * ∑ a, waitProxyFirstTestMass π s a := by
        apply Finset.sum_le_sum
        intro s hs
        calc
          ∑ a, 2 * (waitProxyFirstTestMass π s a * c s) =
              (2 * c s) * ∑ a, waitProxyFirstTestMass π s a := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                ring
          _ ≤ q * ∑ a, waitProxyFirstTestMass π s a := by
                apply mul_le_mul_of_nonneg_right (hcq s (Finset.mem_range.1 hs))
                exact Finset.sum_nonneg fun a _ =>
                  waitProxyFirstTestMass_nonneg π hπ s a
      _ = q * ∑ s ∈ Finset.range n,
          ∑ a, waitProxyFirstTestMass π s a := by
        rw [Finset.mul_sum]
      _ ≤ q * 1 := by
        apply mul_le_mul_of_nonneg_left _ hq0
        have htel := sum_waitProxyFirstTestMass_add_survival π hπ n
        linarith [waitProxySurvival_nonneg π hπ n]
      _ < 1 := by simpa using hq1

/-- Concrete geometric specialization of the finite stopping-law result. -/
theorem geometricEffectiveWeightFinite_strictSubprobability
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (n : ℕ) :
    IsStrictSubprobability
      (waitProxyEffectiveWeightFinite π (waitProxyStrength lam) n) := by
  let q : ℝ := 1 - (1 - lam) ^ n
  apply finiteEffectiveWeight_strictSubprobability_of_bound π hπ
    (waitProxyStrength lam)
    (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s) n q
  · unfold q
    have hp : (0 : ℝ) ≤ (1 - lam) ^ n := pow_nonneg (by linarith) n
    have hp1 : (1 - lam) ^ n ≤ 1 :=
      pow_le_one₀ (by linarith) (by linarith)
    linarith
  · unfold q
    have hp : 0 < (1 - lam) ^ n := pow_pos (by linarith) n
    linarith
  · intro s hs
    unfold waitProxyStrength q
    have hp : (1 - lam) ^ n ≤ (1 - lam) ^ s :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.le_of_lt hs)
    linarith

/-! ### Infinite stopping law

The next declarations pass from the exact finite telescoping identity to the
countable first-test law of one arbitrary policy.  This closes the
measure-free part of the infinite-horizon policy reduction: no probability
space over stopping times is postulated, and all sums are obtained from the
behavioral policy rows themselves.
-/

/-- Probability of first testing some coordinate after exactly `s` waits. -/
noncomputable def waitProxyFirstTestTotal
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation) (s : ℕ) : ℝ :=
  ∑ a, waitProxyFirstTestMass π s a

theorem waitProxyFirstTestTotal_nonneg
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (s : ℕ) :
    0 ≤ waitProxyFirstTestTotal π s := by
  exact Finset.sum_nonneg fun a _ => waitProxyFirstTestMass_nonneg π hπ s a

theorem sum_range_waitProxyFirstTestTotal_le_one
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    ∑ s ∈ Finset.range n, waitProxyFirstTestTotal π s ≤ 1 := by
  have htel := sum_waitProxyFirstTestMass_add_survival π hπ n
  simpa only [waitProxyFirstTestTotal] using
    (show (∑ s ∈ Finset.range n, ∑ a, waitProxyFirstTestMass π s a) ≤ 1 by
      linarith [waitProxySurvival_nonneg π hπ n])

theorem summable_waitProxyFirstTestTotal
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) :
    Summable (waitProxyFirstTestTotal π) :=
  summable_of_sum_range_le
    (waitProxyFirstTestTotal_nonneg π hπ)
    (sum_range_waitProxyFirstTestTotal_le_one π hπ)

theorem tsum_waitProxyFirstTestTotal_le_one
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) :
    ∑' s, waitProxyFirstTestTotal π s ≤ 1 :=
  Real.tsum_le_of_sum_range_le
    (waitProxyFirstTestTotal_nonneg π hπ)
    (sum_range_waitProxyFirstTestTotal_le_one π hπ)

theorem summable_waitProxyFirstTestMass
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (a : A) :
    Summable (fun s => waitProxyFirstTestMass π s a) := by
  apply (summable_waitProxyFirstTestTotal π hπ).of_nonneg_of_le
  · exact fun s => waitProxyFirstTestMass_nonneg π hπ s a
  · intro s
    unfold waitProxyFirstTestTotal
    exact Finset.single_le_sum
      (fun b _ => waitProxyFirstTestMass_nonneg π hπ s b)
      (Finset.mem_univ a)

/-- The actual infinite-horizon effective binary-separation vector of a
policy.  Mass on never testing is absent, exactly as in the paper proof. -/
noncomputable def waitProxyEffectiveWeight
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (a : A) : ℝ :=
  ∑' s, 2 * waitProxyFirstTestMass π s a * c s

theorem summable_waitProxyEffectiveWeight_term
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hchalf : ∀ s, c s ≤ 1 / 2) (a : A) :
    Summable (fun s => 2 * waitProxyFirstTestMass π s a * c s) := by
  apply (summable_waitProxyFirstTestMass π hπ a).of_nonneg_of_le
  · intro s
    exact mul_nonneg
      (mul_nonneg (by norm_num) (waitProxyFirstTestMass_nonneg π hπ s a))
      (hc0 s)
  · intro s
    have hr := waitProxyFirstTestMass_nonneg π hπ s a
    have hc := hchalf s
    nlinarith

theorem waitProxyEffectiveWeight_nonneg
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ) (hc0 : ∀ s, 0 ≤ c s)
    (a : A) :
    0 ≤ waitProxyEffectiveWeight π c a := by
  unfold waitProxyEffectiveWeight
  exact tsum_nonneg fun s => mul_nonneg
    (mul_nonneg (by norm_num) (waitProxyFirstTestMass_nonneg π hπ s a))
    (hc0 s)

/-- Total effective separation contributed by first tests occurring at one
stopping depth. -/
noncomputable def waitProxyEffectiveTotalTerm
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ a, 2 * waitProxyFirstTestMass π s a * c s

theorem waitProxyEffectiveTotalTerm_eq
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (s : ℕ) :
    waitProxyEffectiveTotalTerm π c s =
      (2 * c s) * waitProxyFirstTestTotal π s := by
  unfold waitProxyEffectiveTotalTerm waitProxyFirstTestTotal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem waitProxyEffectiveTotalTerm_nonneg
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ) (hc0 : ∀ s, 0 ≤ c s)
    (s : ℕ) :
    0 ≤ waitProxyEffectiveTotalTerm π c s := by
  rw [waitProxyEffectiveTotalTerm_eq]
  exact mul_nonneg (mul_nonneg (by norm_num) (hc0 s))
    (waitProxyFirstTestTotal_nonneg π hπ s)

theorem waitProxyEffectiveTotalTerm_le_firstTestTotal
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ) (hc0 : ∀ s, 0 ≤ c s)
    (hchalf : ∀ s, c s ≤ 1 / 2) (s : ℕ) :
    waitProxyEffectiveTotalTerm π c s ≤ waitProxyFirstTestTotal π s := by
  rw [waitProxyEffectiveTotalTerm_eq]
  have ht := waitProxyFirstTestTotal_nonneg π hπ s
  have hc := hchalf s
  nlinarith

theorem waitProxyEffectiveTotalTerm_lt_firstTestTotal
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hclt : ∀ s, c s < 1 / 2) {s : ℕ}
    (hs : 0 < waitProxyFirstTestTotal π s) :
    waitProxyEffectiveTotalTerm π c s < waitProxyFirstTestTotal π s := by
  rw [waitProxyEffectiveTotalTerm_eq]
  have hc := hclt s
  nlinarith

theorem summable_waitProxyEffectiveTotalTerm
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ) (hc0 : ∀ s, 0 ≤ c s)
    (hchalf : ∀ s, c s ≤ 1 / 2) :
    Summable (waitProxyEffectiveTotalTerm π c) := by
  exact (summable_waitProxyFirstTestTotal π hπ).of_nonneg_of_le
    (waitProxyEffectiveTotalTerm_nonneg π hπ c hc0)
    (waitProxyEffectiveTotalTerm_le_firstTestTotal π hπ c hc0 hchalf)

/-- Finite Tonelli: summing effective coordinates equals summing their
stopping-depth contributions. -/
theorem sum_waitProxyEffectiveWeight_eq_tsum_totalTerm
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hchalf : ∀ s, c s ≤ 1 / 2) :
    ∑ a, waitProxyEffectiveWeight π c a =
      ∑' s, waitProxyEffectiveTotalTerm π c s := by
  have hswap := Summable.tsum_finsetSum
    (s := (Finset.univ : Finset A))
    (f := fun a s => 2 * waitProxyFirstTestMass π s a * c s)
    (fun a _ => summable_waitProxyEffectiveWeight_term π hπ c hc0 hchalf a)
  simpa [waitProxyEffectiveWeight, waitProxyEffectiveTotalTerm] using hswap.symm

/-- **Arbitrary-policy infinite reduction.**  If every finite test has
strictly subperfect strength, the effective vector extracted from any valid
causal policy is a strict subprobability.  This is the analytic statement
behind `∑_a z_a < 1` in Proposition `prop:unattained-nonzero`. -/
theorem waitProxyEffectiveWeight_strictSubprobability
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hclt : ∀ s, c s < 1 / 2) :
    IsStrictSubprobability (waitProxyEffectiveWeight π c) := by
  have hchalf : ∀ s, c s ≤ 1 / 2 := fun s => (hclt s).le
  constructor
  · exact waitProxyEffectiveWeight_nonneg π hπ c hc0
  · rw [sum_waitProxyEffectiveWeight_eq_tsum_totalTerm π hπ c hc0 hchalf]
    have htotal := tsum_waitProxyFirstTestTotal_le_one π hπ
    have htermSumm := summable_waitProxyEffectiveTotalTerm π hπ c hc0 hchalf
    have htotalSumm := summable_waitProxyFirstTestTotal π hπ
    have hle : ∀ s, waitProxyEffectiveTotalTerm π c s ≤
        waitProxyFirstTestTotal π s :=
      waitProxyEffectiveTotalTerm_le_firstTestTotal π hπ c hc0 hchalf
    rcases lt_or_eq_of_le htotal with hlt | heq
    · exact (htermSumm.tsum_le_tsum hle htotalSumm).trans_lt hlt
    · have hex : ∃ s, 0 < waitProxyFirstTestTotal π s := by
        by_contra hnone
        push Not at hnone
        have hall : ∀ s, waitProxyFirstTestTotal π s = 0 := fun s =>
          le_antisymm (hnone s) (waitProxyFirstTestTotal_nonneg π hπ s)
        have : (∑' s, waitProxyFirstTestTotal π s) = 0 := by
          calc
            (∑' s, waitProxyFirstTestTotal π s) = ∑' _s : ℕ, (0 : ℝ) :=
              tsum_congr hall
            _ = 0 := tsum_zero
        linarith
      obtain ⟨s, hs⟩ := hex
      have hstrict := waitProxyEffectiveTotalTerm_lt_firstTestTotal
        π hπ c hclt hs
      have hsumlt := htermSumm.tsum_lt_tsum hle hstrict htotalSumm
      linarith

theorem geometricEffectiveWeight_strictSubprobability
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    IsStrictSubprobability
      (waitProxyEffectiveWeight π (waitProxyStrength lam)) := by
  exact waitProxyEffectiveWeight_strictSubprobability π hπ
    (waitProxyStrength lam)
    (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
    (fun s => waitProxyStrength_lt_half hlam1 s)

/-- The finite effective vectors converge coordinatewise to the actual
infinite stopping-law vector. -/
theorem waitProxyEffectiveWeightFinite_tendsto
    (π : CausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (hπ : IsCausalPolicy π) (c : ℕ → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hchalf : ∀ s, c s ≤ 1 / 2) (a : A) :
    Filter.Tendsto (fun n => waitProxyEffectiveWeightFinite π c n a)
      Filter.atTop (𝓝 (waitProxyEffectiveWeight π c a)) := by
  have ht := (summable_waitProxyEffectiveWeight_term π hπ c hc0 hchalf a).tendsto_sum_tsum_nat
  simpa [waitProxyEffectiveWeightFinite, waitProxyEffectiveWeight,
    Finset.mul_sum, mul_assoc] using ht

/-! ### Converse realization by a one-shot policy -/

/-- Wait until the unique depth `S`, then test coordinate `a` with probability
`r a`; any leftover mass waits forever.  Off the realized silent path the same
length-based rows keep the definition total and stochastic. -/
noncomputable def waitProxyOneShotPolicy (S : ℕ) (r : A → ℝ) :
    CausalPolicy (WaitProxyAction A) WaitProxyObservation :=
  fun h act =>
    if h.length = S then
      match act with
      | WaitProxyAction.wait => 1 - ∑ a, r a
      | WaitProxyAction.test a => r a
    else
      match act with
      | WaitProxyAction.wait => 1
      | WaitProxyAction.test _ => 0

theorem waitProxyOneShotPolicy_valid (S : ℕ) (r : A → ℝ)
    (hr0 : ∀ a, 0 ≤ r a) (hrsum : ∑ a, r a ≤ 1) :
    IsCausalPolicy (waitProxyOneShotPolicy S r) := by
  intro h
  constructor
  · intro act
    by_cases hs : h.length = S
    · cases act with
      | wait => simp [waitProxyOneShotPolicy, hs]; linarith
      | test a => simp [waitProxyOneShotPolicy, hs, hr0 a]
    · cases act <;> simp [waitProxyOneShotPolicy, hs, hr0]
  · rw [sum_waitProxyAction]
    by_cases hs : h.length = S
    · simp [waitProxyOneShotPolicy, hs]
    · simp [waitProxyOneShotPolicy, hs]

@[simp]
theorem waitProxyOneShotPolicy_test (S : ℕ) (r : A → ℝ)
    (h : CausalHistory (WaitProxyAction A) WaitProxyObservation) (a : A) :
    waitProxyOneShotPolicy S r h (WaitProxyAction.test a) =
      if h.length = S then r a else 0 := by
  by_cases hs : h.length = S <;> simp [waitProxyOneShotPolicy, hs]

@[simp]
theorem waitProxyOneShotPolicy_wait (S : ℕ) (r : A → ℝ)
    (h : CausalHistory (WaitProxyAction A) WaitProxyObservation) :
    waitProxyOneShotPolicy S r h WaitProxyAction.wait =
      if h.length = S then 1 - ∑ a, r a else 1 := by
  by_cases hs : h.length = S <;> simp [waitProxyOneShotPolicy, hs]

theorem waitProxyOneShot_survival_eq_one_of_le
    (S : ℕ) (r : A → ℝ) {s : ℕ} (hs : s ≤ S) :
    waitProxySurvival (waitProxyOneShotPolicy S r) s = 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [show s + 1 = Nat.succ s by omega, waitProxySurvival_succ]
      have hsle : s ≤ S := le_trans (Nat.le_succ s) hs
      rw [ih hsle]
      have hslt : s < S := Nat.lt_of_succ_le hs
      simp [waitProxySilentHistory, hslt.ne]

/-- The one-shot policy has exactly the requested first-test mass at `S` and
zero first-test mass at every other depth. -/
theorem waitProxyOneShot_firstTestMass
    (S : ℕ) (r : A → ℝ) (s : ℕ) (a : A) :
    waitProxyFirstTestMass (waitProxyOneShotPolicy S r) s a =
      if s = S then r a else 0 := by
  by_cases hs : s = S
  · subst s
    simp [waitProxyFirstTestMass,
      waitProxyOneShot_survival_eq_one_of_le S r le_rfl,
      waitProxySilentHistory]
  · simp [waitProxyFirstTestMass, waitProxySilentHistory, hs]

/-- Effective weight of a one-shot policy. -/
theorem waitProxyOneShot_effectiveWeight
    (S : ℕ) (r : A → ℝ) (c : ℕ → ℝ) (a : A) :
    waitProxyEffectiveWeight (waitProxyOneShotPolicy S r) c a =
      2 * r a * c S := by
  unfold waitProxyEffectiveWeight
  rw [tsum_eq_single S]
  · rw [waitProxyOneShot_firstTestMass]
    simp
  · intro s hs
    rw [waitProxyOneShot_firstTestMass]
    simp [hs]

/-- **Converse policy realization.**  Cofinality of the strengths below one
half lets one realize every strict subprobability effective vector exactly:
choose a late enough common test time and rescale its one-shot probabilities.
-/
theorem exists_waitProxyPolicy_effectiveWeight_eq
    (c : ℕ → ℝ) (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (z : A → ℝ) (hz : IsStrictSubprobability z) :
    ∃ π : CausalPolicy (WaitProxyAction A) WaitProxyObservation,
      IsCausalPolicy π ∧ waitProxyEffectiveWeight π c = z := by
  have hzhalf : (∑ a, z a) / 2 < (1 / 2 : ℝ) := by linarith [hz.2]
  obtain ⟨S, hS⟩ := hcofinal ((∑ a, z a) / 2) hzhalf
  have hcS : 0 < c S := by
    have hzsum0 : 0 ≤ ∑ a, z a := Finset.sum_nonneg fun a _ => hz.1 a
    linarith
  let r : A → ℝ := fun a => z a / (2 * c S)
  have hr0 : ∀ a, 0 ≤ r a := by
    intro a
    exact div_nonneg (hz.1 a) (mul_nonneg (by norm_num) hcS.le)
  have hrsum : ∑ a, r a < 1 := by
    change (∑ a, z a / (2 * c S)) < 1
    rw [← Finset.sum_div]
    apply (div_lt_one (mul_pos (by norm_num) hcS)).2
    linarith
  let π := waitProxyOneShotPolicy S r
  refine ⟨π, waitProxyOneShotPolicy_valid S r hr0 hrsum.le, ?_⟩
  funext a
  rw [waitProxyOneShot_effectiveWeight]
  unfold r
  field_simp

/-! ## Deterministic native-plan first-test classification -/

/-- Action selected by a deterministic native plan after the canonical
all-silent, all-wait prefix at a bounded decision depth. -/
noncomputable def waitProxyPlanSilentAction {n : ℕ}
    (τ : CausalPlan (WaitProxyAction A) WaitProxyObservation n) (k : Fin n) :
    WaitProxyAction A :=
  τ (causalDecisionPointOfHistory n (waitProxySilentHistory k.val)
    (by simpa [waitProxySilentHistory] using k.isLt))

/-- The plan waits at every decision point on the no-test path through its
finite horizon. -/
def WaitProxyPlanAlwaysWait {n : ℕ}
    (τ : CausalPlan (WaitProxyAction A) WaitProxyObservation n) : Prop :=
  ∀ k : Fin n, waitProxyPlanSilentAction τ k = WaitProxyAction.wait

/-- The plan first tests coordinate `a` at depth `s` along the unique
pre-test path. -/
def WaitProxyPlanFirstTestsAt {n : ℕ}
    (τ : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (s : ℕ) (a : A) : Prop :=
  ∃ hs : s < n,
    waitProxyPlanSilentAction τ ⟨s, hs⟩ = WaitProxyAction.test a ∧
      ∀ r (hr : r < s),
        waitProxyPlanSilentAction τ ⟨r, lt_trans hr hs⟩ = WaitProxyAction.wait

/-- Every deterministic finite native plan is constant along the realizable
pre-test path, or has a unique least test depth and tested coordinate.  Later
plan decisions may depend on the returned bit, but the response is already
absorbing and those decisions cannot create another informative observation.
-/
theorem waitProxyPlan_alwaysWait_or_firstTestsAt {n : ℕ}
    (τ : CausalPlan (WaitProxyAction A) WaitProxyObservation n) :
    WaitProxyPlanAlwaysWait τ ∨
      ∃ s a, WaitProxyPlanFirstTestsAt τ s a := by
  classical
  by_cases hall : WaitProxyPlanAlwaysWait τ
  · exact Or.inl hall
  · right
    obtain ⟨k, hk⟩ := not_forall.mp hall
    have hex : ∃ s : ℕ, ∃ hs : s < n, ∃ a : A,
        waitProxyPlanSilentAction τ ⟨s, hs⟩ = WaitProxyAction.test a := by
      cases hact : waitProxyPlanSilentAction τ k with
      | wait => exact (hk hact).elim
      | test a => exact ⟨k.val, k.isLt, a, hact⟩
    let s := Nat.find hex
    obtain ⟨hsn, a, ha⟩ := Nat.find_spec hex
    refine ⟨s, a, hsn, ha, ?_⟩
    intro r hr
    cases hact : waitProxyPlanSilentAction τ ⟨r, lt_trans hr hsn⟩ with
    | wait => rfl
    | test b =>
        exfalso
        exact (Nat.find_min hex hr) ⟨lt_trans hr hsn, b, hact⟩

/-- The first-test coordinate and depth are unique. -/
theorem waitProxyPlanFirstTestsAt_unique {n : ℕ}
    (τ : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s t : ℕ} {a b : A}
    (hs : WaitProxyPlanFirstTestsAt τ s a)
    (ht : WaitProxyPlanFirstTestsAt τ t b) :
    s = t ∧ a = b := by
  rcases hs with ⟨hsn, hsa, hbeforeS⟩
  rcases ht with ⟨htn, htb, hbeforeT⟩
  have hst : s = t := by
    rcases lt_trichotomy s t with hlt | heq | hgt
    · have hw := hbeforeT s hlt
      have : (⟨s, hsn⟩ : Fin n) = ⟨s, lt_trans hlt htn⟩ := Fin.ext rfl
      rw [← this, hsa] at hw
      cases hw
    · exact heq
    · have hw := hbeforeS t hgt
      have : (⟨t, htn⟩ : Fin n) = ⟨t, lt_trans hgt hsn⟩ := Fin.ext rfl
      rw [← this, htb] at hw
      cases hw
  subst t
  have hfin : (⟨s, hsn⟩ : Fin n) = ⟨s, htn⟩ := Fin.ext rfl
  rw [← hfin, hsa] at htb
  exact ⟨rfl, WaitProxyAction.test.inj htb⟩

end

end IdExp
