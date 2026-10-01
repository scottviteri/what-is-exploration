import Formal.FinitaryContinuityObstruction
import Mathlib.Computability.Halting

/-!
# A uniform evaluation obstruction for complete policy objectives

The literal Boolean WAIT/REVEAL environment has computable deterministic worlds.
A bounded universal-machine simulation supplies total deterministic policies.
Halting causes one finite-time revelation; nonhalting causes perpetual waiting.
A real objective respecting the actual finitary experiment order and separating
startup revelation from waiting cannot admit a uniform computable-real evaluator
on program descriptions of all total computable policies.
-/

namespace IdExp.PolicyEvaluation
open Nat.Partrec
open Encodable

abbrev History := CausalHistory Bool Bool

/-- A program denotes the deterministic next-action function on every history. -/
def Represents (c : Code) (p : History → Bool) : Prop :=
  ∀ h, Code.eval c (encode h) = Part.some (encode (p h))

/-- The bounded simulation changes from unknown to halted only once. -/
def haltingPulse (c : Code) (t : ℕ) : Bool :=
  (Code.evaln (t + 1) c 0).isSome && !(Code.evaln t c 0).isSome

/-- A total action rule; its computation never waits for the simulated program. -/
def haltingAction (c : Code) (h : History) : Bool := haltingPulse c h.length

noncomputable def haltingPolicy (c : Code) : ValidCausalPolicy Bool Bool :=
  validDetPolicy (haltingAction c)

/-- Reveal exactly at startup, then WAIT. -/
def revealAction (h : History) : Bool := decide (h.length = 0)

noncomputable def revealPolicy : ValidCausalPolicy Bool Bool :=
  validDetPolicy revealAction


theorem haltingPulse_primrec : Primrec fun x : Code × ℕ => haltingPulse x.1 x.2 := by
  have hnow : Primrec fun x : Code × ℕ => (Code.evaln (x.2 + 1) x.1 0).isSome :=
    Primrec.option_isSome.comp <| Code.primrec_evaln.comp
      (((Primrec.succ.comp Primrec.snd).pair Primrec.fst).pair (Primrec.const 0))
  have hprev : Primrec fun x : Code × ℕ => !(Code.evaln x.2 x.1 0).isSome :=
    (Primrec.dom_bool not).comp <| Primrec.option_isSome.comp <| Code.primrec_evaln.comp
      ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0))
  exact (hnow.cond hprev (Primrec.const false)).of_eq fun x => by
    simp [haltingPulse, Bool.cond_eq_ite]

theorem haltingAction_primrec : Primrec fun x : Code × History => haltingAction x.1 x.2 :=
  haltingPulse_primrec.comp (Primrec.fst.pair (Primrec.list_length.comp Primrec.snd))

theorem haltingAction_computable (c : Code) : Computable (haltingAction c) :=
  (haltingAction_primrec.comp ((Primrec.const c).pair Primrec.id)).to_comp

theorem haltingPulse_eq_false_of_not_halts (c : Code) (hc : ¬(Code.eval c 0).Dom) (t : ℕ) :
    haltingPulse c t = false := by
  have hnone : Code.evaln (t + 1) c 0 = Option.none := by
    cases he : Code.evaln (t + 1) c 0 with
    | none => rfl
    | some x =>
      exact False.elim (hc (Code.evaln_sound (show x ∈ Code.evaln (t + 1) c 0 from he)).1)
  simp [haltingPulse, hnone]

theorem haltingPolicy_eq_wait (c : Code) (hc : ¬(Code.eval c 0).Dom) :
    haltingPolicy c = BinaryWaitReveal.waitPolicy := by
  have ha : haltingAction c = fun _ => false := by
    funext h
    exact haltingPulse_eq_false_of_not_halts c hc h.length
  simp [haltingPolicy, BinaryWaitReveal.waitPolicy, ha]

theorem exists_haltingPulse (c : Code) (hc : (Code.eval c 0).Dom) :
    ∃ t, haltingPulse c t = true := by
  classical
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hc
  have hex : ∃ k, (Code.evaln k c 0).isSome = true := by
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    exact ⟨k, Option.isSome_iff_exists.mpr ⟨x, hk⟩⟩
  let k := Nat.find hex
  have hk : (Code.evaln k c 0).isSome = true := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hn
    have : k = 0 := by omega
    simp [this, Code.evaln] at hk
  have hprev : (Code.evaln (k - 1) c 0).isSome = false := by
    cases he : (Code.evaln (k - 1) c 0).isSome
    · rfl
    · exact False.elim (Nat.find_min hex (show k - 1 < k by omega) he)
  exact ⟨k - 1, by simp [haltingPulse, show k - 1 + 1 = k by omega, hk, hprev]⟩

/-- Bounded detection produces at most one REVEAL action. -/
theorem haltingPulse_unique (c : Code) {m n : ℕ}
    (hm : haltingPulse c m = true) (hn : haltingPulse c n = true) : m = n := by
  have not_lt : ∀ i j, haltingPulse c i = true → haltingPulse c j = true → ¬ i < j := by
    intro i j hi hj hij
    have hi' := (Bool.and_eq_true _ _).mp hi
    have hj' := (Bool.and_eq_true _ _).mp hj
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hi'.1
    have hy : x ∈ Code.evaln j c 0 := Code.evaln_mono (by omega) hx
    have hs := Option.isSome_iff_exists.mpr ⟨x, hy⟩
    have hf := (Bool.not_eq_true' _).mp hj'.2
    simp_all
  exact Nat.le_antisymm (Nat.le_of_not_gt (not_lt n m hn hm))
    (Nat.le_of_not_gt (not_lt m n hm hn))

/-- Any deterministic time schedule that reveals once gives injective records thereafter. -/
theorem timed_trace_injective (a : ℕ → Bool) (m : ℕ) (hm : a m = true)
    (t : ℕ) (ht : m < t) :
    Function.Injective (fun θ => detTraceFin (fun h : History => a h.length)
      (BinaryWaitReveal.response θ) t) := by
  intro θ η he
  have hl := (detTraceFin_eq_iff _ _ _ t).mp he
  have hp := detTraceList_eq_of_le _ (show m + 1 ≤ t by omega) hl
  have hlast := congrArg List.getLast? hp
  simpa [detTraceList_succ, BinaryWaitReveal.response, hm] using hlast

theorem timed_dominates_det (a : ℕ → Bool) (m : ℕ) (hm : a m = true)
    (p : History → Bool) :
    CausalFinitaryDominates BinaryWaitReveal.worlds
      (validDetPolicy (fun h : History => a h.length)) (validDetPolicy p) := by
  intro n ε hε
  refine ⟨m + 1, fun t ht => ?_⟩
  change finiteDeficiency
    (causalFiniteExperiment (detPolicy (fun h : History => a h.length))
      (fun θ => detResponse (BinaryWaitReveal.response θ)) t)
    (causalFiniteExperiment (detPolicy p) (fun θ => detResponse (BinaryWaitReveal.response θ)) n) < ε
  rw [causalFiniteExperiment_det, causalFiniteExperiment_det]
  have hz : finiteDeficiency
      (diracExp (fun θ => detTraceFin (fun h : History => a h.length)
        (BinaryWaitReveal.response θ) t))
      (diracExp (fun θ => detTraceFin p (BinaryWaitReveal.response θ) n)) = 0 := by
    apply finiteDeficiency_diracExp_eq_zero_of_separates
    intro θ η he
    exact congrArg (fun θ => detTraceFin p (BinaryWaitReveal.response θ) n)
      (timed_trace_injective a m hm t (by omega) he)
  rwa [hz]

theorem reveal_dominates_det (p : History → Bool) :
    CausalFinitaryDominates BinaryWaitReveal.worlds revealPolicy (validDetPolicy p) := by
  exact timed_dominates_det (fun n => decide (n = 0)) 0 (by decide) p

theorem halting_dominates_reveal (c : Code) (hc : (Code.eval c 0).Dom) :
    CausalFinitaryDominates BinaryWaitReveal.worlds (haltingPolicy c) revealPolicy := by
  obtain ⟨m, hm⟩ := exists_haltingPulse c hc
  exact timed_dominates_det (haltingPulse c) m hm revealAction

theorem monotone_score_halting_eq
    (J : ValidCausalPolicy Bool Bool → ℝ)
    (hmono : ∀ π σ, CausalFinitaryDominates BinaryWaitReveal.worlds π σ → J σ ≤ J π)
    (c : Code) (hc : (Code.eval c 0).Dom) : J (haltingPolicy c) = J revealPolicy :=
  le_antisymm (hmono _ _ (reveal_dominates_det (haltingAction c)))
    (hmono _ _ (halting_dominates_reveal c hc))


/-- Immediate revelation is a sufficient policy even against randomized collectors. -/
theorem reveal_nativelySufficient : CausalNativelySufficient BinaryWaitReveal.worlds revealPolicy := by
  apply (det_causalNativelySufficient_iff_traces_separate revealAction
    BinaryWaitReveal.response).mpr
  refine ⟨1, fun θ η he => ?_⟩
  have hf : detTraceFin revealAction (BinaryWaitReveal.response θ) 1 =
      detTraceFin revealAction (BinaryWaitReveal.response η) 1 :=
    (detTraceFin_eq_iff _ _ _ _).mpr he
  have hθη : θ = η := timed_trace_injective (fun n => decide (n = 0)) 0
    (by decide) 1 (by omega) hf
  subst η
  intro h
  rfl

/-- A computable compiler producing a total history-policy program for each machine. -/
theorem exists_halting_compiler : ∃ compile : Code → Code,
    Computable compile ∧ ∀ c, Represents (compile c) (haltingAction c) := by
  have hc := haltingAction_primrec.to_comp
  obtain ⟨base, hbase⟩ := Code.exists_code.mp hc
  refine ⟨fun c => Code.curry base (encode c),
    (Code.primrec₂_curry.comp (Primrec.const base) Primrec.encode).to_comp, ?_⟩
  intro c h
  simp only [Code.eval_curry]
  have hb := congrFun hbase (Nat.pair (encode c) (encode h))
  simpa using hb


/-- The two worlds' response functions are primitive recursive. -/
theorem world_response_primrec (θ : Bool) :
    Primrec fun x : History × Bool => BinaryWaitReveal.response θ x.1 x.2 :=
  (Primrec.snd.cond (Primrec.const θ) (Primrec.const false)).of_eq fun x => by
    cases x.2 <;> rfl

theorem revealAction_primrec : Primrec revealAction :=
  primrecPred_iff_primrec_decide.mp
    (Primrec.eq.comp Primrec.list_length (Primrec.const 0))

theorem waitAction_primrec : Primrec (fun _ : History => false) := Primrec.const false

/-- Startup revelation strictly improves the actual finitary order. -/
theorem reveal_strictly_dominates_wait :
    CausalFinitaryDominates BinaryWaitReveal.worlds revealPolicy BinaryWaitReveal.waitPolicy ∧
    ¬ CausalFinitaryDominates BinaryWaitReveal.worlds BinaryWaitReveal.waitPolicy revealPolicy := by
  refine ⟨reveal_dominates_det (fun _ => false), ?_⟩
  intro hw
  exact BinaryWaitReveal.wait_not_dominates_immediate <|
    causalFinitaryDominates_trans BinaryWaitReveal.worlds BinaryWaitReveal.worlds_valid hw
      (reveal_dominates_det (BinaryWaitReveal.delayedAction 0))

/-- An arbitrary rational is encoded by two natural numerators and a positive denominator.
The representation is redundant, so no normal-form or sign restriction is imposed. -/
abbrev RationalCode := ℕ × ℕ × ℕ

noncomputable def rationalValue (q : RationalCode) : ℝ :=
  ((q.1 : ℝ) - q.2.1) / (q.2.2 + 1)

theorem rationalValue_rat (r : ℚ) :
    rationalValue (r.num.toNat, (-r.num).toNat, r.den - 1) = (r : ℝ) := by
  have hn : (r.num.toNat : ℤ) - (-r.num).toNat = r.num := by omega
  have hd : r.den - 1 + 1 = r.den := by have := r.den_pos; omega
  unfold rationalValue
  rw [Rat.cast_def]
  have hn' : (r.num.toNat : ℝ) - ((-r.num).toNat : ℝ) = (r.num : ℝ) := by
    exact_mod_cast hn
  have hd' : ((r.den - 1 : ℕ) : ℝ) + 1 = (r.den : ℝ) := by exact_mod_cast hd
  rw [hn', hd']

/-- Comparison of represented rationals is integer arithmetic on their codes. -/
def rationalAbove (r q : RationalCode) : Prop :=
  r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1) <
    q.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1)

instance (r q : RationalCode) : Decidable (rationalAbove r q) :=
  inferInstanceAs (Decidable (_ < _))

theorem rationalAbove_iff (r q : RationalCode) :
    rationalAbove r q ↔ rationalValue r < rationalValue q := by
  unfold rationalAbove rationalValue
  rw [div_lt_div_iff₀ (by positivity : 0 < (r.2.2 : ℝ) + 1)
    (by positivity : 0 < (q.2.2 : ℝ) + 1)]
  have hcast :
      (r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1) <
        q.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1)) ↔
      ((r.1 : ℝ) * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1) <
        q.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1)) := by
    norm_cast
  rw [hcast]
  constructor <;> intro h <;> nlinarith

theorem rationalAbove_primrec (r : RationalCode) : PrimrecPred (rationalAbove r) := by
  exact Primrec.nat_lt.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const r.1)
        (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.const (r.2.2 + 1))))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp Primrec.fst (Primrec.const (r.2.2 + 1)))
      (Primrec.nat_mul.comp (Primrec.const r.2.1)
        (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))))

/-- Uniform computable-real evaluation on programs for total policies.
The evaluator may diverge on invalid or nontotal programs. -/
def UniformlyEvaluates (J : ValidCausalPolicy Bool Bool → ℝ)
    (ev : Code × ℕ →. RationalCode) : Prop :=
  Partrec ev ∧ ∀ c p, Represents c p → ∀ n, ∃ q ∈ ev (c,n),
    |rationalValue q - J (validDetPolicy p)| ≤ (1 / 2 : ℝ) ^ n

/-- The literal policy-evaluation theorem. Only one strict score comparison is
required; all remaining order comparisons use weak finitary monotonicity. -/
theorem no_uniform_evaluation
    (J : ValidCausalPolicy Bool Bool → ℝ)
    (hmono : ∀ π σ, CausalFinitaryDominates BinaryWaitReveal.worlds π σ → J σ ≤ J π)
    (hstrict : J BinaryWaitReveal.waitPolicy < J revealPolicy) :
    ¬ ∃ ev, UniformlyEvaluates J ev := by
  classical
  rintro ⟨ev, hrec, hacc⟩
  obtain ⟨compile, hcompile, hrep⟩ := exists_halting_compiler
  obtain ⟨r, har, hrb⟩ := exists_rat_btwn hstrict
  let threshold : RationalCode := (r.num.toNat, (-r.num).toNat, r.den - 1)
  have hthreshold : rationalValue threshold = (r : ℝ) := rationalValue_rat r
  have hgap : 0 < min ((r : ℝ) - J BinaryWaitReveal.waitPolicy)
      (J revealPolicy - (r : ℝ)) := lt_min (sub_pos.mpr har) (sub_pos.mpr hrb)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (1 / 2 : ℝ) < 1)
  have hnleft : (1 / 2 : ℝ) ^ n < (r : ℝ) - J BinaryWaitReveal.waitPolicy :=
    lt_of_lt_of_le hn (min_le_left _ _)
  have hnright : (1 / 2 : ℝ) ^ n < J revealPolicy - (r : ℝ) :=
    lt_of_lt_of_le hn (min_le_right _ _)
  let classify : Code →. Bool := fun c =>
    (ev (compile c, n)).map (fun q => decide (rationalAbove threshold q))
  have hclassify : Partrec classify :=
    (hrec.comp (hcompile.pair (Computable.const n))).map
      ((primrecPred_iff_primrec_decide.mp (rationalAbove_primrec threshold)).to_comp.comp Computable.snd).to₂
  have hdec : Computable fun c => decide ((Code.eval c 0).Dom) := by
    apply hclassify.of_eq_tot
    intro c
    obtain ⟨q, hq, herr⟩ := hacc (compile c) (haltingAction c) (hrep c) n
    have habs := abs_le.mp herr
    have heq : decide (rationalAbove threshold q) = decide ((Code.eval c 0).Dom) := by
      apply Bool.decide_congr
      rw [rationalAbove_iff, hthreshold]
      by_cases hc : (Code.eval c 0).Dom
      · have hvalue := monotone_score_halting_eq J hmono c hc
        change J (validDetPolicy (haltingAction c)) = _ at hvalue
        rw [hvalue] at habs
        exact iff_of_true (by linarith [habs.1]) hc
      · have hvalue : J (validDetPolicy (haltingAction c)) = J BinaryWaitReveal.waitPolicy :=
          congrArg J (haltingPolicy_eq_wait c hc)
        rw [hvalue] at habs
        exact iff_of_false (by linarith [habs.2]) hc
    change decide ((Code.eval c 0).Dom) ∈
      (ev (compile c, n)).map (fun q => decide (rationalAbove threshold q))
    exact (Part.mem_map_iff _).mpr ⟨q, hq, heq⟩
  exact ComputablePred.halting_problem 0 ⟨inferInstance, hdec⟩

#print axioms no_uniform_evaluation

end IdExp.PolicyEvaluation
