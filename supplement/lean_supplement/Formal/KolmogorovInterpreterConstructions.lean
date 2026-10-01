import Formal.KolmogorovHistoryCompressor

/-!
# Concrete prefix interpreters with exact model-selection behavior

The interpreters below are compiled from primitive-recursive parsers and the
actual partial-recursive evaluator of a supplied machine. No description-length
formula or interpreter is postulated.
-/
namespace IdExp.KolmogorovInterpreterConstructions
open Encodable KolmogorovHistoryCompressor
noncomputable section

abbrev Input := Bits × Bits

def fallback (M : ℕ) (v : Input) : Option (ℕ ⊕ ℕ) :=
  if v.1.take M = List.replicate M true then
    some (.inr (Nat.pair (encode (v.1.drop M)) (encode v.2))) else none

def route (finite : Bool) (M : ℕ) (v : Input) : Option (ℕ ⊕ ℕ) :=
  if finite then
    if v.1 = [false] then some (.inl (encode ([] : Bits)))
    else if v.1 = [true, false] then some (.inl (encode v.2))
    else fallback M v
  else
    if v.1 = [false] then
      if v.2 = [] then none else some (.inl (encode v.2))
    else fallback M v

theorem fallback_primrec (M : ℕ) : Primrec (fallback M) := by
  unfold fallback
  apply Primrec.ite
  · exact Primrec.eq.comp (Primrec.list_take.comp (Primrec.const M) Primrec.fst)
      (Primrec.const _)
  · exact Primrec.option_some.comp (Primrec.sumInr.comp
      (Primrec₂.natPair.comp (Primrec.encode.comp
        (Primrec.list_drop.comp (Primrec.const M) Primrec.fst))
        (Primrec.encode.comp Primrec.snd)))
  · exact Primrec.const _

theorem route_primrec (finite : Bool) (M : ℕ) : Primrec (route finite M) := by
  cases finite
  · apply Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const _))
    · exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const _))
        (Primrec.const _) (Primrec.option_some.comp
          (Primrec.sumInl.comp (Primrec.encode.comp Primrec.snd)))
    · exact fallback_primrec M
  · apply Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const _)) (Primrec.const _)
    exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const _))
      (Primrec.option_some.comp (Primrec.sumInl.comp (Primrec.encode.comp Primrec.snd)))
      (fallback_primrec M)

def dispatch (V : Machine) (v : ℕ ⊕ ℕ) : Part ℕ :=
  v.elim Part.some V.interpreter.eval

theorem dispatch_partrec (V : Machine) : Partrec (dispatch V) := by
  exact Partrec.sumCasesOn_right Computable.id Computable.snd
    ((Nat.Partrec.Code.eval_part.comp (Computable.const V.interpreter) Computable.snd).to₂)

def decodedInput (n : ℕ) : Input :=
  ((decode (α := Bits) n.unpair.1).getD [], (decode (α := Bits) n.unpair.2).getD [])

theorem decodedInput_primrec : Primrec decodedInput := by
  exact (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])).pair
    (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const []))

def run (finite : Bool) (V : Machine) (M n : ℕ) : Part ℕ :=
  (route finite M (decodedInput n) : Part (ℕ ⊕ ℕ)).bind (dispatch V)

theorem run_partrec (finite : Bool) (V : Machine) (M : ℕ) : Nat.Partrec (run finite V M) := by
  apply Partrec.nat_iff.mp
  exact (((route_primrec finite M).comp decodedInput_primrec).to_comp.ofOption).bind
    ((dispatch_partrec V).comp Computable.snd).to₂

def interpreter (finite : Bool) (V : Machine) (M : ℕ) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (run_partrec finite V M))

theorem interpreter_eval (finite : Bool) (V : Machine) (M n : ℕ) :
    (interpreter finite V M).eval n = run finite V M n :=
  congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (run_partrec finite V M))) n

@[simp] theorem decodedInput_encode (p z : Bits) :
    decodedInput (Nat.pair (encode p) (encode z)) = (p,z) := by
  simp [decodedInput]


theorem prefix_ne_zero (M : ℕ) (hM : 2 ≤ M) (q : Bits) :
    List.replicate M true ++ q ≠ [false] := by
  cases M with
  | zero => omega
  | succ n => simp [List.replicate_succ]

theorem prefix_ne_copy (M : ℕ) (hM : 2 ≤ M) (q : Bits) :
    List.replicate M true ++ q ≠ [true, false] := by
  cases M with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k => simp [List.replicate_succ]

theorem take_prefix_iff (M : ℕ) (p : Bits) :
    p.take M = List.replicate M true ↔ ∃ q, p = List.replicate M true ++ q := by
  constructor
  · intro h
    exact ⟨p.drop M, by rw [← h, List.take_append_drop]⟩
  · rintro ⟨q,rfl⟩
    simp

theorem fallback_eval (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M)
    (q z : Bits) :
    (interpreter finite V M).eval
      (Nat.pair (encode (List.replicate M true ++ q)) (encode z)) =
      V.interpreter.eval (Nat.pair (encode q) (encode z)) := by
  rw [interpreter_eval]
  cases finite <;> simp [run, route, decodedInput_encode, prefix_ne_zero M hM,
    prefix_ne_copy M hM, fallback, dispatch, Sum.elim]

def machine (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M) : Machine where
  interpreter := interpreter finite V M
  describes_all := by
    intro z x
    obtain ⟨q,hq⟩ := V.description_exists z x
    refine ⟨List.replicate M true ++ q, ?_⟩
    simpa only [fallback_eval finite V M hM] using (show encode x ∈ V.interpreter.eval _ from hq)

theorem describes_iff (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M)
    (p z x : Bits) :
    (machine finite V M hM).Describes p z x ↔
      (finite = true ∧ p = [false] ∧ x = []) ∨
      (p = (if finite then [true,false] else [false]) ∧
        (finite = true ∨ z ≠ []) ∧ x = z) ∨
      (∃ q, p = List.replicate M true ++ q ∧ V.Describes q z x) := by
  have hz : ¬ ([false] : Bits).take M = List.replicate M true := by
    rw [take_prefix_iff]
    rintro ⟨q,hq⟩
    exact prefix_ne_zero M hM q hq.symm
  have hc : ¬ ([true,false] : Bits).take M = List.replicate M true := by
    rw [take_prefix_iff]
    rintro ⟨q,hq⟩
    exact prefix_ne_copy M hM q hq.symm
  have hf : (∃ q, p = List.replicate M true ++ q ∧ V.Describes q z x) ↔
      p.take M = List.replicate M true ∧ V.Describes (p.drop M) z x := by
    constructor
    · rintro ⟨q,rfl,hq⟩; simpa using hq
    · rintro ⟨hp,hq⟩
      exact ⟨p.drop M, by rw [← hp, List.take_append_drop], hq⟩
  rw [hf]
  change encode x ∈ (interpreter finite V M).eval _ ↔ _
  rw [interpreter_eval]
  simp only [run, decodedInput_encode]
  clear hf
  cases finite <;> by_cases hp : p = [false] <;> by_cases hq : p = [true,false] <;>
    by_cases ha : z = [] <;> by_cases ht : p.take M = List.replicate M true <;>
    simp_all [route, fallback, dispatch, Sum.elim, Machine.Describes, encode_injective.eq_iff]
  all_goals
    change encode x = encode ([] : Bits) ↔ x = []
    exact (encode_injective (α := Bits)).eq_iff


theorem complexity_le_fallback (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M)
    (z x : Bits) : (machine finite V M hM).complexity z x ≤ M + V.complexity z x := by
  obtain ⟨q,hq,hd⟩ := V.shortest_description z x
  have hh := (machine finite V M hM).complexity_le_length
    (List.replicate M true ++ q) z x
    ((describes_iff finite V M hM _ _ _).mpr (Or.inr (Or.inr ⟨q,rfl,hd⟩)))
  simpa [hq] using hh

theorem complexity_eq_fallback (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M)
    (z x : Bits) (hzero : ¬ (finite = true ∧ x = []))
    (hcopy : ¬ ((finite = true ∨ z ≠ []) ∧ x = z)) :
    (machine finite V M hM).complexity z x = M + V.complexity z x := by
  apply Nat.le_antisymm (complexity_le_fallback finite V M hM z x)
  obtain ⟨p,hp,hd⟩ := (machine finite V M hM).shortest_description z x
  rcases (describes_iff finite V M hM p z x).mp hd with hz | hc | ⟨q,rfl,hq⟩
  · exact (hzero ⟨hz.1,hz.2.2⟩).elim
  · exact (hcopy ⟨hc.2.1,hc.2.2⟩).elim
  · have hh := V.complexity_le_length q z x hq
    simp only [List.length_append, List.length_replicate] at hp
    omega

theorem complexity_pos (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M)
    (z x : Bits) : 1 ≤ (machine finite V M hM).complexity z x := by
  obtain ⟨p,hp,hd⟩ := (machine finite V M hM).shortest_description z x
  rcases (describes_iff finite V M hM p z x).mp hd with hz | hc | ⟨q,rfl,hq⟩
  · rw [hz.2.1] at hp; simp at hp; omega
  · rw [hc.1] at hp; cases finite <;> simp at hp <;> omega
  · simp only [List.length_append, List.length_replicate] at hp; omega

theorem finite_empty (V : Machine) (M : ℕ) (hM : 2 ≤ M) (z : Bits) :
    (machine true V M hM).complexity z [] = 1 := by
  apply Nat.le_antisymm _ (complexity_pos true V M hM z [])
  simpa using (machine true V M hM).complexity_le_length [false] z []
    ((describes_iff true V M hM _ _ _).mpr (Or.inl ⟨rfl,rfl,rfl⟩))

theorem finite_self (V : Machine) (M : ℕ) (hM : 2 ≤ M) (z : Bits) (hz : z ≠ []) :
    (machine true V M hM).complexity z z = 2 := by
  apply Nat.le_antisymm
  · simpa using (machine true V M hM).complexity_le_length [true,false] z z
      ((describes_iff true V M hM _ _ _).mpr (Or.inr (Or.inl ⟨rfl,Or.inl rfl,rfl⟩)))
  · obtain ⟨p,hp,hd⟩ := (machine true V M hM).shortest_description z z
    rcases (describes_iff true V M hM p z z).mp hd with hh | hc | ⟨q,rfl,hq⟩
    · exact (hz hh.2.2).elim
    · rw [hc.1] at hp; simp at hp; omega
    · simp only [List.length_append, List.length_replicate] at hp; omega

theorem divergent_self (V : Machine) (M : ℕ) (hM : 2 ≤ M) (z : Bits) (hz : z ≠ []) :
    (machine false V M hM).complexity z z = 1 := by
  apply Nat.le_antisymm _ (complexity_pos false V M hM z z)
  simpa using (machine false V M hM).complexity_le_length [false] z z
    ((describes_iff false V M hM _ _ _).mpr (Or.inr (Or.inl ⟨rfl,Or.inr hz,rfl⟩)))

theorem finite_background (V : Machine) (M : ℕ) (hM : 2 ≤ M) (x : Bits) (hx : x ≠ []) :
    (machine true V M hM).complexity [] x = M + V.complexity [] x :=
  complexity_eq_fallback true V M hM [] x (by simp [hx]) (by simp [hx])

theorem finite_other (V : Machine) (M : ℕ) (hM : 2 ≤ M) (z x : Bits)
    (hx : x ≠ []) (h : x ≠ z) :
    (machine true V M hM).complexity z x = M + V.complexity z x :=
  complexity_eq_fallback true V M hM z x (by simp [hx]) (by simp [h])

theorem divergent_background (V : Machine) (M : ℕ) (hM : 2 ≤ M) (x : Bits) :
    (machine false V M hM).complexity [] x = M + V.complexity [] x :=
  complexity_eq_fallback false V M hM [] x (by simp) (by simp)

theorem divergent_other (V : Machine) (M : ℕ) (hM : 2 ≤ M) (z x : Bits) (h : x ≠ z) :
    (machine false V M hM).complexity z x = M + V.complexity z x :=
  complexity_eq_fallback false V M hM z x (by simp) (by simp [h])

theorem optimal (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M)
    (hV : V.Optimal) : (machine finite V M hM).Optimal := by
  intro W hW
  obtain ⟨c,hc⟩ := hV W hW
  refine ⟨M+c,fun z x => ?_⟩
  have h := complexity_le_fallback finite V M hM z x
  have := hc z x
  omega


theorem prefixFree (finite : Bool) (V : Machine) (M : ℕ) (hM : 2 ≤ M)
    (hV : V.PrefixFree) : (machine finite V M hM).PrefixFree := by
  cases M with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      intro z p q x y hp hq hpq
      rcases (describes_iff finite V _ hM p z x).mp hp with hp | hp | ⟨p',rfl,hpBase⟩
      · rcases hp with ⟨hf,rfl,hx⟩
        rcases (describes_iff finite V _ hM q z y).mp hq with hq | hq | ⟨q',rfl,hqBase⟩
        · exact hq.2.1.symm
        · rw [hq.1]; cases finite <;> simp_all
        · simp [List.replicate_succ] at hpq
      · rcases hp with ⟨rfl,_,hx⟩
        rcases (describes_iff finite V _ hM q z y).mp hq with hq | hq | ⟨q',rfl,hqBase⟩
        · rw [hq.2.1]; cases finite <;> simp_all
        · exact hq.1.symm
        · cases finite <;> simp [List.replicate_succ] at hpq
      · rcases (describes_iff finite V _ hM q z y).mp hq with hq | hq | ⟨q',rfl,hqBase⟩
        · rw [hq.2.1] at hpq; simp [List.replicate_succ] at hpq
        · rw [hq.1] at hpq; cases finite <;> simp [List.replicate_succ] at hpq
        · have he : p' = q' := hV z p' q' x y hpBase hqBase (by simpa using hpq)
          rw [he]

end
end IdExp.KolmogorovInterpreterConstructions
