import Formal.KolmogorovHistoryCompressor

/-!
# Prefix-program concatenation and the two-part complexity upper bound

A supplied complete prefix interpreter is turned into an actual partial-
recursive concatenating interpreter by dovetailing over the split and fuel.
Its first result is decoded as a model before executing the residual program.
Additive optimality then supplies the constant in the two-part chain bound.
-/
namespace IdExp.KolmogorovPrefixChain
open Encodable KolmogorovHistoryCompressor
noncomputable section

abbrev SearchInput := Bits × (ℕ × ℕ)

def evalBits (V : Machine) (v : (Bits × Bits) × ℕ) : Option ℕ :=
  Nat.Partrec.Code.evaln v.2 V.interpreter (Nat.pair (encode v.1.1) (encode v.1.2))

theorem evalBits_primrec (V : Machine) : Primrec (evalBits V) := by
  exact Nat.Partrec.Code.primrec_evaln.comp
    ((Primrec.snd.pair (Primrec.const V.interpreter)).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.encode.comp (Primrec.snd.comp Primrec.fst))))

def firstModel (V : Machine) (v : SearchInput) : Option Bits :=
  (evalBits V ((v.1.take v.2.1, []), v.2.2)).bind (decode₂ Bits)

theorem firstModel_primrec (V : Machine) : Primrec (firstModel V) := by
  apply Primrec.option_bind
  · exact (evalBits_primrec V).comp
      (((Primrec.list_take.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).pair
        (Primrec.const [])).pair (Primrec.snd.comp Primrec.snd))
  · exact (Primrec.decode₂.comp Primrec.snd).to₂

def attempt (V : Machine) (v : SearchInput) : Option ℕ :=
  (firstModel V v).bind fun m => evalBits V ((v.1.drop v.2.1, m), v.2.2)

theorem attempt_primrec (V : Machine) : Primrec (attempt V) := by
  apply Primrec.option_bind (firstModel_primrec V)
  exact ((evalBits_primrec V).comp
    (((Primrec.list_drop.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.fst)).pair Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to₂

def search (V : Machine) (r : Bits) : Part ℕ :=
  Nat.rfindOpt fun n => attempt V (r, n.unpair)

theorem search_partrec (V : Machine) : Partrec (search V) := by
  apply Partrec.rfindOpt
  exact ((attempt_primrec V).to_comp.comp
    (Computable.fst.pair (Computable.unpair.comp Computable.snd))).to₂

def rawProgram (n : ℕ) : Bits :=
  (decode (α := Bits) n.unpair.1).getD []

theorem rawProgram_primrec : Primrec rawProgram := by
  exact Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])

def run (V : Machine) (n : ℕ) : Part ℕ := search V (rawProgram n)

theorem run_partrec (V : Machine) : Nat.Partrec (run V) := by
  exact Partrec.nat_iff.mp ((search_partrec V).comp rawProgram_primrec.to_comp)

def interpreter (V : Machine) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (run_partrec V))

theorem interpreter_eval (V : Machine) (n : ℕ) :
    (interpreter V).eval n = run V n :=
  congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp (run_partrec V))) n

@[simp] theorem rawProgram_encode (p z : Bits) :
    rawProgram (Nat.pair (encode p) (encode z)) = p := by
  simp [rawProgram]

/-- A successful finite search stage has a genuine first program and a genuine
residual program. Strict intermediate decoding excludes malformed outputs. -/
theorem attempt_sound (V : Machine) (r : Bits) (k t x : ℕ)
    (h : x ∈ attempt V (r, k, t)) :
    ∃ p q m : Bits, r = p ++ q ∧ V.Describes p [] m ∧
      x ∈ V.interpreter.eval (Nat.pair (encode q) (encode m)) := by
  simp only [attempt, firstModel, evalBits, Option.mem_def, Option.bind_eq_some_iff] at h
  obtain ⟨m, ⟨v, hv, hm⟩, hx⟩ := h
  have hm' : encode m = v := Encodable.decode₂_eq_some.mp hm
  rw [← hm'] at hv
  exact ⟨r.take k, r.drop k, m, (List.take_append_drop k r).symm,
    Nat.Partrec.Code.evaln_sound hv, Nat.Partrec.Code.evaln_sound hx⟩

theorem attempt_complete (V : Machine) (p q m : Bits) (x : ℕ)
    (hp : V.Describes p [] m)
    (hq : x ∈ V.interpreter.eval (Nat.pair (encode q) (encode m))) :
    ∃ n : ℕ, x ∈ attempt V (p ++ q, n.unpair) := by
  obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hp
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hq
  have hs' := Nat.Partrec.Code.evaln_mono (le_max_left s t) hs
  have ht' := Nat.Partrec.Code.evaln_mono (le_max_right s t) ht
  refine ⟨Nat.pair p.length (max s t), ?_⟩
  simp only [Option.mem_def] at hs' ht'
  simp only [Nat.unpair_pair, attempt, firstModel, evalBits, List.take_left,
    List.drop_left, hs', Option.bind_some, Encodable.decode₂_encode, ht', Option.mem_def]

/-- Two successful splits of the same input produce the same intermediate
model and the same residual computation. -/
theorem split_result_unique (V : Machine) (hf : V.PrefixFree)
    (p p' q q' m m' : Bits) (x y : ℕ)
    (hp : V.Describes p [] m) (hp' : V.Describes p' [] m')
    (hq : x ∈ V.interpreter.eval (Nat.pair (encode q) (encode m)))
    (hq' : y ∈ V.interpreter.eval (Nat.pair (encode q') (encode m')))
    (hh : p ++ q = p' ++ q') : x = y := by
  have hpref : p <+: p' ++ q' := hh ▸ List.prefix_append p q
  have heq : p = p' := by
    rcases List.prefix_or_prefix_of_prefix hpref (List.prefix_append p' q') with h | h
    · exact hf [] p p' m m' hp hp' h
    · exact (hf [] p' p m' m hp' hp h).symm
  subst p'
  have hm : m = m' := Encodable.encode_injective (Part.mem_unique hp hp')
  subst m'
  have hqq : q = q' := by simpa using hh
  subst q'
  exact Part.mem_unique hq hq'

theorem search_iff (V : Machine) (hf : V.PrefixFree) (r : Bits) (x : ℕ) :
    x ∈ search V r ↔
      ∃ p q m : Bits, r = p ++ q ∧ V.Describes p [] m ∧
        x ∈ V.interpreter.eval (Nat.pair (encode q) (encode m)) := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hx
    exact attempt_sound V r n.unpair.1 n.unpair.2 x hn
  · rintro ⟨p, q, m, rfl, hp, hq⟩
    obtain ⟨n, hn⟩ := attempt_complete V p q m x hp hq
    have hd : (search V (p ++ q)).Dom := Nat.rfindOpt_dom.mpr ⟨n, x, hn⟩
    have hget := Part.get_mem hd
    obtain ⟨j, hj⟩ := Nat.rfindOpt_spec hget
    obtain ⟨p', q', m', hh, hp', hq'⟩ :=
      attempt_sound V (p ++ q) j.unpair.1 j.unpair.2 _ hj
    have he := split_result_unique V hf p p' q q' m m' x _ hp hp' hq hq' hh
    exact he.symm ▸ hget

def machine (V : Machine) (hf : V.PrefixFree) : Machine where
  interpreter := interpreter V
  describes_all := by
    intro z x
    obtain ⟨p, hp⟩ := V.description_exists [] []
    obtain ⟨q, hq⟩ := V.description_exists [] x
    refine ⟨p ++ q, ?_⟩
    rw [interpreter_eval]
    change encode x ∈ search V (rawProgram _)
    rw [rawProgram_encode]
    exact (search_iff V hf _ _).mpr ⟨p, q, [], rfl, hp, hq⟩

theorem describes_iff (V : Machine) (hf : V.PrefixFree) (r z x : Bits) :
    (machine V hf).Describes r z x ↔
      ∃ p q m : Bits, r = p ++ q ∧ V.Describes p [] m ∧ V.Describes q m x := by
  change encode x ∈ (interpreter V).eval _ ↔ _
  rw [interpreter_eval]
  change encode x ∈ search V (rawProgram _) ↔ _
  rw [rawProgram_encode]
  exact search_iff V hf r (encode x)

theorem concatenated_prefix_unique (V : Machine) (hf : V.PrefixFree)
    (p p' q q' m m' x y : Bits)
    (hp : V.Describes p [] m) (hp' : V.Describes p' [] m')
    (hq : V.Describes q m x) (hq' : V.Describes q' m' y)
    (hh : p ++ q <+: p' ++ q') : p ++ q = p' ++ q' := by
  have hpref := (List.prefix_append p q).trans hh
  have heq : p = p' := by
    rcases List.prefix_or_prefix_of_prefix hpref (List.prefix_append p' q') with h | h
    · exact hf [] p p' m m' hp hp' h
    · exact (hf [] p' p m' m hp' hp h).symm
  subst p'
  have hm : m = m' := Encodable.encode_injective (Part.mem_unique hp hp')
  subst m'
  have hqq : q <+: q' := (List.prefix_append_right_inj p).mp hh
  have hqe : q = q' := hf m q q' x y hq hq' hqq
  subst q'
  rfl

theorem prefixFree (V : Machine) (hf : V.PrefixFree) : (machine V hf).PrefixFree := by
  intro z r s x y hr hs hrs
  obtain ⟨p, q, m, rfl, hp, hq⟩ := (describes_iff V hf r z x).mp hr
  obtain ⟨p', q', m', rfl, hp', hq'⟩ := (describes_iff V hf s z y).mp hs
  exact concatenated_prefix_unique V hf p p' q q' m m' x y hp hp' hq hq' hrs

/-- The two-part upper bound follows from prefix freedom and additive
optimality of the supplied actual interpreter, with no chain-bound premise. -/
theorem exists_chain_constant (V : Machine) (hf : V.PrefixFree) (ho : V.Optimal) :
    ∃ c : ℕ, ∀ m D : Bits,
      V.complexity [] D ≤ V.complexity [] m + V.complexity m D + c := by
  obtain ⟨c, hc⟩ := ho (machine V hf) (prefixFree V hf)
  refine ⟨c, ?_⟩
  intro m D
  obtain ⟨p, hp, hpd⟩ := V.shortest_description [] m
  obtain ⟨q, hq, hqd⟩ := V.shortest_description m D
  have hd : (machine V hf).Describes (p ++ q) [] D :=
    (describes_iff V hf _ _ _).mpr ⟨p, q, m, rfl, hpd, hqd⟩
  have hlen := (machine V hf).complexity_le_length (p ++ q) [] D hd
  simp only [List.length_append, hp, hq] at hlen
  exact (hc [] D).trans (Nat.add_le_add_right hlen c)

end
end IdExp.KolmogorovPrefixChain
