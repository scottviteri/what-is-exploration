import Formal.IdealHistoryCompressor
import Mathlib.Computability.PartrecCode

/-!
# Exact program-description costs for an oracle full-history compressor

The interpreter is a partial recursive program, not an arbitrary numeric cost
oracle. `complexity` is the minimum length of a binary program which actually
outputs the requested string with the given auxiliary string. Prefix freedom
and optimality are stated explicitly; later negative theorems work for every
such interpreter and therefore require neither a chosen universal machine nor
an invariance-constant comparison. Existence of an optimal prefix interpreter
is standard algorithmic-information theory, not constructed in this module.
-/
namespace IdExp.KolmogorovHistoryCompressor
open Encodable
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Bits := List Bool

structure Machine where
  interpreter : Nat.Partrec.Code
  describes_all : ∀ auxiliary data : Bits, ∃ program : Bits,
    encode data ∈ interpreter.eval (Nat.pair (encode program) (encode auxiliary))

namespace Machine
variable (U : Machine)

def Describes (program auxiliary data : Bits) : Prop :=
  encode data ∈ U.interpreter.eval (Nat.pair (encode program) (encode auxiliary))

theorem description_exists (auxiliary data : Bits) : ∃ program, U.Describes program auxiliary data :=
  U.describes_all auxiliary data

def complexity (auxiliary data : Bits) : ℕ :=
  Nat.find (show ∃ n, ∃ program : Bits, program.length = n ∧ U.Describes program auxiliary data from by
    obtain ⟨p,hp⟩ := U.description_exists auxiliary data
    exact ⟨p.length,p,rfl,hp⟩)

theorem shortest_description (auxiliary data : Bits) :
    ∃ program, program.length = U.complexity auxiliary data ∧ U.Describes program auxiliary data := by
  unfold complexity
  exact Nat.find_spec (p := fun n => ∃ program : Bits, program.length = n ∧ U.Describes program auxiliary data)
    (by obtain ⟨p,hp⟩ := U.description_exists auxiliary data; exact ⟨p.length,p,rfl,hp⟩)

theorem complexity_le_length (program auxiliary data : Bits)
    (hp : U.Describes program auxiliary data) : U.complexity auxiliary data ≤ program.length :=
  Nat.find_min' _ ⟨program,rfl,hp⟩

/-- Prefix-free program domains, separately for every fixed auxiliary input. -/
def PrefixFree : Prop := ∀ auxiliary p q x y : Bits,
  U.Describes p auxiliary x → U.Describes q auxiliary y → p <+: q → p = q

/-- Additive optimality among complete prefix-free partial-recursive interpreters. -/
def Optimal : Prop := ∀ V : Machine, V.PrefixFree → ∃ c : ℕ,
  ∀ auxiliary data, U.complexity auxiliary data ≤ V.complexity auxiliary data + c

end Machine

/-- Both the action and the observation are encoded at every step. -/
def encodeHistory : List (Bool × Fin 2) → Bits
  | [] => []
  | (a,o) :: rest => a :: decide (o = 1) :: encodeHistory rest

theorem encodeHistory_injective : Function.Injective encodeHistory := by
  intro h k he
  induction h generalizing k with
  | nil => cases k <;> simp_all [encodeHistory]
  | cons ao h ih =>
    cases k with
    | nil => simp [encodeHistory] at he
    | cons bo k =>
      rcases ao with ⟨a,o⟩
      rcases bo with ⟨b,p⟩
      simp only [encodeHistory, List.cons.injEq] at he
      obtain ⟨hab,hop,hrest⟩ := he
      have hk := ih hrest
      subst b
      subst k
      fin_cases o <;> fin_cases p <;> simp_all

/-- Models range over every finite auxiliary string. The first term charges
its exact description complexity; the second is an exact conditional residual. -/
def twoPartCost (U : Machine) (model : Bits) (h : List (Bool × Fin 2)) : ℕ :=
  U.complexity [] model + U.complexity model (encodeHistory h)

def specification (U : Machine) (initial : Bits) :
    IdealHistoryCompressor.Specification (Bool × Fin 2) where
  Model := Bits
  initial := initial
  cost := twoPartCost U

/-- The same shortest-program cost with any supplied archive-dependent global
minimizer selection. Old optimizing models are still retained by `update`. -/
def specificationWithSelection (U : Machine) (initial : Bits)
    (select : (h : List (Bool × Fin 2)) →
      {m : Bits // ∀ other : Bits, twoPartCost U m h ≤ twoPartCost U other h}) :
    IdealHistoryCompressor.Specification (Bool × Fin 2) where
  Model := Bits
  initial := initial
  cost := twoPartCost U
  minimizer := select

/-- Every oracle update minimizes over all finite models, including its old model. -/
theorem oracle_update_minimizes (U : Machine) (initial old model : Bits)
    (h : List (Bool × Fin 2)) :
    twoPartCost U ((specification U initial).update old h) h ≤ twoPartCost U model h :=
  (specification U initial).update_minimizes old model h

/-- The fitted model and a shortest conditional residual really reconstruct
both action and observation labels of the full archive. -/
theorem fitted_lossless (U : Machine) (initial : Bits) (h : List (Bool × Fin 2)) :
    ∃ modelProgram residualProgram,
      U.Describes modelProgram [] ((specification U initial).fittedModel h) ∧
      U.Describes residualProgram ((specification U initial).fittedModel h) (encodeHistory h) ∧
      modelProgram.length + residualProgram.length =
        twoPartCost U ((specification U initial).fittedModel h) h := by
  obtain ⟨p,hp,hpd⟩ := U.shortest_description [] ((specification U initial).fittedModel h)
  obtain ⟨q,hq,hqd⟩ := U.shortest_description ((specification U initial).fittedModel h) (encodeHistory h)
  exact ⟨p,q,hpd,hqd,by simp only [hp,hq,twoPartCost]⟩

end
end IdExp.KolmogorovHistoryCompressor
