import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Exact model selection and same-archive compression progress

Models need not be finite, enumerable, or computably optimizable. Description
costs are natural numbers. Every update attains the global minimum over every
model, retaining the current model on optimizing ties. Both assessments encode
the same complete new archive. The model-description charge is part of `cost`.
-/
namespace IdExp.IdealHistoryCompressor
noncomputable section

/-- Default choice of a global minimizer. A learner may supply any other fixed
archive-dependent choice through `Specification.minimizer`. -/
def chooseMinimizer {Model Datum : Type*} (initial : Model)
    (cost : Model → List Datum → ℕ) (D : List Datum) :
    {m : Model // ∀ other : Model, cost m D ≤ cost other D} := by
  classical
  have hex : ∃ n, ∃ m : Model, cost m D = n := ⟨cost initial D, initial, rfl⟩
  have hmin : ∃ m : Model, cost m D = Nat.find hex := Nat.find_spec hex
  refine ⟨Classical.choose hmin, ?_⟩
  intro other
  rw [Classical.choose_spec hmin]
  exact Nat.find_min' hex ⟨other, rfl⟩

structure Specification (Datum : Type*) where
  Model : Type
  initial : Model
  cost : Model → List Datum → ℕ
  /-- Fixed archive-dependent minimizer selection, used only when the old model
  is not optimal. This is learner data, not a single hard-coded choice rule. -/
  minimizer : (D : List Datum) → {m : Model // ∀ other : Model, cost m D ≤ cost other D} :=
    fun D => chooseMinimizer initial cost D

namespace Specification
attribute [local instance] Classical.propDecidable

variable {Datum : Type*} (S : Specification Datum)

def optimalCost (D : List Datum) : ℕ :=
  Nat.find (show ∃ n, ∃ m : S.Model, S.cost m D = n from ⟨S.cost S.initial D, S.initial, rfl⟩)

theorem optimalCost_attained (D : List Datum) : ∃ m : S.Model, S.cost m D = S.optimalCost D := by
  unfold optimalCost
  exact Nat.find_spec (p := fun n => ∃ m : S.Model, S.cost m D = n)
    ⟨S.cost S.initial D, S.initial, rfl⟩

theorem optimalCost_le (D : List Datum) (m : S.Model) : S.optimalCost D ≤ S.cost m D :=
  Nat.find_min' _ ⟨m, rfl⟩

def bestModel (D : List Datum) : S.Model := (S.minimizer D).1

theorem bestModel_optimal (D : List Datum) : S.cost (S.bestModel D) D = S.optimalCost D := by
  apply le_antisymm
  · have h := (S.minimizer D).2 (Classical.choose (S.optimalCost_attained D))
    simpa only [bestModel, Classical.choose_spec (S.optimalCost_attained D)] using h
  · exact S.optimalCost_le D (S.bestModel D)

def update (old : S.Model) (D : List Datum) : S.Model :=
  if S.cost old D = S.optimalCost D then old else S.bestModel D

theorem update_optimal (old : S.Model) (D : List Datum) :
    S.cost (S.update old D) D = S.optimalCost D := by
  unfold update
  split_ifs with h
  · exact h
  · exact S.bestModel_optimal D

theorem update_minimizes (old m : S.Model) (D : List Datum) :
    S.cost (S.update old D) D ≤ S.cost m D := by
  rw [S.update_optimal]
  exact S.optimalCost_le D m

theorem update_keeps_optimizer (old : S.Model) (D : List Datum)
    (h : ∀ m, S.cost old D ≤ S.cost m D) : S.update old D = old := by
  have he : S.cost old D = S.optimalCost D := by
    apply le_antisymm
    · simpa only [S.bestModel_optimal] using h (S.bestModel D)
    · exact S.optimalCost_le D old
  simp [update, he]

/-- Both costs use the same full new archive; the difference is real-valued. -/
def gain (old : S.Model) (D : List Datum) : ℝ :=
  (S.cost old D : ℝ) - (S.cost (S.update old D) D : ℝ)

theorem gain_nonneg (old : S.Model) (D : List Datum) : 0 ≤ S.gain old D := by
  unfold gain
  exact sub_nonneg.mpr (by exact_mod_cast S.update_minimizes old old D)

/-- Execute every update in order without discarding previous data. -/
def runFrom (old : S.Model) (archive : List Datum) : List Datum → S.Model × ℝ
  | [] => (old, 0)
  | x :: rest =>
    let D := archive ++ [x]
    let new := S.update old D
    let tail := runFrom new D rest
    (tail.1, S.gain old D + tail.2)

def score (D : List Datum) : ℝ := (S.runFrom S.initial [] D).2

def fittedModel (D : List Datum) : S.Model := (S.runFrom S.initial [] D).1

theorem runFrom_score_nonneg (old : S.Model) (archive D : List Datum) :
    0 ≤ (S.runFrom old archive D).2 := by
  induction D generalizing old archive with
  | nil => exact le_rfl
  | cons x D ih =>
    exact add_nonneg (S.gain_nonneg old (archive ++ [x]))
      (ih (S.update old (archive ++ [x])) (archive ++ [x]))

theorem score_nonneg (D : List Datum) : 0 ≤ S.score D :=
  S.runFrom_score_nonneg S.initial [] D

end Specification
end
end IdExp.IdealHistoryCompressor
