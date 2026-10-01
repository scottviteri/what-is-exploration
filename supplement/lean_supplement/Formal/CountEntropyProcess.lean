import Formal.RewardProcessWitness
import Formal.FirstVisitCountMisranking
import Formal.ControlEntropy

/-!
# First-visit and empirical-entropy optima lose a whole native process

The first action permanently selects the revealing or independent-noise
branch. The objective is optimized over every randomized history policy.
At two observations empirical label entropy is the number of distinct labels
minus one, times log 2. Every optimum of either objective therefore remains
world-independent forever and is strictly finitarily dominated by READ.
-/
namespace IdExp.FirstVisitCount
open Finset
noncomputable section

theorem noise_tail_independent (π : CausalPolicy Action Observation)
    (θ θ' : World) (o : Observation) (pre rest : CausalHistory Action Observation) :
    causalTraceProbFrom π (response θ) ((1,o) :: pre) rest =
      causalTraceProbFrom π (response θ') ((1,o) :: pre) rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom, response, KnownNoise.response]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
    rw [List.cons_append, ih]

theorem noise_prefix_classIndependent (π : ValidCausalPolicy Action Observation)
    (hπ : π.1 [] 0 = 0) (t : ℕ) :
    ClassIndependentFiniteExperiment (causalFiniteExperiment π.1 response t) := by
  intro θ θ'
  funext w
  unfold causalFiniteExperiment causalTraceProb
  cases he : List.ofFn w with
  | nil => rfl
  | cons ao rest =>
    by_cases ha : ao.1 = 0
    · simp [causalTraceProbFrom, ha, hπ]
    · have ha1 : ao.1 = 1 := by
        rcases ao with ⟨a,o⟩
        fin_cases a <;> simp_all
      rcases ao with ⟨a,o⟩
      dsimp at ha1
      subst a
      simp only [causalTraceProbFrom, response, KnownNoise.response,
        show (1 : Fin 2) ≠ 0 by decide, if_false, List.nil_append]
      rw [noise_tail_independent π.1 θ θ' o [] rest]

def readDecode (w : CausalFiniteTrace Action Observation 1) : World :=
  if (w 0).2 = 0 then 0 else 1

theorem read_prefix_reveals (θ : World) (w : CausalFiniteTrace Action Observation 1)
    (hw : causalFiniteExperiment (purePolicy 0).1 response 1 θ w ≠ 0) :
    readDecode w = θ := by
  have he : causalFiniteExperiment (purePolicy 0).1 response 1 θ w =
      (if (w 0).1 = 0 then (1 : ℝ) else 0) * KnownNoise.response θ [] (w 0).1 (w 0).2 := by
    simp [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom, List.ofFn_succ,
      purePolicy, KnownNoise.purePolicy, detPolicy, response]
  rw [he] at hw
  have ha : (w 0).1 = 0 := by split_ifs at hw <;> simp_all
  rw [ha] at hw
  simp only [if_true, one_mul, KnownNoise.response] at hw
  unfold readDecode
  generalize ho : (w 0).2 = o at hw ⊢
  fin_cases θ <;> fin_cases o <;> norm_num at *

theorem readPolicy_finitarilyGreatest : CausalFinitarilyGreatest response (purePolicy 0) :=
  causalFinitarilyGreatest_of_revealing_prefix response response_valid
    (purePolicy 0) 1 readDecode read_prefix_reveals

theorem noise_root_strictly_dominated (π : ValidCausalPolicy Action Observation)
    (hπ : π.1 [] 0 = 0) :
    CausalFinitaryDominates response (purePolicy 0) π ∧
      ¬ CausalFinitaryDominates response π (purePolicy 0) := by
  refine ⟨readPolicy_finitarilyGreatest π, ?_⟩
  apply classIndependent_prefixes_not_finitarily_dominate response response_valid π (purePolicy 0) 2
    (noise_prefix_classIndependent π hπ)
  change 0 < finiteTV (readRecord 0) (readRecord 1)
  rw [readRecord_pairTV]
  norm_num

theorem every_count_optimum_strictly_finitarily_dominated
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation, expectedCount ρ ≤ expectedCount π) :
    CausalFinitaryDominates response (purePolicy 0) π ∧
      ¬ CausalFinitaryDominates response π (purePolicy 0) :=
  noise_root_strictly_dominated π ((count_maximizers π).mp hopt)

/-- Actual empirical frequencies of the two observed labels. -/
def empiricalLabelLaw (w : CausalFiniteTrace Action Observation 2) (o : Observation) : ℝ :=
  ((if (w 0).2 = o then 1 else 0) + (if (w 1).2 = o then 1 else 0)) / 2

def empiricalLabelEntropy (w : CausalFiniteTrace Action Observation 2) : ℝ :=
  ent (empiricalLabelLaw w)

theorem empiricalLabelEntropy_eq (w : CausalFiniteTrace Action Observation 2) :
    empiricalLabelEntropy w = (countReward w - 1) * Real.log 2 := by
  generalize h0 : (w 0).2 = o0
  generalize h1 : (w 1).2 = o1
  fin_cases o0 <;> fin_cases o1 <;>
    norm_num [empiricalLabelEntropy, empiricalLabelLaw, countReward, ent,
      Fin.sum_univ_succ, Fin.reduceFinMk, h0, h1, Real.negMulLog, Real.log_div] <;>
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat] <;>
    norm_num [show (2 : Fin 4).val = 2 from rfl, show (2 : Fin 3).val = 2 from rfl,
      Real.negMulLog, Real.log_div] <;> ring

def expectedEmpiricalEntropy (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑ θ, prior θ * ∑ w, causalFiniteExperiment π.1 response 2 θ w * empiricalLabelEntropy w

theorem expectedEmpiricalEntropy_eq (π : ValidCausalPolicy Action Observation) :
    expectedEmpiricalEntropy π = (expectedCount π - 1) * Real.log 2 := by
  have hrow (θ : World) :
      (∑ w, causalFiniteExperiment π.1 response 2 θ w * empiricalLabelEntropy w) =
      ((∑ w, causalFiniteExperiment π.1 response 2 θ w * countReward w) - 1) * Real.log 2 := by
    simp only [empiricalLabelEntropy_eq, ← mul_assoc, mul_sub, mul_one]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    rw [(causalFiniteExperiment_valid π.1 π.2 response response_valid 2 θ).2]
  unfold expectedEmpiricalEntropy expectedCount
  simp only [hrow, ← mul_assoc, mul_sub, mul_one]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, KnownNoise.prior_valid.2]

theorem entropy_maximizers (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      expectedEmpiricalEntropy ρ ≤ expectedEmpiricalEntropy π) ↔ π.1 [] 0 = 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← count_maximizers π]
  simp only [expectedEmpiricalEntropy_eq, mul_le_mul_iff_left₀ hlog, sub_le_sub_iff_right]

theorem every_entropy_optimum_strictly_finitarily_dominated
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation,
      expectedEmpiricalEntropy ρ ≤ expectedEmpiricalEntropy π) :
    CausalFinitaryDominates response (purePolicy 0) π ∧
      ¬ CausalFinitaryDominates response π (purePolicy 0) :=
  noise_root_strictly_dominated π ((entropy_maximizers π).mp hopt)

/-- Attainment is explicit, so the universal optimizer statements are nonvacuous. -/
theorem noise_attains_count_and_entropy :
    (∀ ρ : ValidCausalPolicy Action Observation, expectedCount ρ ≤ expectedCount (purePolicy 1)) ∧
    (∀ ρ : ValidCausalPolicy Action Observation,
      expectedEmpiricalEntropy ρ ≤ expectedEmpiricalEntropy (purePolicy 1)) := by
  have h : (purePolicy 1).1 [] 0 = 0 := by simp [purePolicy, KnownNoise.purePolicy, detPolicy]
  exact ⟨(count_maximizers _).mpr h, (entropy_maximizers _).mpr h⟩

end
end IdExp.FirstVisitCount
