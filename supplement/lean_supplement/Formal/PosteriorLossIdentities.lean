import Formal.QuadraticReverseBound
import Formal.CrossingPartitionScores

/-!
# The posterior losses of an exact stochastic garbling

Information loss is the expected KL divergence from the source posterior to
the garbled posterior. The expectation uses the actual joint signal law,
not independent posterior draws. Positive joint mass implies posterior
absolute continuity; null pairs contribute zero. Natural-log and bit units
are explicit. The quadratic counterpart reuses the checked variance identity.
-/

namespace IdExp
open Finset
noncomputable section

universe u v
variable {Θ : Type v} {S T : Type u} [Fintype Θ] [Fintype S] [Fintype T]

/-- The source posterior is absolutely continuous with respect to the
garbled posterior on every positive-probability signal pair. -/
theorem posterior_garble_support (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (s : S) (t : T)
    (hst : 0 < garbleJoint α F G s t) (θ : Θ)
    (hz : finiteBayesPosterior α (finiteDecisionLaw F G) t θ = 0) :
    finiteBayesPosterior α F s θ = 0 := by
  have hFG := finiteDecisionLaw_valid F hF G hG
  have hg0 := (hG s (Set.mem_univ s)).1 t
  have hg : 0 < G s t := by
    by_contra hn
    have : G s t = 0 := le_antisymm (le_of_not_gt hn) hg0
    simp [garbleJoint, this] at hst
  have hzero : α θ * finiteDecisionLaw F G θ t = 0 := by
    rw [← finiteBayesMass_mul_posterior α hα.1 _ (fun θ t => (hFG θ).1 t), hz, mul_zero]
  have hle : F θ s * G s t ≤ finiteDecisionLaw F G θ t :=
    Finset.single_le_sum (fun z _ => mul_nonneg ((hF θ).1 z)
      ((hG z (Set.mem_univ z)).1 t)) (Finset.mem_univ s)
  have hz' : α θ * F θ s = 0 := by
    have ha := mul_le_mul_of_nonneg_left hle (hα.1 θ)
    rw [hzero] at ha
    have hn := mul_nonneg (hα.1 θ) ((hF θ).1 s)
    nlinarith
  rw [finiteBayesPosterior_eq_div, hz', zero_div]

/-- Expected posterior KL equals the information lost, in natural-log units. -/
theorem information_gap_eq_expected_posteriorKL [Nonempty S]
    (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) :
    finiteBayesInformation α F - finiteBayesInformation α (finiteDecisionLaw F G) =
      ∑ s, ∑ t, garbleJoint α F G s t *
        finiteKL (finiteBayesPosterior α F s)
          (finiteBayesPosterior α (finiteDecisionLaw F G) t) := by
  rw [← weighted_finiteKL_joint_eq α hα F hF G hG]
  have hFG := finiteDecisionLaw_valid F hF G hG
  have hterm (θ : Θ) (s : S) (t : T) :
      α θ * (jointForward F G θ (s, t) *
        Real.log (jointForward F G θ (s, t) /
          jointReverse F G (bayesReverseChannel α F G) θ (s, t))) =
      garbleJoint α F G s t * (finiteBayesPosterior α F s θ *
        Real.log (finiteBayesPosterior α F s θ /
          finiteBayesPosterior α (finiteDecisionLaw F G) t θ)) := by
    have hcoef : garbleJoint α F G s t * finiteBayesPosterior α F s θ =
        α θ * F θ s * G s t := by
      unfold garbleJoint
      rw [mul_right_comm, finiteBayesMass_mul_posterior α hα.1 F (fun θ s => (hF θ).1 s)]
    simp only [← mul_assoc]
    rw [hcoef]
    unfold jointForward jointReverse
    simp only [← mul_assoc]
    by_cases h : α θ * F θ s * G s t = 0
    · rw [h, zero_mul, zero_mul]
    · have hαF := (mul_ne_zero_iff.1 h).1
      have hg := (mul_ne_zero_iff.1 h).2
      have ha := (mul_ne_zero_iff.1 hαF).1
      have hf := (mul_ne_zero_iff.1 hαF).2
      have hap := lt_of_le_of_ne (hα.1 θ) (Ne.symm ha)
      have hfp := lt_of_le_of_ne ((hF θ).1 s) (Ne.symm hf)
      have hgp := lt_of_le_of_ne ((hG s (Set.mem_univ s)).1 t) (Ne.symm hg)
      have hm : finiteBayesMass α F s ≠ 0 := by
        have hle : α θ * F θ s ≤ finiteBayesMass α F s :=
          Finset.single_le_sum (fun c _ => mul_nonneg (hα.1 c) ((hF c).1 s))
            (Finset.mem_univ θ)
        exact ne_of_gt ((mul_pos hap hfp).trans_le hle)
      have hfgp : 0 < finiteDecisionLaw F G θ t := by
        have hle : F θ s * G s t ≤ finiteDecisionLaw F G θ t :=
          Finset.single_le_sum (fun z _ => mul_nonneg ((hF θ).1 z)
            ((hG z (Set.mem_univ z)).1 t)) (Finset.mem_univ s)
        exact (mul_pos hfp hgp).trans_le hle
      have hm' : finiteBayesMass α (finiteDecisionLaw F G) t ≠ 0 := by
        have hle : α θ * finiteDecisionLaw F G θ t ≤
            finiteBayesMass α (finiteDecisionLaw F G) t :=
          Finset.single_le_sum (fun c _ => mul_nonneg (hα.1 c) ((hFG c).1 t))
            (Finset.mem_univ θ)
        exact ne_of_gt ((mul_pos hap hfgp).trans_le hle)
      congr 2
      simp only [finiteBayesPosterior_eq_div, bayesReverseChannel, if_neg hm']
      field_simp
  simp only [finiteKL, Fintype.sum_prod_type, Finset.mul_sum]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact Finset.sum_comm

/-- The paper's bit-normalized version; both information and KL are divided
by `log 2`. This is not an unbounded log score inside a unit-range envelope. -/
theorem information_gap_bits_eq_expected_posteriorKL_bits [Nonempty S]
    (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) :
    (finiteBayesInformation α F - finiteBayesInformation α (finiteDecisionLaw F G)) /
        Real.log 2 =
      ∑ s, ∑ t, garbleJoint α F G s t *
        (finiteKL (finiteBayesPosterior α F s)
          (finiteBayesPosterior α (finiteDecisionLaw F G) t) / Real.log 2) := by
  rw [information_gap_eq_expected_posteriorKL α hα F hF G hG]
  simp only [Finset.sum_div, mul_div_assoc]

theorem quadratic_gap_eq_expected_posterior_sq (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    quadraticPosteriorScore α F - quadraticPosteriorScore α (finiteDecisionLaw F G) =
      ∑ s, ∑ t, garbleJoint α F G s t *
        ∑ θ, (finiteBayesPosterior α F s θ -
          finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 := by
  unfold quadraticPosteriorScore
  rw [sum_garbleJoint_sq_dist α hα F hF G hG]
  ring

end
end IdExp
