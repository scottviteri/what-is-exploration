import Formal.FourBitMovementOptima
import Formal.PosteriorLossIdentities

/-! Full-world information and ordinary posterior Brier movement in the same
four-bit environment and with exactly the same uniform prior and policy class. -/
noncomputable section
namespace IdExp.FourBitPosterior
open Finset ScheduledReveal

inductive ControlKind | information | brier deriving DecidableEq

def potential : ControlKind → (World → ℝ) → ℝ
  | .information, p => -ent p
  | .brier, p => ∑ θ, (p θ)^2

def prefixPotential (kind : ControlKind) (π : Policy) (n : ℕ) : ℝ :=
  ∑ θ, prior θ * ∑ h : CausalFiniteTrace Action Observation n,
    record π n θ h * potential kind (posterior π n h)

def controlObjective (kind : ControlKind) (γ : ℝ) (π : Policy) : ℝ :=
  ∑' n, γ^n*(prefixPotential kind π (n+1)-prefixPotential kind π n)

/-- The Brier potential increment is the literal expected squared change of
successive posteriors of the actual retained history, including null records. -/
theorem brier_increment_eq_squared_movement (π : Policy) (n : ℕ) :
    prefixPotential .brier π (n+1) - prefixPotential .brier π n =
      ∑ h : CausalFiniteTrace Action Observation (n+1),
        finiteBayesMass prior (record π (n+1)) h *
          ∑ θ, (posterior π (n+1) h θ - posterior π n (Fin.init h) θ)^2 := by
  have hp (k : ℕ) : prefixPotential .brier π k =
      finiteBayesPotential posteriorQuadraticPotential prior (record π k) := by
    unfold prefixPotential finiteBayesPotential finiteBayesMass
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro h _
    rw [sum_mul]
    apply sum_congr rfl
    intro θ _
    simp only [potential, posteriorQuadraticPotential]
    ring
  have hg : finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
    causalFiniteExperiment_prefix π.1 π.2 response (ScheduledReveal.response_valid signal) n
  have he := quadratic_gap_eq_expected_posterior_sq prior prior_valid
    (record π (n+1)) (record_valid π (n+1)) (causalPrefixRule n)
    (causalPrefixRule_mem_stochasticRules n)
  rw [hg, quadraticPosteriorScore, quadraticPosteriorScore, ← hp, ← hp] at he
  simp only [garbleJoint, causalPrefixRule, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, sum_ite_eq', mem_univ, ↓reduceIte] at he
  convert he using 1 <;> ring

def fullControl : ControlKind → ℝ | .information => 4*Real.log 2 | .brier => 15/16

def partialControl : ControlKind → ℝ → ℝ
  | .information, γ => Real.log 2*(1+γ+γ^2)
  | .brier, γ => 1/16+γ/8+γ^2/4

theorem root_average (π : Policy) (n : ℕ) (f : Bool → ℝ) :
    (∑ θ, prior θ * ∑ h : CausalFiniteTrace Action Observation (n+1),
      record π (n+1) θ h * f (h 0).1) =
      fullProbability π*f true + (1-fullProbability π)*f false := by
  have he (θ : World) : (∑ h : CausalFiniteTrace Action Observation (n+1),
      record π (n+1) θ h * f (h 0).1) = ∑ a : Action, π.1 [] a * f a := by
    rw [ScheduledReveal.firstExpectation signal π.1 π.2 θ n (fun ao => f ao.1), Fintype.sum_prod_type]
    apply sum_congr rfl; intro a _
    calc _ = (π.1 [] a * f a) * ∑ o, response θ [] a o := by
          rw [mul_sum]; apply sum_congr rfl; intro o _; ring
      _ = _ := by rw [(ScheduledReveal.response_valid signal θ [] a).2, mul_one]
  simp only [he, ← sum_mul, prior_valid.2, one_mul, Fintype.sum_bool, probability_false,
    fullProbability]

 theorem cell_potential (kind : ControlKind) (b : Bool) (n : ℕ) (θ : World)
    (hc : cellSize signal b n θ ≠ 0) :
    potential kind (cellPosterior signal b n θ) =
      match kind with
      | .information => -Real.log (cellSize signal b n θ)
      | .brier => 1 / cellSize signal b n θ := by
  have hsum (c : ℝ) : (∑ η : World, if Agree signal b n θ η then c else 0) =
      cellSize signal b n θ * c := by
    rw [cellSize, sum_mul]
    apply sum_congr rfl; intro η _; split <;> ring
  cases kind
  · have he (η : World) : Real.negMulLog (cellPosterior signal b n θ η) =
        if Agree signal b n θ η then -(1/cellSize signal b n θ)*Real.log (1/cellSize signal b n θ) else 0 := by
      unfold cellPosterior
      split <;> simp [Real.negMulLog]
    simp only [potential, ent, he]
    rw [hsum, one_div, Real.log_inv]
    field_simp
  · simp only [potential, cellPosterior, ite_pow, zero_pow (by decide : 2≠0)]
    rw [hsum]
    field_simp

 theorem cell_potential_full (kind : ControlKind) (n : ℕ) (θ : World) :
    potential kind (cellPosterior signal true (n+1) θ) =
      match kind with | .information => 0 | .brier => 1 := by
    rw [cell_potential kind true (n+1) θ (by rw [size_full]; norm_num), size_full]
    cases kind <;> norm_num

 def cellMass (n : ℕ) : ℝ := if n=1 then 8 else if n=2 then 4 else 2
 theorem size_partial (n : ℕ) (θ : World) : cellSize signal false (n+1) θ = cellMass (n+1) := by
   rcases n with _ | n
   · simpa [cellMass] using size_partial_one θ
   rcases n with _ | n
   · simpa [cellMass] using size_partial_two θ
   · have he : cellSize signal false (n+2+1) θ = cellSize signal false 3 θ := by
       simp only [cellSize, agree_after_three (n+2+1) (by omega)]
     rw [he, size_partial_three]
     simp [cellMass, show n+2+1≠1 by omega, show n+2+1≠2 by omega]

 def partialPotential (kind : ControlKind) (n : ℕ) : ℝ :=
   match kind with
   | .information => -Real.log (cellMass n)
   | .brier => 1/cellMass n
 theorem prefix_potential_succ (kind : ControlKind) (π : Policy) (n : ℕ) :
     prefixPotential kind π (n+1) =
       fullProbability π*(match kind with | .information => 0 | .brier => 1) +
       (1-fullProbability π)*partialPotential kind (n+1) := by
   have he (θ : World) (h : CausalFiniteTrace Action Observation (n+1)) :
       record π (n+1) θ h * potential kind (posterior π (n+1) h) =
       record π (n+1) θ h * (if (h 0).1 then
         (match kind with | .information => 0 | .brier => 1) else partialPotential kind (n+1)) := by
     by_cases hh : record π (n+1) θ h=0
     · simp [hh]
     · have hp : posterior π (n+1) h = cellPosterior signal (h 0).1 (n+1) θ := by
         funext η; exact posterior_cell signal π.1 n θ h hh η
       rw [hp]
       cases hb : (h 0).1
       · have hc : cellSize signal false (n+1) θ ≠ 0 := by
           rw [size_partial]; unfold cellMass; split <;> norm_num; split <;> norm_num
         rw [cell_potential kind false (n+1) θ hc, size_partial]
         rfl
       · rw [cell_potential_full]; rfl
   simp only [prefixPotential, he]
   cases kind
   · simpa only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte] using
       root_average π n (fun b => if b then 0 else partialPotential .information (n+1))
   · simpa only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte] using
       root_average π n (fun b => if b then 1 else partialPotential .brier (n+1))

 theorem log_constants : Real.log (4:ℝ)=2*Real.log 2 ∧
     Real.log (8:ℝ)=3*Real.log 2 ∧ Real.log (16:ℝ)=4*Real.log 2 := by
   constructor
   · have h := Real.log_pow (2:ℝ) 2; norm_num at h; exact h
   constructor
   · have h := Real.log_pow (2:ℝ) 3; norm_num at h; exact h
   · have h := Real.log_pow (2:ℝ) 4; norm_num at h; exact h

 theorem prefix_potential_zero (kind : ControlKind) (π : Policy) :
     prefixPotential kind π 0 = match kind with
       | .information => -4*Real.log 2 | .brier => 1/16 := by
   have he (θ : World) (h : CausalFiniteTrace Action Observation 0) : record π 0 θ h=1 := by
     simp [record, ScheduledReveal.record, causalFiniteExperiment, causalTraceProb,
       causalTraceProbFrom, List.ofFn_zero]
   simp only [prefixPotential, posterior_root, he, one_mul, sum_const,
     Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one, one_smul,
     ← sum_mul, prior_valid.2, one_mul]
   cases kind <;> norm_num [potential, ent, prior, uniform, Real.negMulLog,
     Real.log_div, log_constants.2.2] <;> ring

 theorem control_after_three (kind : ControlKind) (π : Policy) (n : ℕ) (hn : 3 ≤ n) :
     prefixPotential kind π (n+1)-prefixPotential kind π n = 0 := by
   obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
   simp [prefix_potential_succ, partialPotential, cellMass, show m≠0 by omega, show m+1≠1 by omega,
     show m+1≠2 by omega, show m+1+1≠1 by omega, show m+1+1≠2 by omega]

/-- Exact complete and discounted information/Brier returns. These are potential
increments: they are not the predictive Square score in the source's table. -/
theorem controlObjective_eq (kind : ControlKind) (γ : ℝ) (π : Policy) :
    controlObjective kind γ π = fullProbability π*fullControl kind +
      (1-fullProbability π)*partialControl kind γ := by
  have he : (∑' n, γ^n*(prefixPotential kind π (n+1)-prefixPotential kind π n)) =
      ∑ n ∈ range 3, γ^n*(prefixPotential kind π (n+1)-prefixPotential kind π n) := by
    apply tsum_eq_sum
    intro n hn
    rw [control_after_three kind π n (by simpa only [mem_range, not_lt] using hn), mul_zero]
  rw [controlObjective, he]
  norm_num only [sum_range_succ, sum_range_zero, pow_zero, one_mul, pow_one, zero_add]
  rw [prefix_potential_succ, prefix_potential_succ, prefix_potential_succ, prefix_potential_zero]
  cases kind <;> norm_num [fullControl, partialControl, partialPotential, cellMass,
    log_constants.1, log_constants.2.1] <;> ring

theorem control_gap (kind : ControlKind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    partialControl kind γ < fullControl kind := by
  have hsq : γ^2 ≤ 1 := pow_le_one₀ hγ hγ1
  cases kind
  · simp only [partialControl, fullControl]
    have hl : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
    nlinarith
  · simp only [partialControl, fullControl]; nlinarith

theorem control_eq_max_iff (kind : ControlKind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy) :
    controlObjective kind γ π=fullControl kind ↔ fullProbability π=1 := by
  rw [controlObjective_eq]
  have hg := control_gap kind γ hγ hγ1
  constructor
  · intro he; nlinarith
  · intro he; simp [he]

theorem control_optimal_deficiency_zero (kind : ControlKind) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy)
    (hopt : controlObjective kind γ π=fullControl kind) (n : ℕ) (hn : 3 ≤ n+1) :
    finiteDeficiency (record π (n+1)) (diracExp (id : World → World))=0 := by
  rw [deficiency_exact π n hn, (control_eq_max_iff kind γ hγ hγ1 π).mp hopt]
  norm_num

end IdExp.FourBitPosterior
