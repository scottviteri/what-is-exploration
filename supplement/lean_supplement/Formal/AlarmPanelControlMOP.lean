import Formal.AlarmPanelControl

/-!
# Historical history-state entropy optimizer at discount one half

This is the retained alarm/history calculation formerly attributed to MOP.
The local score is action entropy plus fixed-world next-observation entropy,
with the complete observed history as the policy input. All entropies are in nats.
The actual causal discounted return is constructed below.

The selected MOP comparison was replaced on 23 September 2026 because this
history-state setting does not establish correspondence to the source's physical
MDP states. See `MOPFiniteMDP.lean` and ledger `prop:mop-finite-mdp` for the
five-state, legal-action, stationary-policy result with READ deficiency 1/3.
The formulas and theorems here retain their original scope; they are not that
selected MOP result. See `claim:alarm-panel-mop-all-discounts` for their status.
-/
namespace IdExp.AlarmPanel.MOP
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def tilt (a : Action) : ℝ := if a = 0 then 0 else (5/3 : ℝ) * Real.log 2

def normalizer : ℝ := ∑ a : Action, Real.exp (tilt a)

def optimizerRow (a : Action) : ℝ := Real.exp (tilt a) / normalizer

theorem normalizer_eq : normalizer = 1 + 2 * Real.exp ((5/3 : ℝ) * Real.log 2) := by
  norm_num [normalizer,tilt,Fin.sum_univ_succ]

theorem normalizer_pos : 0 < normalizer := by
  rw [normalizer_eq]
  positivity

theorem optimizerRow_pos (a : Action) : 0 < optimizerRow a :=
  div_pos (Real.exp_pos _) normalizer_pos

theorem optimizerRow_valid : IsDist optimizerRow := by
  refine ⟨fun a => (optimizerRow_pos a).le, ?_⟩
  simp only [optimizerRow,← sum_div]
  exact div_self (ne_of_gt normalizer_pos)

theorem log_optimizerRow (a : Action) :
    Real.log (optimizerRow a) = tilt a - Real.log normalizer := by
  rw [optimizerRow,Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt normalizer_pos),
    Real.log_exp]

def tiltedEntropy (p : Action → ℝ) : ℝ := ent p + ∑ a, p a * tilt a

theorem finiteKL_optimizerRow (p : Action → ℝ) (hp : IsDist p) :
    finiteKL p optimizerRow = Real.log normalizer - tiltedEntropy p := by
  unfold finiteKL
  simp_rw [mul_log_div_eq _ _ (ne_of_gt (optimizerRow_pos _)),log_optimizerRow]
  simp only [mul_sub,sum_sub_distrib,← sum_mul,hp.2,one_mul,
    tiltedEntropy,ent,Real.negMulLog,neg_mul,sum_neg_distrib]
  ring

theorem tiltedEntropy_le (p : Action → ℝ) (hp : IsDist p) :
    tiltedEntropy p ≤ Real.log normalizer := by
  have hk := finiteTV_sq_le_finiteKL_half p optimizerRow hp optimizerRow_valid
    (fun a h => False.elim ((ne_of_gt (optimizerRow_pos a)) h))
  rw [finiteKL_optimizerRow p hp] at hk
  nlinarith [sq_nonneg (finiteTV p optimizerRow)]

theorem tiltedEntropy_eq_iff (p : Action → ℝ) (hp : IsDist p) :
    tiltedEntropy p = Real.log normalizer ↔ p = optimizerRow := by
  constructor
  · intro he
    have hk := finiteTV_sq_le_finiteKL_half p optimizerRow hp optimizerRow_valid
      (fun a h => False.elim ((ne_of_gt (optimizerRow_pos a)) h))
    rw [finiteKL_optimizerRow p hp,he] at hk
    apply (finiteTV_eq_zero_iff p optimizerRow).mp
    nlinarith [finiteTV_nonneg p optimizerRow]
  · rintro rfl
    have he : finiteKL optimizerRow optimizerRow = 0 := by
      unfold finiteKL
      apply sum_eq_zero; intro a _
      rw [div_self (ne_of_gt (optimizerRow_pos a)),Real.log_one,mul_zero]
    rw [finiteKL_optimizerRow _ optimizerRow_valid] at he
    linarith

/-- The root objective after optimizing every tail action entropy. -/
def rootScore (p : Action → ℝ) : ℝ :=
  ent p + (p 0 + (1-p 0) * (8/3 : ℝ)) * Real.log 2

theorem rootScore_eq (p : Action → ℝ) (hp : IsDist p) :
    rootScore p = Real.log 2 + tiltedEntropy p := by
  have hs := hp.2
  simp only [Fin.sum_univ_three] at hs
  unfold rootScore tiltedEntropy tilt
  simp only [Fin.sum_univ_succ]
  norm_num
  norm_num only [Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.val_ofNat]
  norm_num
  nlinarith [congrArg (fun x : ℝ => x * Real.log 2) hs]

theorem rootScore_maximizer_iff (p : Action → ℝ) (hp : IsDist p) :
    (∀ q, IsDist q → rootScore q ≤ rootScore p) ↔ p = optimizerRow := by
  constructor
  · intro h
    apply (tiltedEntropy_eq_iff p hp).mp
    have hq := h optimizerRow optimizerRow_valid
    rw [rootScore_eq p hp,rootScore_eq _ optimizerRow_valid,
      (tiltedEntropy_eq_iff _ optimizerRow_valid).mpr rfl] at hq
    exact le_antisymm (tiltedEntropy_le p hp) (by linarith)
  · rintro rfl q hq
    rw [rootScore_eq q hq,rootScore_eq _ optimizerRow_valid,
      (tiltedEntropy_eq_iff _ optimizerRow_valid).mpr rfl]
    exact add_le_add_right (tiltedEntropy_le q hq) _

theorem optimizer_inspection :
    optimizerRow 0 = 1 / (1 + 2 * Real.exp ((5/3 : ℝ) * Real.log 2)) := by
  rw [optimizerRow,tilt,if_pos rfl,Real.exp_zero,normalizer_eq]

theorem optimizer_inspection_rpow :
    optimizerRow 0 = 1 / (1 + 4 * (2 : ℝ)^((2/3 : ℝ))) := by
  rw [optimizer_inspection,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  have he : Real.exp ((5/3 : ℝ) * Real.log 2) =
      2 * Real.exp (Real.log 2 * (2/3 : ℝ)) := by
    rw [show (5/3 : ℝ)*Real.log 2 = Real.log 2 + Real.log 2 * (2/3 : ℝ) by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [he]
  ring

theorem optimizer_inspection_bounds : 0 < optimizerRow 0 ∧ optimizerRow 0 < 1 := by
  refine ⟨optimizerRow_pos _, ?_⟩
  rw [optimizer_inspection]
  apply (div_lt_one (by positivity)).mpr
  linarith [Real.exp_pos ((5/3 : ℝ) * Real.log 2)]

/-- Physical transition entropy is evaluated in each actual fixed world. -/
def localReward (π : ValidCausalPolicy Action Observation) (θ : World) (h : History) : ℝ :=
  ent (π.1 h) + ∑ a, π.1 h a * ent (response θ h a)

def stage (π : ValidCausalPolicy Action Observation) (θ : World) (t : ℕ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Observation t,
    experiment π.1 t θ w * localReward π θ (List.ofFn w)

theorem pointDist_entropy (o : Observation) : ent (pointDist o) = 0 := by
  apply sum_eq_zero; intro p _
  unfold pointDist
  split_ifs <;> simp

theorem transitionEntropy_root (θ : World) (a : Action) :
    ent (response θ [] a) = if a = 0 then Real.log 2 else 2*Real.log 2 := by
  by_cases ha : a = 0
  · have hr : response θ [] a = pairDist θ.isSome := by
      funext o; simp [response,inspect,ha]
    rw [hr]
    simp [ha,Control.pairDist_entropy]
  · have hr : response θ [] a = uniformDist := by
      funext o; simp [response,inspect,ha]
    simp [hr,ha,uniformDist_entropy]

theorem transitionEntropy_tail (θ : World) (h : History) (hh : h ≠ []) (a : Action) :
    ent (response θ h a) = Control.localCapacity θ h := by
  rw [Control.localCapacity_tail θ h hh]
  by_cases ht : h.length % 2 = 1
  · by_cases hi : inspected h
    · have hr : response θ h a = pointDist 0 := by
        funext o; simp [response,hh,ht,hi]
      simp [hr,ht,hi,pointDist_entropy]
    · have hr : response θ h a = pairDist (a == play1) := by
        funext o; simp [response,hh,ht,hi]
      simp [hr,ht,hi,Control.pairDist_entropy]
  · have hr : response θ h a = pointDist (monitorLabel θ ((h.length-2)/2)) := by
      funext o; simp [response,hh,ht]
    simp [hr,ht,pointDist_entropy]

theorem localReward_root (π : ValidCausalPolicy Action Observation) (θ : World) :
    localReward π θ [] = ent (π.1 []) + (2-π.1 [] 0)*Real.log 2 := by
  simp only [localReward,transitionEntropy_root,Fin.sum_univ_succ]
  have hs := (π.2 []).2
  simp only [Fin.sum_univ_three] at hs
  norm_num
  norm_num only [Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.val_ofNat]
  norm_num
  nlinarith [congrArg (fun x : ℝ => x * Real.log 2) hs]

theorem localReward_tail (π : ValidCausalPolicy Action Observation) (θ : World)
    (h : History) (hh : h ≠ []) :
    localReward π θ h = ent (π.1 h) + Control.localCapacity θ h := by
  simp only [localReward,transitionEntropy_tail θ h hh,← sum_mul,(π.2 h).2,one_mul]

theorem stage_nonneg (π : ValidCausalPolicy Action Observation) (θ : World) (t : ℕ) :
    0 ≤ stage π θ t := by
  apply sum_nonneg; intro w _
  apply mul_nonneg ((experiment_valid π.1 π.2 t θ).1 w)
  apply add_nonneg (ent_nonneg_of_isDist _ (π.2 _))
  apply sum_nonneg; intro a _
  exact mul_nonneg ((π.2 _).1 a) (ent_nonneg_of_isDist _ (response_valid θ _ a))

theorem stage_zero (π : ValidCausalPolicy Action Observation) (θ : World) :
    stage π θ 0 = ent (π.1 []) + (2-π.1 [] 0)*Real.log 2 := by
  simp [stage,experiment,causalFiniteExperiment,causalTraceProb,causalTraceProbFrom,localReward_root]

theorem stage_succ_le (π : ValidCausalPolicy Action Observation) (θ : World) (t : ℕ) :
    stage π θ (t+1) ≤ Real.log 3 + Control.empowermentStage π θ (t+1) := by
  have hlocal (w : CausalFiniteTrace Action Observation (t+1)) :
      localReward π θ (List.ofFn w) ≤ Real.log 3 + Control.localCapacity θ (List.ofFn w) := by
    rw [localReward_tail _ _ _ (by simp)]
    exact add_le_add (by simpa using ent_le_log_card _ (π.2 (List.ofFn w))) le_rfl
  calc
    _ ≤ ∑ w : CausalFiniteTrace Action Observation (t+1),
        experiment π.1 (t+1) θ w * (Real.log 3 + Control.localCapacity θ (List.ofFn w)) := by
      apply sum_le_sum; intro w _
      exact mul_le_mul_of_nonneg_left (hlocal w) ((experiment_valid π.1 π.2 (t+1) θ).1 w)
    _ = _ := by
      simp only [mul_add,sum_add_distrib,← sum_mul,(experiment_valid π.1 π.2 (t+1) θ).2,one_mul,
        Control.empowermentStage]

/-- Both actions at each panel/monitor pair are scored with their original
half-discount weights. Grouping adjacent terms does not omit any decision. -/
def pairedStage (π : ValidCausalPolicy Action Observation) (θ : World) (k : ℕ) : ℝ :=
  (1/2 : ℝ) * stage π θ (2*k+1) + (1/4 : ℝ) * stage π θ (2*k+2)

def tailBound (π : ValidCausalPolicy Action Observation) : ℝ :=
  (3/4 : ℝ)*Real.log 3 + (1/2 : ℝ)*(1-π.1 [] 0)*Real.log 2

theorem pairedStage_nonneg (π : ValidCausalPolicy Action Observation) (θ : World) (k : ℕ) :
    0 ≤ pairedStage π θ k := by
  exact add_nonneg (mul_nonneg (by norm_num) (stage_nonneg π θ _))
    (mul_nonneg (by norm_num) (stage_nonneg π θ _))

theorem pairedStage_le (π : ValidCausalPolicy Action Observation) (θ : World) (k : ℕ) :
    pairedStage π θ k ≤ tailBound π := by
  have hodd := stage_succ_le π θ (2*k)
  have heven := stage_succ_le π θ (2*k+1)
  simp only [Control.empowermentStage_succ] at hodd heven
  have ho : (2*k+1)%2=1 := by omega
  have he : (2*k+1+1)%2 ≠ 1 := by omega
  simp only [ho,he,if_true,if_false,add_zero] at hodd heven
  change stage π θ (2*k+2) ≤ Real.log 3 at heven
  unfold pairedStage tailBound
  linarith

/-- Complete gamma=1/2 MOP return, with adjacent tail stages grouped. -/
def objective (π : ValidCausalPolicy Action Observation) (θ : World) : ℝ :=
  stage π θ 0 + ∑' k : ℕ, (1/4 : ℝ)^k * pairedStage π θ k

theorem objective_le (π : ValidCausalPolicy Action Observation) (θ : World) :
    objective π θ ≤ rootScore (π.1 []) + Real.log 3 := by
  have hs := summable_discounted_of_bounded (γ := (1/4 : ℝ))
    (by norm_num) (by norm_num) (pairedStage_nonneg π θ) (pairedStage_le π θ)
  have hu : Summable (fun k : ℕ => (1/4 : ℝ)^k * tailBound π) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).mul_right _
  have hb := Summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (pairedStage_le π θ k) (by positivity)) hs hu
  simp only [tsum_mul_right,tsum_geometric_of_lt_one
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)] at hb
  unfold objective
  rw [stage_zero]
  unfold rootScore tailBound at *
  linarith

/-- Arbitrary root row, followed by maximal-entropy actions at every history. -/
def uniformTail (p : Action → ℝ) (hp : IsDist p) : ValidCausalPolicy Action Observation :=
  ⟨fun h => if h = [] then p else uniformPrior Action, by
    intro h
    by_cases hh : h = []
    · simpa [hh] using hp
    · simpa [hh] using (isDist_uniformPrior (Θ := Action))⟩

theorem uniformTail_stage (p : Action → ℝ) (hp : IsDist p) (θ : World) (t : ℕ) :
    stage (uniformTail p hp) θ (t+1) =
      Real.log 3 + Control.empowermentStage (uniformTail p hp) θ (t+1) := by
  have hl (w : CausalFiniteTrace Action Observation (t+1)) :
      localReward (uniformTail p hp) θ (List.ofFn w) =
        Real.log 3 + Control.localCapacity θ (List.ofFn w) := by
    rw [localReward_tail _ _ _ (by simp)]
    simp [uniformTail,ent_uniformPrior]
  simp only [stage,hl,mul_add,sum_add_distrib,← sum_mul,
    (experiment_valid (uniformTail p hp).1 (uniformTail p hp).2 (t+1) θ).2,one_mul,
    Control.empowermentStage]

theorem uniformTail_pair (p : Action → ℝ) (hp : IsDist p) (θ : World) (k : ℕ) :
    pairedStage (uniformTail p hp) θ k = tailBound (uniformTail p hp) := by
  unfold pairedStage
  rw [uniformTail_stage p hp θ (2*k),show 2*k+2=(2*k+1)+1 by omega,
    uniformTail_stage p hp θ (2*k+1)]
  simp only [Control.empowermentStage_succ]
  have ho : (2*k+1)%2=1 := by omega
  have he : (2*k+1+1)%2 ≠ 1 := by omega
  simp only [ho,he,if_true,if_false]
  unfold tailBound
  ring

theorem uniformTail_objective (p : Action → ℝ) (hp : IsDist p) (θ : World) :
    objective (uniformTail p hp) θ = rootScore p + Real.log 3 := by
  simp only [objective,uniformTail_pair,tsum_mul_right,tsum_geometric_of_lt_one
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1),stage_zero]
  simp only [uniformTail,if_true]
  unfold rootScore tailBound
  simp only [uniformTail,if_true]
  ring

def optimizer : ValidCausalPolicy Action Observation := uniformTail optimizerRow optimizerRow_valid

theorem optimizer_maximizes (π : ValidCausalPolicy Action Observation) (θ : World) :
    objective π θ ≤ objective optimizer θ := by
  rw [optimizer,uniformTail_objective]
  exact (objective_le π θ).trans (add_le_add
    ((rootScore_maximizer_iff _ optimizerRow_valid).mpr rfl _ (π.2 [])) le_rfl)

theorem maximizing_root (π : ValidCausalPolicy Action Observation) (θ : World)
    (hmax : ∀ ρ, objective ρ θ ≤ objective π θ) : π.1 [] = optimizerRow := by
  apply (rootScore_maximizer_iff _ (π.2 [])).mp
  intro q hq
  have hl := hmax (uniformTail q hq)
  rw [uniformTail_objective] at hl
  have hu := objective_le π θ
  linarith

/-- Summability of the ordinary ungrouped half-discount series. -/
theorem discountedStage_summable (π : ValidCausalPolicy Action Observation) (θ : World) :
    Summable (fun t : ℕ => (1/2 : ℝ)^t * stage π θ t) := by
  apply summable_discounted_of_bounded (B := max (stage π θ 0) (Real.log 3 + Real.log 2))
    (by norm_num) (by norm_num) (stage_nonneg π θ)
  intro t
  cases t with
  | zero => exact le_max_left _ _
  | succ n =>
    apply le_trans (stage_succ_le π θ n)
    apply le_trans _ (le_max_right _ _)
    apply add_le_add_right
    rw [Control.empowermentStage_succ]
    split_ifs
    · nlinarith [(π.2 []).1 0,Real.log_pos (by norm_num : (1:ℝ)<2)]
    · exact (Real.log_pos (by norm_num : (1:ℝ)<2)).le

/-- The grouped definition is exactly the ordinary sum over every decision. -/
theorem ordinary_discounted_eq (π : ValidCausalPolicy Action Observation) (θ : World) :
    (∑' t : ℕ, (1/2 : ℝ)^t * stage π θ t) = objective π θ := by
  have hs := discountedStage_summable π θ
  let f : ℕ → ℝ := fun t => (1/2 : ℝ)^(t+1) * stage π θ (t+1)
  have ht : Summable f := hs.comp_injective (fun a b h => Nat.add_right_cancel h)
  have he : Summable (fun k : ℕ => f (2*k)) := ht.comp_injective (by
    intro a b h
    change 2*a = 2*b at h
    omega)
  have ho : Summable (fun k : ℕ => f (2*k+1)) := ht.comp_injective (by
    intro a b h
    change 2*a+1 = 2*b+1 at h
    omega)
  have hsplit : (∑' k, f k) = ∑' k, (f (2*k) + f (2*k+1)) := by
    rw [he.tsum_add ho]
    exact (tsum_even_add_odd he ho).symm
  calc
    _ = stage π θ 0 + ∑' k, f k := by
      rw [hs.tsum_eq_zero_add]
      simp only [pow_zero,one_mul]
      rfl
    _ = stage π θ 0 + ∑' k, (f (2*k) + f (2*k+1)) := by rw [hsplit]
    _ = objective π θ := by
      unfold objective
      congr 1
      apply tsum_congr; intro k
      dsimp [f]
      simp only [pairedStage,pow_add,pow_mul,pow_one]
      norm_num
      ring

open MeasureTheory

theorem objective_nonneg (π : ValidCausalPolicy Action Observation) (θ : World) :
    0 ≤ objective π θ := by
  exact add_nonneg (stage_nonneg π θ 0)
    (tsum_nonneg (fun k => mul_nonneg (by positivity) (pairedStage_nonneg π θ k)))

theorem objective_integrable (π : ValidCausalPolicy Action Observation) :
    Integrable (objective π) AlarmPanelPrior.prior := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (rootScore (π.1 []) + Real.log 3)
  apply Filter.Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs,abs_of_nonneg (objective_nonneg π θ)]
  exact objective_le π θ

/-- The same fixed full-support world prior as every other study row. -/
def priorObjective (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∫ θ, objective π θ ∂AlarmPanelPrior.prior

theorem priorObjective_le (π : ValidCausalPolicy Action Observation) :
    priorObjective π ≤ rootScore (π.1 []) + Real.log 3 := by
  have h := integral_mono (objective_integrable π)
    (integrable_const (rootScore (π.1 []) + Real.log 3)) (objective_le π)
  simpa [priorObjective] using h

theorem uniformTail_priorObjective (p : Action → ℝ) (hp : IsDist p) :
    priorObjective (uniformTail p hp) = rootScore p + Real.log 3 := by
  simp [priorObjective,uniformTail_objective]

theorem optimizer_maximizes_prior (π : ValidCausalPolicy Action Observation) :
    priorObjective π ≤ priorObjective optimizer := by
  rw [optimizer,uniformTail_priorObjective]
  exact (priorObjective_le π).trans (add_le_add
    ((rootScore_maximizer_iff _ optimizerRow_valid).mpr rfl _ (π.2 [])) le_rfl)

theorem maximizing_prior_root (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ, priorObjective ρ ≤ priorObjective π) : π.1 [] = optimizerRow := by
  apply (rootScore_maximizer_iff _ (π.2 [])).mp
  intro q hq
  have hl := hmax (uniformTail q hq)
  rw [uniformTail_priorObjective] at hl
  have hu := priorObjective_le π
  linarith

theorem optimizer_prior_value :
    priorObjective optimizer = Real.log 2 +
      Real.log (1 + 2 * Real.exp ((5/3 : ℝ) * Real.log 2)) + Real.log 3 := by
  rw [optimizer,uniformTail_priorObjective,rootScore_eq _ optimizerRow_valid,
    (tiltedEntropy_eq_iff _ optimizerRow_valid).mpr rfl,normalizer_eq]

theorem maximizing_prior_inspection (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ, priorObjective ρ ≤ priorObjective π) :
    π.1 [] 0 = 1 / (1 + 4 * (2 : ℝ)^((2/3 : ℝ))) := by
  rw [maximizing_prior_root π hmax,optimizer_inspection_rpow]

end
end IdExp.AlarmPanel.MOP
