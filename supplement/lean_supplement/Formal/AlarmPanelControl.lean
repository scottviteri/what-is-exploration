import Formal.AlarmPanelFinite
import Formal.ControlChannelCapacity

/-! Literal sensor-channel empowerment on the shared alarm/panel interface.
The hypothetical channel input is the proposed action; its output excludes
the agent's copied action. -/
namespace IdExp.AlarmPanel.Control
open Finset
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def panelChannel : FiniteExperiment Action Observation := fun a => pairDist (a == 2)

theorem panelChannel_valid : IsFiniteExperiment panelChannel := fun a => pairDist_valid _

theorem pairDist_entropy (b : Bool) : ent (pairDist b) = Real.log 2 := by
  cases b <;> norm_num [ent,pairDist,Fin.sum_univ_succ,Real.negMulLog,Real.log_div] <;> ring

theorem panel_information (ν : Action → ℝ) (hν : IsDist ν) :
    finiteBayesInformation ν panelChannel = ent (finiteBayesMass ν panelChannel) - Real.log 2 := by
  rw [finiteBayesInformation_eq_ent_mass_sub ν hν panelChannel panelChannel_valid]
  simp only [panelChannel,pairDist_entropy,← sum_mul,hν.2,one_mul]

theorem panel_information_le (ν : Action → ℝ) (hν : IsDist ν) :
    finiteBayesInformation ν panelChannel ≤ Real.log 2 := by
  have hm : IsDist (finiteBayesMass ν panelChannel) := by
    constructor
    · exact finiteBayesMass_nonneg _ _ hν.1 (fun a o => (panelChannel_valid a).1 o)
    · unfold finiteBayesMass
      rw [sum_comm]
      simp only [← mul_sum,(panelChannel_valid _).2,mul_one,hν.2]
  have hh := ent_le_log_card _ hm
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at hh
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  rw [h4] at hh
  rw [panel_information ν hν]
  linarith

def panelInput (a : Action) : ℝ := if a = 0 then 0 else 1/2

theorem panelInput_valid : IsDist panelInput := by
  constructor
  · intro a; fin_cases a <;> norm_num [panelInput]
  · norm_num [panelInput,Fin.sum_univ_succ]

theorem panelInput_mass : finiteBayesMass panelInput panelChannel = uniformDist := by
  funext o
  fin_cases o <;> norm_num [finiteBayesMass,panelInput,panelChannel,pairDist,
    uniformDist,Fin.sum_univ_succ] <;>
    norm_num only [Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_succ,Fin.val_ofNat] <;> norm_num

theorem panelInput_information : finiteBayesInformation panelInput panelChannel = Real.log 2 := by
  rw [panel_information _ panelInput_valid,panelInput_mass,uniformDist_entropy]
  ring

theorem panel_capacity : capacity panelChannel = Real.log 2 := by
  have hm : IsMaxOn (fun ν => finiteBayesInformation ν panelChannel)
      (stdSimplex ℝ Action) panelInput := by
    apply isMaxOn_iff.2
    intro ν hν
    rw [panelInput_information]
    exact panel_information_le ν hν
  rw [capacity_eq_of_isMaxOn panelChannel panelInput_valid hm,panelInput_information]

theorem point_capacity (o : Observation) :
    capacity (fun _ : Action => pointDist o) = 0 := by
  have he : (fun _ : Action => pointDist o) = diracExp (fun _ : Action => o) := by
    funext a x
    simp [pointDist,diracExp,eq_comm]
  rw [he,capacity_dirac_const]

/-- Actual sensor-channel capacity at a visited physical history. -/
def localCapacity (θ : World) (h : History) : ℝ := capacity (response θ h)

theorem localCapacity_tail (θ : World) (h : History) (hh : h ≠ []) :
    localCapacity θ h = if h.length % 2 = 1 ∧ ¬ inspected h then Real.log 2 else 0 := by
  by_cases hp : h.length % 2 = 1
  · by_cases hi : inspected h
    · have he : response θ h = fun _ => pointDist 0 := by
        funext a o; simp [response,hh,hp,hi]
      simp [localCapacity,he,point_capacity,hp,hi]
    · have he : response θ h = panelChannel := by
        funext a o; simp [response,hh,hp,hi,panelChannel,play1]
      simp [localCapacity,he,panel_capacity,hp,hi]
  · have he : response θ h = fun _ => pointDist (monitorLabel θ ((h.length-2)/2)) := by
      funext a o; simp [response,hh,hp]
    simp [localCapacity,he,point_capacity,hp]

/-- Literal expected capacity of the next sensor channel at decision t. -/
def empowermentStage (π : ValidCausalPolicy Action Observation) (θ : World) (t : ℕ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Observation t,
    experiment π.1 t θ w * localCapacity θ (List.ofFn w)

theorem empowermentStage_zero (π : ValidCausalPolicy Action Observation) (θ : World) :
    empowermentStage π θ 0 = localCapacity θ [] := by
  simp [empowermentStage,experiment,causalFiniteExperiment,causalTraceProb,causalTraceProbFrom]

theorem inspected_ofFn (t : ℕ) (w : CausalFiniteTrace Action Observation (t+1)) :
    inspected (List.ofFn w) ↔ (w 0).1 = 0 := by
  rw [List.ofFn_succ]
  exact inspected_cons _ _ _

theorem empowermentStage_succ (π : ValidCausalPolicy Action Observation) (θ : World) (t : ℕ) :
    empowermentStage π θ (t+1) =
      if (t+1)%2 = 1 then (1-π.1 [] 0) * Real.log 2 else 0 := by
  have hl (w : CausalFiniteTrace Action Observation (t+1)) :
      localCapacity θ (List.ofFn w) =
        if (t+1)%2=1 ∧ (w 0).1 ≠ 0 then Real.log 2 else 0 := by
    rw [localCapacity_tail θ (List.ofFn w) (by simp)]
    simp only [List.length_ofFn,inspected_ofFn]
  simp only [empowermentStage,hl]
  by_cases ht : (t+1)%2=1
  · simp only [ht,true_and,ite_true]
    have hr := causalFiniteExperiment_root_action_mass response response_valid π t θ 0
    have hn := (experiment_valid π.1 π.2 (t+1) θ).2
    have he : (∑ w : CausalFiniteTrace Action Observation (t+1),
        if (w 0).1 ≠ 0 then experiment π.1 (t+1) θ w else 0) = 1-π.1 [] 0 := by
      have hs : (∑ w : CausalFiniteTrace Action Observation (t+1),
          if (w 0).1 = 0 then experiment π.1 (t+1) θ w else 0) +
          (∑ w : CausalFiniteTrace Action Observation (t+1),
          if (w 0).1 ≠ 0 then experiment π.1 (t+1) θ w else 0) =
          ∑ w : CausalFiniteTrace Action Observation (t+1), experiment π.1 (t+1) θ w := by
        rw [← sum_add_distrib]
        apply sum_congr rfl; intro w _
        by_cases ha : (w 0).1 = 0 <;> simp [ha]
      change (∑ w, if (w 0).1 = 0 then experiment π.1 (t+1) θ w else 0) = _ at hr
      rw [hr,hn] at hs
      linarith
    calc
      _ = (∑ w : CausalFiniteTrace Action Observation (t+1),
          if (w 0).1 ≠ 0 then experiment π.1 (t+1) θ w else 0) * Real.log 2 := by
        simp only [sum_mul]
        apply sum_congr rfl; intro w _
        split_ifs <;> ring
      _ = _ := by rw [he]
  · simp [ht]

/-- A two-decision visited-capacity score already forces the failed startup choice. -/
def empowermentTwo (π : ValidCausalPolicy Action Observation) (θ : World) : ℝ :=
  empowermentStage π θ 0 + empowermentStage π θ 1

theorem empowermentTwo_eq (π : ValidCausalPolicy Action Observation) (θ : World) :
    empowermentTwo π θ = localCapacity θ [] + (1-π.1 [] 0) * Real.log 2 := by
  simp only [empowermentTwo,empowermentStage_zero,empowermentStage_succ π θ 0]
  norm_num

theorem empowermentTwo_maximizer_iff (π : ValidCausalPolicy Action Observation) (θ : World) :
    (∀ ρ, empowermentTwo ρ θ ≤ empowermentTwo π θ) ↔ π.1 [] 0 = 0 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [empowermentTwo_eq,empowermentTwo_eq,noveltyPolicy_root] at hh
    nlinarith [(π.2 []).1 0]
  · intro h ρ
    rw [empowermentTwo_eq,empowermentTwo_eq,h]
    nlinarith [(ρ.2 []).1 0]

/-- Complete discounted visited sensor capacity, grouping each panel/monitor
pair while retaining its original time weight. -/
def empowermentDiscounted (γ : ℝ) (π : ValidCausalPolicy Action Observation) (θ : World) : ℝ :=
  empowermentStage π θ 0 + ∑' k : ℕ,
    (γ^(2*k+1) * empowermentStage π θ (2*k+1) +
     γ^(2*k+2) * empowermentStage π θ (2*k+2))

theorem empowermentDiscounted_eq (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) (θ : World) :
    empowermentDiscounted γ π θ = localCapacity θ [] +
      γ / (1-γ^2) * (1-π.1 [] 0) * Real.log 2 := by
  have hγ2 : γ^2 < 1 := by nlinarith
  have he (k : ℕ) :
      γ^(2*k+1) * empowermentStage π θ (2*k+1) +
      γ^(2*k+2) * empowermentStage π θ (2*k+2) =
      (γ^2)^k * (γ * (1-π.1 [] 0) * Real.log 2) := by
    rw [empowermentStage_succ π θ (2*k),
      show 2*k+2=(2*k+1)+1 by omega,empowermentStage_succ π θ (2*k+1)]
    have ho : (2*k+1)%2=1 := by omega
    have hz : (2*k+1+1)%2 ≠ 1 := by omega
    simp only [ho,hz,if_true,if_false,mul_zero,add_zero,pow_succ,pow_mul]
    ring
  simp only [empowermentDiscounted,he,empowermentStage_zero,tsum_mul_right,
    tsum_geometric_of_lt_one (sq_nonneg γ) hγ2]
  ring

theorem empowermentDiscounted_maximizer_iff (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) (θ : World) :
    (∀ ρ, empowermentDiscounted γ ρ θ ≤ empowermentDiscounted γ π θ) ↔ π.1 [] 0 = 0 := by
  have hγ2 : γ^2 < 1 := by nlinarith
  have hp : 0 < γ / (1-γ^2) := div_pos hγ0 (by linarith)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have hh := h noveltyPolicy
    rw [empowermentDiscounted_eq γ hγ0.le hγ1,empowermentDiscounted_eq γ hγ0.le hγ1,
      noveltyPolicy_root] at hh
    nlinarith [(π.2 []).1 0,mul_pos hp hl]
  · intro h ρ
    rw [empowermentDiscounted_eq γ hγ0.le hγ1,empowermentDiscounted_eq γ hγ0.le hγ1,h]
    nlinarith [(ρ.2 []).1 0,mul_pos hp hl]

/-- Average the complete capacity return under the study's common prior. -/
def priorEmpowermentDiscounted (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∫ θ, empowermentDiscounted γ π θ ∂AlarmPanelPrior.prior

theorem priorEmpowermentDiscounted_eq (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    priorEmpowermentDiscounted γ π =
      (localCapacity none [] + localCapacity (some 0) []) / 2 +
      γ / (1-γ^2) * (1-π.1 [] 0) * Real.log 2 := by
  unfold priorEmpowermentDiscounted
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    rw [empowermentDiscounted_eq γ hγ0 hγ1,empowermentDiscounted_eq γ hγ0 hγ1]
    rfl)]
  rw [empowermentDiscounted_eq γ hγ0 hγ1,empowermentDiscounted_eq γ hγ0 hγ1]
  ring

theorem priorEmpowermentDiscounted_maximizer_iff (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, priorEmpowermentDiscounted γ ρ ≤ priorEmpowermentDiscounted γ π) ↔ π.1 [] 0 = 0 := by
  rw [← empowermentDiscounted_maximizer_iff γ hγ0 hγ1 π none]
  simp only [priorEmpowermentDiscounted_eq γ hγ0.le hγ1,
    empowermentDiscounted_eq γ hγ0.le hγ1]
  constructor <;> intro h ρ <;> have hh := h ρ <;> linarith

end
end IdExp.AlarmPanel.Control
