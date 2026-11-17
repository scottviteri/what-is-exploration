import Formal.PairedAlarmBlockComplete
import Formal.InformationDeficiencyContinuity
import Formal.AlarmPanelPrior

/-!
# Literal full-observation-block empowerment on the coinless alarm

A probe imposes its open-loop actions and retains all resulting observations.
The channel executes the actual response law, including startup. After a
nonempty history its capacity is zero in INSPECT mode and n bits in PLAY mode.
-/

noncomputable section
namespace IdExp.PairedAlarm.BlockChannel
open Finset MeasureTheory
open scoped Classical

section Generic
variable {I J X : Type*} [Fintype I] [Fintype J] [Fintype X]

def pushPrior (f : I → J) (ν : I → ℝ) : J → ℝ := fun j =>
  ∑ i, if f i = j then ν i else 0

theorem pushPrior_sum (f : I → J) (ν : I → ℝ) (g : J → ℝ) :
    ∑ j, pushPrior f ν j * g j = ∑ i, ν i * g (f i) := by
  classical
  simp only [pushPrior, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

theorem pushPrior_valid (f : I → J) (ν : I → ℝ) (hν : IsDist ν) :
    IsDist (pushPrior f ν) := by
  classical
  constructor
  · intro j
    exact sum_nonneg fun i _ => by split <;> simp_all [hν.1 i]
  · simpa using pushPrior_sum f ν (fun _ => 1) |>.trans (by simpa using hν.2)

theorem information_precomp (E : FiniteExperiment J X) (hE : IsFiniteExperiment E)
    (f : I → J) (ν : I → ℝ) (hν : IsDist ν) :
    finiteBayesInformation ν (fun i => E (f i)) =
      finiteBayesInformation (pushPrior f ν) E := by
  rw [finiteBayesInformation_eq_ent_mass_sub ν hν _ (fun i => hE (f i)),
    finiteBayesInformation_eq_ent_mass_sub _ (pushPrior_valid f ν hν) E hE]
  have hm : finiteBayesMass (pushPrior f ν) E = finiteBayesMass ν (fun i => E (f i)) := by
    funext x
    exact pushPrior_sum f ν (fun j => E j x)
  rw [hm, pushPrior_sum]

variable [Nonempty I] [Nonempty J]

theorem capacity_precomp_le (E : FiniteExperiment J X) (hE : IsFiniteExperiment E)
    (f : I → J) : capacity (fun i => E (f i)) ≤ capacity E := by
  obtain ⟨ν, hν, hmax⟩ := exists_capacity_achieving _ (fun i => hE (f i))
  rw [capacity_eq_of_isMaxOn _ hν hmax, information_precomp E hE f ν hν]
  exact information_le_capacity E hE (pushPrior_valid f ν hν)

theorem capacity_precomp_surjective (E : FiniteExperiment J X) (hE : IsFiniteExperiment E)
    (f : I → J) (hf : Function.Surjective f) :
    capacity (fun i => E (f i)) = capacity E := by
  apply le_antisymm (capacity_precomp_le E hE f)
  let g := Function.surjInv hf
  have hg : ∀ j, f (g j) = j := Function.surjInv_eq hf
  have hp := capacity_precomp_le (fun i => E (f i)) (fun i => hE (f i)) g
  simpa only [hg] using hp

/-- An exact decoder makes a channel as informative as its input. -/
theorem capacity_of_decoder [Nonempty X] (E : FiniteExperiment I X)
    (hE : IsFiniteExperiment E) (decode : X → I)
    (hsupport : ∀ i x, E i x ≠ 0 → decode x = i) :
    capacity E = Real.log (Fintype.card I) := by
  classical
  have hdec : finiteDecisionLaw E (diracExp decode) = diracExp (id : I → I) := by
    funext i j
    have he (x : X) : E i x * diracExp decode x j =
        E i x * (if j = i then 1 else 0) := by
      by_cases hx : E i x = 0
      · simp [hx]
      · rw [diracExp_apply, hsupport i x hx]
    change (∑ x, E i x * diracExp decode x j) = _
    simp only [he, ← sum_mul, (hE i).2, one_mul]
    rfl
  have hrec : finiteDecisionLaw (diracExp (id : I → I)) E = E := by
    funext i x
    simp [finiteDecisionLaw, diracExp]
  rw [← capacity_dirac_id (A := I)]
  apply le_antisymm
  · rw [← hrec]
    exact capacity_garble_le _ (diracExp_valid _) E (by intro i _; exact hE i)
  · rw [← hdec]
    exact capacity_garble_le E hE _ (by intro x _; exact diracExp_valid decode x)

end Generic

/-- Full ordered observations produced by imposed actions. -/
def channel (θ : World) (h : History) :
    (n : ℕ) → FiniteExperiment (Fin n → Action) (Fin n → Observation)
  | 0 => fun _ _ => 1
  | n+1 => fun a y => response θ h (a 0) (y 0) *
      channel θ (h ++ [(a 0, y 0)]) n (Fin.tail a) (Fin.tail y)

theorem channel_valid (θ : World) (h : History) (n : ℕ) :
    IsFiniteExperiment (channel θ h n) := by
  induction n generalizing h with
  | zero => intro a; constructor <;> simp [channel]
  | succ n ih =>
    intro a
    constructor
    · intro y
      exact mul_nonneg ((response_valid θ h (a 0)).1 (y 0))
        ((ih _ (Fin.tail a)).1 (Fin.tail y))
    · rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Observation)).sum_comp]
      rw [Fintype.sum_prod_type]
      have he (x : Observation) (ys : Fin n → Observation) :
          (Fin.consEquiv (fun _ : Fin (n+1) => Observation)) (x,ys) = Fin.cons x ys := rfl
      simp only [he, channel, Fin.cons_zero, Fin.tail_cons]
      simp only [← mul_sum, (ih _ _).2, mul_one, (response_valid θ h (a 0)).2]

/-- After startup, the fixed-world channel is a product of its stage channels. -/
theorem channel_tail (θ : World) (h : History) (hh : h ≠ []) (n : ℕ)
    (a : Fin n → Action) (y : Fin n → Observation) :
    channel θ h n a y = ∏ i, prodLaw (panelDisplay h (a i))
      (pointMonitor (monitorLabel θ (h.length + i.val - 1))) (y i) := by
  induction n generalizing h with
  | zero => simp [channel]
  | succ n ih =>
    simp only [channel]
    rw [ih _ (by simp), Fin.prod_univ_succ]
    congr 1
    · simp [response_tick θ h _ _ hh, prodLaw]
    · apply prod_congr rfl
      intro i _
      rw [Empowerment.panelDisplay_append h hh]
      have hl : (h ++ [(a 0, y 0)]).length + i.val - 1 = h.length + i.succ.val - 1 := by
        simp
      rw [hl]
      rfl

def buttonBits {n : ℕ} (a : Fin n → Action) : Fin n → Bool := fun i => a i == play1

def buttonActions {n : ℕ} (b : Fin n → Bool) : Fin n → Action :=
  fun i => if b i then play1 else play0

theorem buttonBits_actions {n : ℕ} (b : Fin n → Bool) : buttonBits (buttonActions b) = b := by
  funext i
  cases h : b i <;> simp [buttonBits, buttonActions, h, play0, play1]

theorem buttonBits_surjective (n : ℕ) : Function.Surjective (@buttonBits n) :=
  fun b => ⟨buttonActions b, buttonBits_actions b⟩

def bitChannel (θ : World) (clock n : ℕ) :
    FiniteExperiment (Fin n → Bool) (Fin n → Observation) := fun b y =>
  ∏ i, prodLaw (pairDist (b i)) (pointMonitor (monitorLabel θ (clock+i.val-1))) (y i)

theorem channel_play (θ : World) (h : History) (hh : h ≠ []) (hi : ¬inspected h) (n : ℕ) :
    channel θ h n = fun a => bitChannel θ h.length n (buttonBits a) := by
  funext a y
  rw [channel_tail θ h hh]
  simp [bitChannel, panelDisplay, hi, buttonBits]

theorem bitChannel_valid (θ : World) (clock n : ℕ) (hc : 0 < clock) :
    IsFiniteExperiment (bitChannel θ clock n) := by
  let h : History := List.replicate clock (play0, (0,0))
  have hh : h ≠ [] := by simp [h]; omega
  have hi : ¬inspected h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : clock ≠ 0)
    simp [h, List.replicate_succ, inspected, inspect, play0]
  intro b
  have he : channel θ h n (buttonActions b) = bitChannel θ clock n b := by
    rw [channel_play θ h hh hi]
    simp only [buttonBits_actions]
    simp [h]
  rw [← he]
  exact channel_valid θ h n _

def decodeBits {n : ℕ} (y : Fin n → Observation) : Fin n → Bool :=
  fun i => decide (2 ≤ (y i).1.val)

theorem bitChannel_support (θ : World) (clock n : ℕ) (b : Fin n → Bool)
    (y : Fin n → Observation) (hy : bitChannel θ clock n b y ≠ 0) : decodeBits y = b := by
  funext i
  have hp := (Finset.prod_ne_zero_iff.mp hy) i (mem_univ i)
  have hd : pairDist (b i) (y i).1 ≠ 0 := fun hz => hp (by simp [prodLaw, hz])
  change decide (2 ≤ (y i).1.val) = b i
  generalize hbi : b i = bi at *
  generalize hdi : (y i).1 = d at *
  cases bi <;> fin_cases d <;> norm_num [pairDist] at *

theorem bitChannel_capacity (θ : World) (clock n : ℕ) (hc : 0 < clock) :
    capacity (bitChannel θ clock n) = (n:ℝ) * Real.log 2 := by
  rw [capacity_of_decoder _ (bitChannel_valid θ clock n hc) decodeBits
    (bitChannel_support θ clock n)]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow]

/-- Full-block capacity in bits. -/
def blockCapacity (θ : World) (h : History) (n : ℕ) : ℝ :=
  capacity (channel θ h n) / Real.log 2

theorem blockCapacity_tail (θ : World) (h : History) (hh : h ≠ []) (n : ℕ) :
    blockCapacity θ h n = if inspected h then 0 else n := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  have hc : 0 < h.length := List.length_pos_iff.mpr hh
  by_cases hi : inspected h
  · have he : channel θ h n = fun _ => channel θ h n (fun _ => inspect) := by
      funext a y
      rw [channel_tail θ h hh, channel_tail θ h hh]
      simp [panelDisplay, hi]
    rw [blockCapacity, he, Empowerment.capacity_constChannel _
      (channel_valid θ h n (fun _ => inspect))]
    simp [hi]
  · rw [blockCapacity, channel_play θ h hh hi,
      capacity_precomp_surjective _ (bitChannel_valid θ h.length n hc) buttonBits
        (buttonBits_surjective n), bitChannel_capacity θ h.length n hc]
    simp [hi, hl]

/-- The full block equals the terminal component sum after startup. -/
theorem blockCapacity_eq_component_sum (θ : World) (h : History) (hh : h ≠ []) (n : ℕ) :
    blockCapacity θ h n = ∑ j ∈ range n, Empowerment.multiStepCapacity θ h (j+1) := by
  rw [blockCapacity_tail θ h hh]
  simp_rw [Empowerment.multiStepCapacity_tail θ h hh]
  by_cases hi : inspected h <;> simp [hi]

theorem blockCapacity_nonneg (θ : World) (h : History) (n : ℕ) :
    0 ≤ blockCapacity θ h n :=
  div_nonneg (Empowerment.capacity_nonneg_of_valid _ (channel_valid θ h n))
    (Real.log_nonneg (by norm_num))

/-- A length-n input has at most n log₂(3) bits of information. -/
theorem blockCapacity_upper (θ : World) (h : History) (n : ℕ) :
    blockCapacity θ h n ≤ n * Real.log 3 / Real.log 2 := by
  obtain ⟨ν, hν, hmax⟩ := exists_capacity_achieving _ (channel_valid θ h n)
  have hc : capacity (channel θ h n) ≤ n * Real.log 3 := by
    rw [capacity_eq_of_isMaxOn _ hν hmax]
    have hb := (finiteBayesInformation_le_ent ν hν _ (channel_valid θ h n)).trans
      (ent_le_log_card ν hν)
    simpa [Fintype.card_fun, Action, Real.log_pow] using hb
  exact div_le_div_of_nonneg_right hc (Real.log_nonneg (by norm_num))

theorem blockCapacity_integrable (h : History) (n : ℕ) :
    Integrable (fun θ => blockCapacity θ h n) AlarmPanelPrior.prior := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (n * Real.log 3 / Real.log 2)
  filter_upwards [] with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (blockCapacity_nonneg θ h n)]
  exact blockCapacity_upper θ h n

/-- Prior average of the actual startup capacity; it does not involve the collecting policy. -/
def startup (n : ℕ) : ℝ := ∫ θ, blockCapacity θ [] n ∂AlarmPanelPrior.prior

theorem startup_nonneg (n : ℕ) : 0 ≤ startup n :=
  integral_nonneg (fun θ => blockCapacity_nonneg θ [] n)

theorem startup_upper (n : ℕ) : startup n ≤ n * Real.log 3 / Real.log 2 := by
  have hu := integral_mono (blockCapacity_integrable [] n)
    (integrable_const (n * Real.log 3 / Real.log 2)) (fun θ => blockCapacity_upper θ [] n)
  simpa [startup] using hu

/-- Expected literal capacity at the collected history, in one fixed world. -/
def worldStage (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World) (t : ℕ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Observation t,
    experiment π.1 t θ w * blockCapacity θ (List.ofFn w) n

theorem worldStage_zero (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World) :
    worldStage n π θ 0 = blockCapacity θ [] n := by
  simp [worldStage, experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]

theorem worldStage_succ (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World)
    (t : ℕ) : worldStage n π θ (t+1) = n * (1-inspectionProbability π.1) := by
  have he : worldStage n π θ (t+1) = n * Empowerment.multiStepStage 1 π θ (t+1) := by
    unfold worldStage Empowerment.multiStepStage
    rw [mul_sum]
    apply sum_congr rfl
    intro w _
    rw [blockCapacity_tail θ (List.ofFn w) (by simp),
      Empowerment.multiStepCapacity_tail θ (List.ofFn w) (by simp) 0]
    split_ifs <;> ring
  rw [he, Empowerment.multiStepStage_succ 0]

theorem worldStage_integrable (n : ℕ) (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    Integrable (fun θ => worldStage n π θ t) AlarmPanelPrior.prior := by
  cases t with
  | zero => simpa only [worldStage_zero] using blockCapacity_integrable [] n
  | succ t => simpa only [worldStage_succ] using
      (integrable_const ((n:ℝ) * (1-inspectionProbability π.1)))

/-- Prior expectation of the actual visited full-block capacity. -/
def stage (n : ℕ) (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  ∫ θ, worldStage n π θ t ∂AlarmPanelPrior.prior

theorem stage_zero (n : ℕ) (π : ValidCausalPolicy Action Observation) : stage n π 0 = startup n := by
  simp only [stage, worldStage_zero, startup]

theorem stage_succ (n : ℕ) (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    stage n π (t+1) = n * (1-inspectionProbability π.1) := by
  simp [stage, worldStage_succ]

/-- Finite undiscounted return, with startup included. -/
def finiteReturn (n : ℕ) (π : ValidCausalPolicy Action Observation) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, stage n π t

theorem finiteReturn_eq (n : ℕ) (π : ValidCausalPolicy Action Observation) (T : ℕ) :
    finiteReturn n π T = BlockComplete.finiteReturn (startup n) n π T := by
  cases T with
  | zero => simp [finiteReturn, BlockComplete.finiteReturn]
  | succ T =>
    rw [finiteReturn, sum_range_succ']
    simp [stage_succ, stage_zero, BlockComplete.finiteReturn, BlockComplete.count]
    ring

/-- Finite linearity also puts the prior expectation outside the cumulative sum. -/
theorem finiteReturn_eq_integral_sum (n : ℕ) (π : ValidCausalPolicy Action Observation) (T : ℕ) :
    finiteReturn n π T = ∫ θ, ∑ t ∈ range T, worldStage n π θ t ∂AlarmPanelPrior.prior := by
  rw [integral_finsetSum _ (fun t _ => worldStage_integrable n π t)]
  rfl

/-- Before taking the complete return, every horizon from two onward selects pure PLAY. -/
theorem finiteReturn_maximizer_iff (n : ℕ) (hn : 1 ≤ n) (T : ℕ) (hT : 2 ≤ T)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, finiteReturn n ρ T ≤ finiteReturn n π T) ↔ inspectionProbability π.1 = 0 := by
  have hT0 : T ≠ 0 := by omega
  have hc : 0 < (BlockComplete.count n T : ℝ) := by
    exact_mod_cast (show 0 < BlockComplete.count n T from
      Nat.mul_pos (by omega) (by omega))
  simp only [finiteReturn_eq, BlockComplete.finiteReturn, hT0, if_false]
  constructor
  · intro h
    have hp := h Empowerment.playPolicy
    rw [Empowerment.playPolicy_inspection] at hp
    have hs := inspectionProbability_nonneg π.1 π.2
    nlinarith
  · intro hs ρ
    rw [hs]
    have hr := inspectionProbability_nonneg ρ.1 ρ.2
    nlinarith

/-- The nonnegative complete return, allowing positive infinity. -/
def completeReturn (n : ℕ) (π : ValidCausalPolicy Action Observation) : ENNReal :=
  ⨆ T : ℕ, ENNReal.ofReal (finiteReturn n π T)

theorem completeReturn_eq (n : ℕ) (π : ValidCausalPolicy Action Observation) :
    completeReturn n π = BlockComplete.completeReturn (startup n) n π := by
  simp only [completeReturn, finiteReturn_eq, BlockComplete.completeReturn]

theorem completeReturn_inspect (n : ℕ) (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 = 1) : completeReturn n π = ENNReal.ofReal (startup n) := by
  rw [completeReturn_eq]
  exact BlockComplete.inspect_return (startup n) n π hs

theorem completeReturn_play (n : ℕ) (hn : 1 ≤ n) (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 < 1) : completeReturn n π = ⊤ := by
  rw [completeReturn_eq]
  exact BlockComplete.play_return (startup n) n hn π hs

theorem maximizer_iff (n : ℕ) (hn : 1 ≤ n) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, completeReturn n ρ ≤ completeReturn n π) ↔ inspectionProbability π.1 < 1 := by
  simp only [completeReturn_eq]
  exact BlockComplete.maximizer_iff (startup n) n hn π

/-- Every literal full-block optimum has positive native loss and a strict native dominator. -/
theorem all_optima_failure (n : ℕ) (hn : 1 ≤ n) (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, completeReturn n ρ ≤ completeReturn n π) :
    0 < BlockComplete.eventualInspectionDeficiency π ∧
      BlockComplete.eventualInspectionDeficiency π ≤ 1/2 ∧
      CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
      ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  apply BlockComplete.all_optima_failure (startup n) n hn π
  simpa only [completeReturn_eq] using hopt

theorem optimizer_loss_realized (n : ℕ) (hn : 1 ≤ n) (d : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1/2) :
    ∃ π : ValidCausalPolicy Action Observation,
      (∀ ρ, completeReturn n ρ ≤ completeReturn n π) ∧
      BlockComplete.eventualInspectionDeficiency π = d := by
  simpa only [completeReturn_eq] using
    BlockComplete.optimizer_loss_realized (startup n) n hn d hd hd1

end IdExp.PairedAlarm.BlockChannel
