import Formal.DIAYNStateMDP
import Formal.AbsorbingExperiment
import Formal.CausalPolicyMixture
import Formal.CausalProcess

/-!
# Native capability of the literal state-based DIAYN MDP

The sampled skill is realized by one valid history policy with the exact
mixture law of full records. Independently of reward optimization, every causal
collector has permanent READ deficiency `(1-s)/2`, where s is its root READ
probability. Repeated observed states and arbitrary adaptive action randomness
supply no additional unknown-world information after the first transition.
-/
namespace IdExp.DIAYNState
noncomputable section
open Finset

/-- One latent uniform skill is sampled for the whole run. The behavioral
realization uses posterior skill weights from the retained action history. -/
def collector (P : Policy) : ValidCausalPolicy Action State :=
  ⟨causalPolicyMixture (uniformPrior Skill) (fun z => (causalPolicy P z).1),
    isCausalPolicy_causalPolicyMixture _ isDist_uniformPrior _ (fun z => (causalPolicy P z).2)⟩

/-- Exact sampled-skill realization, including every randomized retained action. -/
theorem collector_record_mixture (P : Policy) (t : ℕ) (θ : World)
    (w : CausalFiniteTrace Action State t) :
    causalFiniteExperiment (collector P).1 response t θ w =
      ∑ z : Skill, uniformPrior Skill z *
        causalFiniteExperiment (causalPolicy P z).1 response t θ w :=
  congrFun (congrFun (causalFiniteExperiment_policyMixture
    (uniformPrior Skill) isDist_uniformPrior (fun z => (causalPolicy P z).1)
    (fun z => (causalPolicy P z).2) response t) θ) w

/-- Root READ probability of the actual once-sampled skill collector. -/
def readProbability (P : Policy) : ℝ :=
  ∑ z : Skill, uniformPrior Skill z * rootExperiment P z 0

theorem collector_readProbability (P : Policy) :
    (collector P).1 [] 0 = readProbability P := by
  simp [collector, causalPolicyMixture, causalPolicyMixtureMass, causalPolicyProb,
    causalPolicyProbFrom, causalPolicy, currentState, readProbability,
    rootExperiment, uniformPrior, Fin.sum_univ_two]

/-- World-independent continuation law for a convenient presentation. -/
def nativeStay : CausalResponse Action State := fun h _ s => point (currentState h) s

theorem nativeStay_valid : IsCausalResponse nativeStay := by
  intro h a
  exact point_valid _

/-- On impossible nonempty histories ending at the root this presentation
stays there. On every realizable history it is the literal MDP response. -/
def nativeResponse (θ : World) : CausalResponse Action State :=
  fun h a s => if h = [] then point (branch θ a) s else nativeStay h a s

def nativeRoot (a : Action) : FiniteExperiment World State := fun θ => point (branch θ a)

theorem nativeRoot_valid (a : Action) : IsFiniteExperiment (nativeRoot a) := by
  intro θ
  exact point_valid _

theorem nativeResponse_valid (θ : World) : IsCausalResponse (nativeResponse θ) := by
  intro h a
  by_cases hh : h = []
  · have he : nativeResponse θ h a = point (branch θ a) := by
      funext s; simp [nativeResponse, hh]
    rw [he]
    exact point_valid _
  · have he : nativeResponse θ h a = nativeStay h a := by
      funext s; simp [nativeResponse, hh]
    rw [he]
    exact nativeStay_valid h a

theorem nativeResponse_sharedTail : HasSharedCausalTail nativeResponse 1 nativeStay := by
  intro θ h a s hh
  have hn : h ≠ [] := by intro hz; simp [hz] at hh
  simp [nativeResponse, hn]

/-- The two response presentations induce exactly the same actual finite records. -/
theorem experiment_eq_nativeResponse (π : ValidCausalPolicy Action State) (t : ℕ) :
    causalFiniteExperiment π.1 response t = causalFiniteExperiment π.1 nativeResponse t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext θ w
    have hp := congrFun (congrFun ih θ) (Fin.init w)
    change causalTraceProb π.1 (response θ) (List.ofFn (Fin.init w)) =
      causalTraceProb π.1 (nativeResponse θ) (List.ofFn (Fin.init w)) at hp
    change causalTraceProb π.1 (response θ) (List.ofFn w) =
      causalTraceProb π.1 (nativeResponse θ) (List.ofFn w)
    rw [List.ofFn_succ_last, causalTraceProb_append_singleton,
      causalTraceProb_append_singleton]
    change causalTraceProb π.1 (response θ) (List.ofFn (Fin.init w)) *
      π.1 (List.ofFn (Fin.init w)) (w (Fin.last t)).1 *
        response θ (List.ofFn (Fin.init w)) (w (Fin.last t)).1 (w (Fin.last t)).2 =
      causalTraceProb π.1 (nativeResponse θ) (List.ofFn (Fin.init w)) *
      π.1 (List.ofFn (Fin.init w)) (w (Fin.last t)).1 *
        nativeResponse θ (List.ofFn (Fin.init w)) (w (Fin.last t)).1 (w (Fin.last t)).2
    by_cases hz : causalTraceProb π.1 (response θ) (List.ofFn (Fin.init w)) = 0
    · rw [hz, ← hp, hz]; simp
    have hr : response θ (List.ofFn (Fin.init w)) (w (Fin.last t)).1 (w (Fin.last t)).2 =
        nativeResponse θ (List.ofFn (Fin.init w)) (w (Fin.last t)).1 (w (Fin.last t)).2 := by
      cases t with
      | zero => simp [response, transition, currentState, nativeResponse]
      | succ t =>
        have hn := supported_currentState_ne_none π.1 θ t (Fin.init w) hz
        cases hs : currentState (List.ofFn (Fin.init w)) with
        | none => exact False.elim (hn hs)
        | some s =>
          have hne : List.ofFn (Fin.init w) ≠ [] := by simp
          simp only [response, hs, transition, nativeResponse, if_neg hne, nativeStay]
    rw [hr, hp]

/-- Full root record of an arbitrary randomized history policy. -/
def nativeRootRecord (π : ValidCausalPolicy Action State) : FiniteExperiment World (Action × State) :=
  absorbingRootExperiment nativeRoot π.1

theorem nativeRootRecord_valid (π : ValidCausalPolicy Action State) :
    IsFiniteExperiment (nativeRootRecord π) :=
  absorbingRootExperiment_valid nativeRoot nativeRoot_valid π.1 π.2

theorem native_one_eq_absorbing (π : CausalPolicy Action State) :
    causalFiniteExperiment π nativeResponse 1 =
      causalFiniteExperiment π (absorbingResponse none nativeRoot) 1 := by
  funext θ w
  simp [causalFiniteExperiment, causalTraceProb, List.ofFn_succ, causalTraceProbFrom,
    nativeResponse, absorbingResponse, nativeRoot]

theorem prefix_root_equiv (π : ValidCausalPolicy Action State) (t : ℕ) :
    FiniteBlackwellLE (causalFiniteExperiment π.1 response (t+1)) (nativeRootRecord π) ∧
      FiniteBlackwellLE (nativeRootRecord π) (causalFiniteExperiment π.1 response (t+1)) := by
  rw [experiment_eq_nativeResponse]
  obtain ⟨he1, h1e⟩ := causalFiniteExperiment_sharedTail_blackwell_equiv π.1 π.2
    nativeResponse nativeResponse_valid nativeStay nativeStay_valid 1 nativeResponse_sharedTail
    (show 1 ≤ t+1 by omega)
  have hr := absorbingCausalExperiment_root_blackwell_equiv none nativeRoot nativeRoot_valid π.1 π.2 0
  rw [← native_one_eq_absorbing] at hr
  exact ⟨finiteBlackwellLE_trans he1 hr.1, finiteBlackwellLE_trans hr.2 h1e⟩

theorem native_root_bounds (π : ValidCausalPolicy Action State) :
    0 ≤ π.1 [] 0 ∧ π.1 [] 0 ≤ 1 := by
  refine ⟨(π.2 []).1 0, ?_⟩
  have h := (π.2 []).2
  simp only [Fin.sum_univ_three] at h
  linarith [(π.2 []).1 1, (π.2 []).1 2]

theorem native_root_other (π : ValidCausalPolicy Action State) :
    π.1 [] 1 + π.1 [] 2 = 1 - π.1 [] 0 := by
  have h := (π.2 []).2
  simp only [Fin.sum_univ_three] at h
  linarith

/-- The retained root records differ only on the READ branch. -/
private theorem branch_one (θ : World) : branch θ (1 : Action) = some (Sum.inr (0 : Skill)) := rfl

private theorem branch_two (θ : World) : branch θ (2 : Action) = some (Sum.inr (1 : Skill)) := rfl

theorem nativeRootRecord_pairTV (π : ValidCausalPolicy Action State) :
    finiteTV (nativeRootRecord π 0) (nativeRootRecord π 1) = π.1 [] 0 := by
  have hs := (native_root_bounds π).1
  norm_num [nativeRootRecord, absorbingRootExperiment, nativeRoot, point, branch_one, branch_two,
    finiteTV, Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_sum_type,
    Fin.sum_univ_three, Fin.sum_univ_two, abs_of_nonneg hs]
  simp only [reduceCtorEq, if_false, sub_self, abs_zero, zero_add, add_zero]
  ring

/-- Preserve an observed READ bit; otherwise make a fair world guess. -/
def nativeGuess (ao : Action × State) (θ : World) : ℝ :=
  match ao.2 with
  | some (Sum.inl b) => if θ = b then 1 else 0
  | _ => 1 / 2

def worldIdentity : FiniteExperiment World World := diracExp id

theorem worldIdentity_valid : IsFiniteExperiment worldIdentity := by
  intro θ
  constructor
  · intro b; simp only [worldIdentity, diracExp]; split_ifs <;> norm_num
  · fin_cases θ <;> norm_num [worldIdentity, diracExp, Fin.sum_univ_two]

theorem nativeGuess_valid : nativeGuess ∈ stochasticRules (Action × State) World := by
  intro ao _
  rcases ao with ⟨a, s⟩
  cases s with
  | none => constructor <;> simp [nativeGuess]
  | some s =>
    cases s with
    | inl b =>
      constructor
      · intro θ; simp only [nativeGuess]; split_ifs <;> norm_num
      · simp [nativeGuess]
    | inr b => constructor <;> simp [nativeGuess]

theorem nativeGuess_error (π : ValidCausalPolicy Action State) (θ : World) :
    decodeErr (nativeRootRecord π) worldIdentity nativeGuess θ = (1 - π.1 [] 0)/2 := by
  have hs0 := (native_root_bounds π).1
  have hs1 := (native_root_bounds π).2
  have ho := native_root_other π
  fin_cases θ <;>
    norm_num [decodeErr, nativeRootRecord, absorbingRootExperiment, nativeRoot, point,
      branch_one, branch_two, nativeGuess, worldIdentity, diracExp, Fintype.sum_prod_type,
      Fintype.sum_option, Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two] <;>
    (repeat first | rw [abs_of_nonpos (by linarith)] | rw [abs_of_nonneg (by linarith)]) <;>
    linarith

theorem root_world_deficiency (π : ValidCausalPolicy Action State) :
    finiteDeficiency (nativeRootRecord π) worldIdentity = (1 - π.1 [] 0)/2 := by
  apply le_antisymm
  · exact finiteDeficiency_le_of_decoder _ _ nativeGuess nativeGuess_valid _
      (fun θ => (nativeGuess_error π θ).le)
  · have h := finiteDeficiency_pairwise_lower _ _ (nativeRootRecord_valid π) worldIdentity_valid 0 1
    have ht : finiteTV (worldIdentity 0) (worldIdentity 1) = 1 := by
      norm_num [worldIdentity, diracExp, finiteTV, Fin.sum_univ_two]
    rwa [ht, nativeRootRecord_pairTV] at h

theorem prefix_world_deficiency (π : ValidCausalPolicy Action State) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 response (t+1)) worldIdentity =
      (1 - π.1 [] 0)/2 := by
  rw [finiteDeficiency_eq_of_source_blackwellEquiv _ (nativeRootRecord π) worldIdentity
    (prefix_root_equiv π t).1 (prefix_root_equiv π t).2]
  exact root_world_deficiency π

/-- Full revelation can simulate any finite target experiment. -/
theorem worldIdentity_dominates {Y : Type*} [Fintype Y]
    (E : FiniteExperiment World Y) (hE : IsFiniteExperiment E) :
    FiniteBlackwellLE E worldIdentity := by
  refine ⟨E, fun θ _ => hE θ, ?_⟩
  funext θ y
  simp [finiteDecisionLaw, worldIdentity, diracExp]

/-- Decode the world from the deterministic native READ output. -/
def nativeWorldOfState : State → World
  | some (Sum.inl θ) => θ
  | _ => 0

theorem nativeRoot_read_world_equiv :
    FiniteBlackwellLE (nativeRoot 0) worldIdentity ∧
      FiniteBlackwellLE worldIdentity (nativeRoot 0) := by
  refine ⟨worldIdentity_dominates _ (nativeRoot_valid 0), ?_⟩
  refine ⟨absorbingSignalRule nativeWorldOfState, absorbingSignalRule_valid _, ?_⟩
  funext θ b
  simp [finiteDecisionLaw, nativeRoot, point, absorbingSignalRule,
    nativeWorldOfState, worldIdentity, diracExp]
  rfl

def readPlan : CausalPlan Action State 1 := fun _ => 0

theorem nativeRead_world_equiv :
    FiniteBlackwellLE (causalPlanObservationExperiment 1 readPlan response) worldIdentity ∧
      FiniteBlackwellLE worldIdentity (causalPlanObservationExperiment 1 readPlan response) := by
  have heq : causalPlanObservationExperiment 1 readPlan response =
      causalPlanObservationExperiment 1 readPlan (absorbingResponse none nativeRoot) := by
    unfold causalPlanObservationExperiment
    rw [experiment_eq_nativeResponse ⟨_, isCausalPolicy_causalPolicyOfPlan 1 readPlan⟩,
      native_one_eq_absorbing]
  rw [heq]
  have hr := absorbingNativeTest_all_depths_blackwell_equiv none nativeRoot nativeRoot_valid 0 readPlan
  change FiniteBlackwellLE _ (nativeRoot 0) ∧ FiniteBlackwellLE (nativeRoot 0) _ at hr
  exact ⟨finiteBlackwellLE_trans hr.1 nativeRoot_read_world_equiv.1,
    finiteBlackwellLE_trans nativeRoot_read_world_equiv.2 hr.2⟩

/-- Exact permanent loss to the available native READ experiment. -/
theorem prefix_nativeRead_deficiency (π : ValidCausalPolicy Action State) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 response (t+1))
      (causalPlanObservationExperiment 1 readPlan response) = (1 - π.1 [] 0)/2 := by
  rw [finiteDeficiency_eq_of_target_blackwellEquiv _ _ worldIdentity
    (causalFiniteExperiment_valid π.1 π.2 response response_valid (t+1))
    (causalPlanObservationExperiment_valid 1 readPlan response response_valid)
    worldIdentity_valid nativeRead_world_equiv.1 nativeRead_world_equiv.2]
  exact prefix_world_deficiency π t

/-- Eventual loss takes the infimum over every finite collection time, including
zero, and equals the same permanent positive-time loss. -/
theorem eventual_nativeRead_deficiency (π : ValidCausalPolicy Action State) :
    sInf (Set.range (causalPolicyTestDeficiency π response ⟨1, readPlan⟩)) =
      (1 - π.1 [] 0)/2 := by
  let f := causalPolicyTestDeficiency π response ⟨1, readPlan⟩
  have hf (t : ℕ) : f (t+1) = (1 - π.1 [] 0)/2 :=
    prefix_nativeRead_deficiency π t
  have ha : Antitone f := causalPolicyTestDeficiency_antitone π response response_valid _
  have hl (t : ℕ) : (1 - π.1 [] 0)/2 ≤ f t := by
    rw [← hf t]
    exact ha (by omega)
  change sInf (Set.range f) = _
  apply le_antisymm
  · rw [← hf 0]
    exact csInf_le ⟨(1 - π.1 [] 0)/2, by rintro _ ⟨t, rfl⟩; exact hl t⟩ ⟨1, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact hl t)

def readPolicy : ValidCausalPolicy Action State :=
  ⟨detPolicy (fun _ => 0), isCausalPolicy_detPolicy _⟩

theorem readPolicy_nativelySufficient : CausalNativelySufficient response readPolicy := by
  intro n ε hε
  refine ⟨1, ?_⟩
  intro t ht τ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  have h := finiteDeficiency_mono_target_of_finiteBlackwellLE
    (causalFiniteExperiment readPolicy.1 response (k+1))
    (causalPlanObservationExperiment n τ response) worldIdentity
    (causalFiniteExperiment_valid readPolicy.1 readPolicy.2 response response_valid (k+1))
    worldIdentity_valid
    (worldIdentity_dominates _ (causalPlanObservationExperiment_valid n τ response response_valid))
  rw [prefix_world_deficiency] at h
  norm_num [readPolicy, detPolicy] at h
  exact h.trans_lt hε

theorem native_not_sufficient (π : ValidCausalPolicy Action State) (hs : π.1 [] 0 < 1) :
    ¬ CausalNativelySufficient response π := by
  intro h
  obtain ⟨T, hT⟩ := h 1 ((1-π.1 [] 0)/2) (by linarith)
  have hb := hT (T+1) (by omega) readPlan
  rw [prefix_nativeRead_deficiency] at hb
  exact lt_irrefl _ hb

theorem readPolicy_strictly_dominates (π : ValidCausalPolicy Action State) (hs : π.1 [] 0 < 1) :
    CausalFinitaryDominates response readPolicy π ∧
      ¬ CausalFinitaryDominates response π readPolicy := by
  have hg := (causalNativelySufficient_iff_finitarilyGreatest response response_valid readPolicy).1
    readPolicy_nativelySufficient
  refine ⟨hg π, ?_⟩
  intro hback
  apply native_not_sufficient π hs
  apply (causalNativelySufficient_iff_finitarilyGreatest response response_valid π).2
  intro ρ
  exact causalFinitaryDominates_trans response response_valid hback (hg ρ)

/-- The stationary skill-policy family executes as an actual causal collector. -/
theorem collector_nativeRead_deficiency (P : Policy) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment (collector P).1 response (t+1))
      (causalPlanObservationExperiment 1 readPlan response) = (1-readProbability P)/2 := by
  rw [prefix_nativeRead_deficiency, collector_readProbability]

theorem collector_strictly_dominated (P : Policy) (hs : readProbability P < 1) :
    CausalFinitaryDominates response readPolicy (collector P) ∧
      ¬ CausalFinitaryDominates response (collector P) readPolicy :=
  readPolicy_strictly_dominates _ (by rwa [collector_readProbability])

end
end IdExp.DIAYNState
