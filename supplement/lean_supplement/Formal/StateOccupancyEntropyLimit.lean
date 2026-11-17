import Formal.StateOccupancyEntropyNative
import Formal.EntropyGeometry

/-!
# Limiting ensemble state entropy for the current comparison table

The literal marginal is constant after one transition. We connect it to the
proper-discount limit and optimize the limiting entropy directly, without
interchanging optimization and limits or using single-trajectory occupancy.
-/
namespace IdExp.StateOccupancyEntropy
open Finset Filter Topology
noncomputable section

def limitingOccupancy (π : ValidCausalPolicy Action State) (θ : World) : State → ℝ
  | none => 0
  | some b => terminalLaw π θ b

def limitingObjective (π : ValidCausalPolicy Action State) (θ : World) : ℝ :=
  ent (limitingOccupancy π θ)

theorem limitingOccupancy_valid (π : ValidCausalPolicy Action State) (θ : World) :
    IsDist (limitingOccupancy π θ) := by
  constructor
  · intro s; cases s with
    | none => exact le_rfl
    | some b => exact (terminalLaw_valid π θ).1 b
  · simpa [limitingOccupancy, Fintype.sum_option] using (terminalLaw_valid π θ).2

theorem stateMarginal_eq_limiting (π : ValidCausalPolicy Action State) (θ : World)
    {t : ℕ} (ht : 1 ≤ t) : stateMarginal π θ t = limitingOccupancy π θ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  funext s
  exact stateMarginal_succ π θ n s

theorem stateMarginal_tendsto_limiting (π : ValidCausalPolicy Action State) (θ : World) :
    Tendsto (stateMarginal π θ) atTop (𝓝 (limitingOccupancy π θ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
  exact (stateMarginal_eq_limiting π θ ht).symm

theorem occupancy_tendsto_limiting {ι : Type*} {l : Filter ι}
    (π : ValidCausalPolicy Action State) (θ : World) (γ : ι → ℝ)
    (hγ : Tendsto γ l (𝓝 1)) (hproper : ∀ᶠ i in l, 0 ≤ γ i ∧ γ i < 1) :
    Tendsto (fun i => occupancy π θ (γ i)) l (𝓝 (limitingOccupancy π θ)) := by
  apply tendsto_pi_nhds.mpr
  intro s
  have he : (fun i => occupancy π θ (γ i) s) =ᶠ[l]
      (fun i => match s with | none => 1 - γ i | some b => γ i * terminalLaw π θ b) :=
    hproper.mono fun i hi => occupancy_eq π θ (γ i) hi.1 hi.2 s
  apply Tendsto.congr' he.symm
  cases s with
  | none => simpa [limitingOccupancy] using (tendsto_const_nhds (x := (1 : ℝ))).sub hγ
  | some b => simpa [limitingOccupancy] using hγ.mul_const (terminalLaw π θ b)

theorem objective_tendsto_limiting {ι : Type*} {l : Filter ι}
    (π : ValidCausalPolicy Action State) (θ : World) (γ : ι → ℝ)
    (hγ : Tendsto γ l (𝓝 1)) (hproper : ∀ᶠ i in l, 0 ≤ γ i ∧ γ i < 1) :
    Tendsto (fun i => objective π θ (γ i)) l (𝓝 (limitingObjective π θ)) :=
  continuous_ent.continuousAt.tendsto.comp
    (occupancy_tendsto_limiting π θ γ hγ hproper)

theorem limitingObjective_eq_ent (π : ValidCausalPolicy Action State) (θ : World) :
    limitingObjective π θ = ent (terminalLaw π θ) := by
  simp [limitingObjective, limitingOccupancy, ent, Fintype.sum_option]

theorem limitingObjective_eq_binary (π : ValidCausalPolicy Action State) (θ : World) :
    limitingObjective π θ = binaryEntropy ((1 + π.1 [] 0) / 2) := by
  have h := objective_eq_binary π θ (1/2) (by norm_num) (by norm_num)
  rw [objective_eq π θ (1/2) (by norm_num) (by norm_num)] at h
  rw [limitingObjective_eq_ent]
  linarith

theorem limitingObjective_le (π : ValidCausalPolicy Action State) (θ : World) :
    limitingObjective π θ ≤ Real.log 2 := by
  rw [limitingObjective_eq_ent]
  simpa using ent_le_log_card (terminalLaw π θ) (terminalLaw_valid π θ)

theorem limitingObjective_eq_max_iff (π : ValidCausalPolicy Action State) (θ : World) :
    limitingObjective π θ = Real.log 2 ↔ π.1 [] 0 = 0 := by
  rw [limitingObjective_eq_ent]
  have h := ent_eq_log_card_iff (terminalLaw π θ) (terminalLaw_valid π θ)
  simpa [terminalLaw_uniform_iff] using h

theorem limitingObjective_maximizer_iff (π : ValidCausalPolicy Action State) (θ : World) :
    (∀ ρ, limitingObjective ρ θ ≤ limitingObjective π θ) ↔ π.1 [] 0 = 0 := by
  have hr : limitingObjective (purePolicy 1) θ = Real.log 2 :=
    (limitingObjective_eq_max_iff _ θ).2 (by simp [purePolicy])
  constructor
  · intro h
    apply (limitingObjective_eq_max_iff π θ).1
    exact le_antisymm (limitingObjective_le π θ) (by simpa [hr] using h (purePolicy 1))
  · intro hp ρ
    rw [(limitingObjective_eq_max_iff π θ).2 hp]
    exact limitingObjective_le ρ θ

/-- The worst value over the two physical MDPs, with no world-prior mixture. -/
def worstLimitingObjective (π : ValidCausalPolicy Action State) : ℝ :=
  min (limitingObjective π 0) (limitingObjective π 1)

theorem worstLimitingObjective_eq (π : ValidCausalPolicy Action State) (θ : World) :
    worstLimitingObjective π = limitingObjective π θ := by
  simp [worstLimitingObjective, limitingObjective_eq_binary]

theorem worstLimitingObjective_maximizer_iff (π : ValidCausalPolicy Action State) :
    (∀ ρ, worstLimitingObjective ρ ≤ worstLimitingObjective π) ↔ π.1 [] 0 = 0 := by
  simp_rw [worstLimitingObjective_eq _ 0]
  exact limitingObjective_maximizer_iff π 0

theorem limiting_all_optima_failure (θ : World) :
    (∃ π, ∀ ρ, limitingObjective ρ θ ≤ limitingObjective π θ) ∧
    ∀ π : ValidCausalPolicy Action State,
      (∀ ρ, limitingObjective ρ θ ≤ limitingObjective π θ) →
        (∀ t, finiteDeficiency (causalFiniteExperiment π.1 response t)
          (causalFiniteExperiment (purePolicy 0).1 response 1) = 1/2) ∧
        eventualTestDeficiency π = 1/2 ∧
        CausalFinitaryDominates response (purePolicy 0) π ∧
        ¬ CausalFinitaryDominates response π (purePolicy 0) := by
  refine ⟨⟨purePolicy 1, (limitingObjective_maximizer_iff _ θ).2 (by simp [purePolicy])⟩, ?_⟩
  intro π hopt
  have hp := (limitingObjective_maximizer_iff π θ).1 hopt
  exact ⟨random_deficiency π hp, random_eventualDeficiency π hp,
    random_strictly_dominated π hp⟩

end
end IdExp.StateOccupancyEntropy
