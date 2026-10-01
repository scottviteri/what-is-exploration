import Formal.FinitePolicyPerturbation
import Formal.DeficiencyTriangle
import Formal.CausalProcess

/-!
# A vanishing admissibility modulus on compact experiment families

The paper's qualitative admissibility statement: on a compact family of valid
finite experiments with a common signal alphabet, varying continuously in
uniform row total variation, a continuous score that strictly preserves
Blackwell domination admits a joint optimization/dominance tolerance.  For
every `ε > 0` there are `η, ρ > 0` such that whenever `t` simulates `s`
within `ρ` and scores at most `η` better, `s` simulates `t` within `ε`.
In particular an `η`-optimal member is at most `ε` worse than any feasible
`ρ`-dominator.

The family is parameterized by a compact space.  The paper's fixed-horizon
policy family is one instance; the abstract statement needs only the row
continuity, the compactness, the score continuity, and the strictness.  The
proof is a nested-closed-set compactness argument; it constructs no rate and
assumes no greatest feasible experiment, attained optimum, or world
identification.
-/

namespace IdExp

open Set Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {Θ X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Θ]

/-! ## Deficiency is one-Lipschitz in its target as well -/

/-- **Target Lipschitz lemma.**  A uniform rowwise TV bound between two valid
targets controls the change of directed deficiency from any fixed valid
source. -/
theorem abs_finiteDeficiency_sub_le_of_rowTV_target
    (E : FiniteExperiment Θ X) (F F' : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hF' : IsFiniteExperiment F') (d : ℝ)
    (hrow : ∀ θ, finiteTV (F θ) (F' θ) ≤ d) :
    |finiteDeficiency E F - finiteDeficiency E F'| ≤ d := by
  have hFF' : finiteDeficiency F F' ≤ d := finiteDeficiency_le_of_rowTV F F' d hrow
  have hF'F : finiteDeficiency F' F ≤ d :=
    finiteDeficiency_le_of_rowTV F' F d fun θ => by
      rw [finiteTV_symm]
      exact hrow θ
  have h1 := finiteDeficiency_triangle E F F' hE hF hF'
  have h2 := finiteDeficiency_triangle E F' F hE hF' hF
  rw [abs_le]
  constructor <;> linarith

/-! ## Uniformly row-continuous families -/

variable {T : Type*} [TopologicalSpace T]

/-- A family of valid finite experiments on a common signal alphabet whose
rows vary continuously in the parameter, uniformly over the worlds.  The
world class is arbitrary and nonempty; no topology on it is used. -/
structure UniformRowFamily (Θ X T : Type*) [Fintype X] [TopologicalSpace T] where
  /-- The experiment at each parameter. -/
  exp : T → FiniteExperiment Θ X
  /-- Every member is a valid experiment. -/
  valid : ∀ t, IsFiniteExperiment (exp t)
  /-- Uniform row continuity at every parameter. -/
  uniformRow : ∀ t₀ : T, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ t in 𝓝 t₀, ∀ θ, finiteTV (exp t θ) (exp t₀ θ) ≤ ε

/-- Directed deficiency is jointly continuous along a uniformly
row-continuous family. -/
theorem UniformRowFamily.continuous_deficiency (fam : UniformRowFamily Θ X T) :
    Continuous (fun p : T × T => finiteDeficiency (fam.exp p.1) (fam.exp p.2)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, t₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hs := fam.uniformRow s₀ (ε / 3) (by positivity)
  have ht := fam.uniformRow t₀ (ε / 3) (by positivity)
  have hprod := hs.prod_mk ht
  rw [← nhds_prod_eq] at hprod
  refine hprod.mono ?_
  rintro ⟨s, t⟩ ⟨hs', ht'⟩
  rw [Real.dist_eq]
  have h1 := abs_finiteDeficiency_sub_le_of_rowTV (fam.exp s) (fam.exp s₀) (fam.exp t)
    (fam.valid s) (fam.valid s₀) (fam.valid t) (ε / 3) hs'
  have h2 := abs_finiteDeficiency_sub_le_of_rowTV_target (fam.exp s₀) (fam.exp t) (fam.exp t₀)
    (fam.valid s₀) (fam.valid t) (fam.valid t₀) (ε / 3) ht'
  calc |finiteDeficiency (fam.exp s) (fam.exp t) - finiteDeficiency (fam.exp s₀) (fam.exp t₀)|
      = |(finiteDeficiency (fam.exp s) (fam.exp t) - finiteDeficiency (fam.exp s₀) (fam.exp t)) +
          (finiteDeficiency (fam.exp s₀) (fam.exp t) - finiteDeficiency (fam.exp s₀) (fam.exp t₀))| := by
        ring_nf
    _ ≤ |finiteDeficiency (fam.exp s) (fam.exp t) - finiteDeficiency (fam.exp s₀) (fam.exp t)| +
          |finiteDeficiency (fam.exp s₀) (fam.exp t) - finiteDeficiency (fam.exp s₀) (fam.exp t₀)| :=
        abs_add_le _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add h1 h2
    _ < ε := by linarith

/-- Deficiency along the family is nonnegative. -/
theorem UniformRowFamily.deficiency_nonneg (fam : UniformRowFamily Θ X T) (s t : T) :
    0 ≤ finiteDeficiency (fam.exp s) (fam.exp t) := by
  haveI := nonempty_of_isFiniteExperiment (fam.exp t) (fam.valid t)
  exact finiteDeficiency_nonneg_of_valid _ _ (fam.valid s) (fam.valid t)

/-! ## The compact modulus -/

/-- A real number bounded by `1/(k+1)` for every `k` is at most zero. -/
theorem le_zero_of_forall_le_one_div_succ {a : ℝ}
    (h : ∀ k : ℕ, a ≤ 1 / ((k : ℝ) + 1)) : a ≤ 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have := h k
  linarith

/-- The failure set at tolerance `1/(k+1)`: pairs where `t` simulates `s`
within the tolerance and scores at most the tolerance better, yet `s` misses
`t` by at least `ε`. -/
def admissibilityFailureSet (fam : UniformRowFamily Θ X T) (J : T → ℝ) (ε : ℝ) (k : ℕ) :
    Set (T × T) :=
  {p | finiteDeficiency (fam.exp p.2) (fam.exp p.1) ≤ 1 / ((k : ℝ) + 1) ∧
    J p.2 ≤ J p.1 + 1 / ((k : ℝ) + 1) ∧
    ε ≤ finiteDeficiency (fam.exp p.1) (fam.exp p.2)}

theorem admissibilityFailureSet_isClosed (fam : UniformRowFamily Θ X T) (J : T → ℝ)
    (hJ : Continuous J) (ε : ℝ) (k : ℕ) : IsClosed (admissibilityFailureSet fam J ε k) := by
  have hcont := fam.continuous_deficiency
  have hswap : Continuous (fun p : T × T => finiteDeficiency (fam.exp p.2) (fam.exp p.1)) := by
    have h := hcont.comp continuous_swap
    simp only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] at h
    exact h
  simp only [admissibilityFailureSet, Set.setOf_and]
  refine IsClosed.inter (isClosed_le hswap continuous_const) ?_
  refine IsClosed.inter (isClosed_le (hJ.comp continuous_snd)
    ((hJ.comp continuous_fst).add continuous_const)) ?_
  exact isClosed_le continuous_const hcont

theorem one_div_succ_succ_le (k : ℕ) :
    (1 : ℝ) / ((((k + 1 : ℕ) : ℝ)) + 1) ≤ 1 / ((k : ℝ) + 1) := by
  apply one_div_le_one_div_of_le
  · positivity
  · push_cast; linarith

theorem admissibilityFailureSet_antitone (fam : UniformRowFamily Θ X T) (J : T → ℝ)
    (ε : ℝ) (k : ℕ) :
    admissibilityFailureSet fam J ε (k + 1) ⊆ admissibilityFailureSet fam J ε k := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hk := one_div_succ_succ_le k
  exact ⟨h1.trans hk, h2.trans (by linarith), h3⟩

/-- A common point of all failure sets contradicts strictness. -/
theorem admissibilityFailureSet_iInter_empty (fam : UniformRowFamily Θ X T) (J : T → ℝ)
    (hstrict : ∀ s t, finiteDeficiency (fam.exp t) (fam.exp s) = 0 → J t ≤ J s →
      finiteDeficiency (fam.exp s) (fam.exp t) = 0)
    (ε : ℝ) (hε : 0 < ε) (p : T × T)
    (hp : ∀ k, p ∈ admissibilityFailureSet fam J ε k) : False := by
  have h0 : finiteDeficiency (fam.exp p.2) (fam.exp p.1) = 0 :=
    le_antisymm (le_zero_of_forall_le_one_div_succ fun k => (hp k).1)
      (fam.deficiency_nonneg p.2 p.1)
  have hJ' : J p.2 ≤ J p.1 := by
    have : J p.2 - J p.1 ≤ 0 :=
      le_zero_of_forall_le_one_div_succ fun k => by linarith [(hp k).2.1]
    linarith
  have hε' : ε ≤ finiteDeficiency (fam.exp p.1) (fam.exp p.2) := (hp 0).2.2
  have := hstrict p.1 p.2 h0 hJ'
  linarith

set_option maxHeartbeats 400000 in
/-- **Vanishing joint tolerance on a compact family.**  Let `J` be continuous
and strictly preserve Blackwell domination on a uniformly row-continuous
family over a compact parameter space: whenever `t` simulates `s` exactly and
does not score better, `s` simulates `t` exactly.  Then for every `ε > 0`
there are `η, ρ > 0` such that any `t` simulating `s` within `ρ` and scoring
at most `η` more is itself simulated by `s` within `ε`. -/
theorem compact_admissibility_modulus [CompactSpace T]
    (fam : UniformRowFamily Θ X T) (J : T → ℝ) (hJ : Continuous J)
    (hstrict : ∀ s t, finiteDeficiency (fam.exp t) (fam.exp s) = 0 → J t ≤ J s →
      finiteDeficiency (fam.exp s) (fam.exp t) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s t : T,
      finiteDeficiency (fam.exp t) (fam.exp s) ≤ ρ → J t ≤ J s + η →
        finiteDeficiency (fam.exp s) (fam.exp t) ≤ ε := by
  intro ε hε
  by_contra hcon
  have hnonempty : ∀ k, (admissibilityFailureSet fam J ε k).Nonempty := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    by_contra hempty
    apply hcon
    refine ⟨_, hpos, _, hpos, fun s t hts hJst => ?_⟩
    by_contra hst
    exact hempty ⟨(s, t), hts, hJst, (not_le.mp hst).le⟩
  have hclosed := admissibilityFailureSet_isClosed fam J hJ ε
  have hcompact : IsCompact (admissibilityFailureSet fam J ε 0) := (hclosed 0).isCompact
  obtain ⟨p, hp⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (admissibilityFailureSet fam J ε) (admissibilityFailureSet_antitone fam J ε)
      hnonempty hcompact hclosed
  rw [Set.mem_iInter] at hp
  exact admissibilityFailureSet_iInter_empty fam J hstrict ε hε p hp

/-- **Approximate optima are approximately admissible.**  With the joint
tolerances supplied by the compact modulus, an `η`-optimal member of the
family simulates every feasible `ρ`-dominator within `ε`. -/
theorem eta_optimal_simulates_rho_dominators [CompactSpace T]
    (fam : UniformRowFamily Θ X T) (J : T → ℝ) (hJ : Continuous J)
    (hstrict : ∀ s t, finiteDeficiency (fam.exp t) (fam.exp s) = 0 → J t ≤ J s →
      finiteDeficiency (fam.exp s) (fam.exp t) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : T,
      (∀ t, J t ≤ J s + η) →
        ∀ t, finiteDeficiency (fam.exp t) (fam.exp s) ≤ ρ →
          finiteDeficiency (fam.exp s) (fam.exp t) ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, ρ, hρ, h⟩ := compact_admissibility_modulus fam J hJ hstrict ε hε
  exact ⟨η, hη, ρ, hρ, fun s hopt t hts => h s t hts (hopt t)⟩

/-- Strictness follows from strict Blackwell monotonicity of the score: a
score that strictly increases along every strict exact domination is strict
in the sense used above. -/
theorem strict_of_strictBlackwellMono (fam : UniformRowFamily Θ X T) (J : T → ℝ)
    (hmono : ∀ s t, finiteDeficiency (fam.exp t) (fam.exp s) = 0 →
      finiteDeficiency (fam.exp s) (fam.exp t) ≠ 0 → J s < J t) :
    ∀ s t, finiteDeficiency (fam.exp t) (fam.exp s) = 0 → J t ≤ J s →
      finiteDeficiency (fam.exp s) (fam.exp t) = 0 := by
  intro s t hts hJ
  by_contra hne
  exact absurd hJ (not_le.mpr (hmono s t hts hne))

end

end IdExp
