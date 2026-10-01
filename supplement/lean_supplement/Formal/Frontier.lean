import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn
import Mathlib.Topology.Sequences

/-!
# The compact Pareto frontier: abstract order and topology

Paper Definition `def:frontier` and Propositions `prop:approach`, `prop:frontier`.
The completion of the attainable region is a compact space on which Blackwell
dominance is a closed preorder; objectives are continuous functions on it.
The three order/topology steps used there are proved here in the abstract:

* `exists_maximal_of_compactSpace`: in a compact space with a preorder whose
  up-sets are closed, every point lies below a maximal element (so the Pareto
  frontier is nonempty and above every attainable point);
* `tendsto_infDist_argmax_of_tendsto_sSup`: in a compact metric space, a
  maximizing sequence of a continuous function converges to the set of its
  maximizers (distance to that set tends to zero);
* `argmax_subset_maximal_of_strictMono`: maximizers of a strictly monotone
  function are maximal, so maximizing sequences of a continuous strictly
  monotone objective converge to the frontier
  (`tendsto_infDist_frontier_of_strictMono`);
* `exists_gap_of_compact`: the operational form of asymptotic frontier
  completeness — outside every `η`-neighbourhood of the maximizers the objective
  is bounded away from its supremum;
* `maximal_iff_safe_and_live`, `top_le_of_safe_and_live`, `split_le_of_triangle`:
  the two-bounds characterization of frontier attainment (safety toward a
  dominating frontier point plus liveness), its attained-top case, and the ε split.
-/

open Filter Topology Set Metric

set_option linter.unusedSectionVars false

namespace IdExp

section Zorn

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Preorder X]

/-- **Maximal elements above every point.**  If every up-set `Ici x` is closed and
the space is compact, every element is below a maximal element: a chain's up-sets
are a directed family of nonempty closed (hence compact) sets, whose intersection
provides an upper bound; Zorn finishes. -/
theorem exists_maximal_of_compactSpace (hclosed : ∀ x : X, IsClosed (Ici x)) (x : X) :
    ∃ m, x ≤ m ∧ ∀ y, m ≤ y → y ≤ m := by
  have hchain : ∀ c ⊆ (Set.univ : Set X), IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ (Set.univ : Set X), ∀ z ∈ c, z ≤ ub := by
    intro c _ hc y hy
    haveI : Nonempty c := ⟨⟨y, hy⟩⟩
    have hdir : Directed (· ⊇ ·) (fun z : c => Ici (z : X)) := by
      intro a b
      rcases hc.total a.2 b.2 with h | h
      · exact ⟨b, Ici_subset_Ici.2 h, subset_rfl⟩
      · exact ⟨a, subset_rfl, Ici_subset_Ici.2 h⟩
    have hne : ∀ z : c, (Ici (z : X)).Nonempty := fun z => ⟨z, le_rfl⟩
    have hcpt : ∀ z : c, IsCompact (Ici (z : X)) := fun z => (hclosed z).isCompact
    obtain ⟨ub, hub⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun z : c => Ici (z : X)) hdir hne hcpt (fun z => hclosed z)
    exact ⟨ub, Set.mem_univ ub, fun z hz => Set.mem_iInter.1 hub ⟨z, hz⟩⟩
  obtain ⟨m, hxm, hmax⟩ := zorn_le_nonempty₀ (Set.univ : Set X) hchain x (Set.mem_univ x)
  exact ⟨m, hxm, fun y hy => hmax.2 (Set.mem_univ y) hy⟩

end Zorn

section Maximizing

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The set of maximizers of `f` over the whole (compact) space. -/
def argmaxSet (f : X → ℝ) : Set X := {x | ∀ y, f y ≤ f x}

/-- A continuous function on a nonempty compact space has a maximizer. -/
theorem argmaxSet_nonempty [Nonempty X] {f : X → ℝ} (hf : Continuous f) :
    (argmaxSet f).Nonempty := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  exact ⟨x, fun y => hx (Set.mem_univ y)⟩

theorem argmaxSet_isClosed {f : X → ℝ} (hf : Continuous f) : IsClosed (argmaxSet f) := by
  have : argmaxSet f = ⋂ y, {x | f y ≤ f x} := by ext x; simp [argmaxSet]
  rw [this]
  exact isClosed_iInter fun y => isClosed_le continuous_const hf

/-- **Maximizing sequences converge to the maximizers.**  If `f (x n)` tends to the
value of `f` at a maximizer, the distance from `x n` to `argmaxSet f` tends to zero. -/
theorem tendsto_infDist_argmax_of_tendsto_sSup {f : X → ℝ} (hf : Continuous f)
    {m : X} (hm : m ∈ argmaxSet f) (x : ℕ → X)
    (hx : Tendsto (fun n => f (x n)) atTop (𝓝 (f m))) :
    Tendsto (fun n => infDist (x n) (argmaxSet f)) atTop (𝓝 0) := by
  by_contra hcon
  -- some `ε > 0` is exceeded infinitely often
  have hfreq : ∃ ε > 0, ∃ᶠ n in atTop, ε ≤ infDist (x n) (argmaxSet f) := by
    by_contra hall
    apply hcon
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h1 : ¬ ∃ᶠ n in atTop, ε ≤ infDist (x n) (argmaxSet f) := fun h => hall ⟨ε, hε, h⟩
    rw [Filter.not_frequently] at h1
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h1
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
    exact not_le.1 (hN n hn)
  obtain ⟨ε, hε, hfr⟩ := hfreq
  obtain ⟨φ, hφ, hφε⟩ := Filter.extraction_of_frequently_atTop hfr
  -- a convergent subsequence by compactness
  obtain ⟨a, -, ψ, hψ, hlim⟩ := isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (x (φ n)))
  -- its limit maximizes `f`
  have hfa : f a = f m := by
    have h1 : Tendsto (fun n => f (x (φ (ψ n)))) atTop (𝓝 (f a)) :=
      (hf.tendsto a).comp hlim
    have h2 : Tendsto (fun n => f (x (φ (ψ n)))) atTop (𝓝 (f m)) :=
      hx.comp ((hφ.comp hψ).tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  have ha : a ∈ argmaxSet f := fun y => hfa ▸ hm y
  -- but the subsequence stays `ε`-far from the maximizers, and `infDist` is continuous
  have hcont : Tendsto (fun n => infDist (x (φ (ψ n))) (argmaxSet f)) atTop
      (𝓝 (infDist a (argmaxSet f))) :=
    ((continuous_infDist_pt (argmaxSet f)).tendsto a).comp hlim
  have hzero : infDist a (argmaxSet f) = 0 := infDist_zero_of_mem ha
  have hge : ε ≤ infDist a (argmaxSet f) :=
    ge_of_tendsto hcont (Filter.Eventually.of_forall fun n => hφε (ψ n))
  rw [hzero] at hge
  exact absurd hge (not_le.2 hε)

/-- Maximizers of a strictly monotone function are maximal elements. -/
theorem argmax_subset_maximal_of_strictMono [Preorder X] {f : X → ℝ}
    (hstrict : ∀ a b : X, a < b → f a < f b) {m : X} (hm : m ∈ argmaxSet f) :
    ∀ y, m ≤ y → y ≤ m := by
  intro y hy
  by_contra hym
  exact absurd (hm y) (not_le.2 (hstrict m y (lt_of_le_not_ge hy hym)))

/-- **Asymptotic frontier completeness, abstract form.**  For a continuous, strictly
monotone objective on a compact metric space with a preorder, every maximizing
sequence converges to a subset of the maximal elements (the frontier). -/
theorem tendsto_infDist_frontier_of_strictMono [Preorder X] {f : X → ℝ} (hf : Continuous f)
    (hstrict : ∀ a b : X, a < b → f a < f b) {m : X} (hm : m ∈ argmaxSet f) (x : ℕ → X)
    (hx : Tendsto (fun n => f (x n)) atTop (𝓝 (f m))) :
    Tendsto (fun n => infDist (x n) {z : X | ∀ y, z ≤ y → y ≤ z}) atTop (𝓝 0) := by
  have hsub : argmaxSet f ⊆ {z : X | ∀ y, z ≤ y → y ≤ z} := fun z hz =>
    argmax_subset_maximal_of_strictMono hstrict hz
  have h := tendsto_infDist_argmax_of_tendsto_sSup hf hm x hx
  refine squeeze_zero (fun n => infDist_nonneg) (fun n => infDist_le_infDist_of_subset hsub ?_) h
  exact ⟨m, hm⟩

/-- **The operational form.**  Outside every `η`-neighbourhood of the maximizers, a
continuous function on a compact space is bounded away from its maximum. -/
theorem exists_gap_of_compact {f : X → ℝ} (hf : Continuous f) {m : X} (hm : m ∈ argmaxSet f)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ z : X, η ≤ infDist z (argmaxSet f) → f z ≤ f m - δ := by
  set S : Set X := {z | η ≤ infDist z (argmaxSet f)} with hS
  have hSc : IsClosed S := isClosed_le continuous_const (continuous_infDist_pt _)
  have hScpt : IsCompact S := hSc.isCompact
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    have hzS : z ∈ S := hz
    rw [hemp] at hzS
    exact absurd hzS (Set.notMem_empty z)
  obtain ⟨z₀, hz₀S, hz₀⟩ := hScpt.exists_isMaxOn hne hf.continuousOn
  have hz₀lt : f z₀ < f m := by
    rcases lt_or_eq_of_le (hm z₀) with h | h
    · exact h
    · exfalso
      have : z₀ ∈ argmaxSet f := fun y => h ▸ hm y
      have h0 : infDist z₀ (argmaxSet f) = 0 := infDist_zero_of_mem this
      have : η ≤ 0 := h0 ▸ hz₀S
      exact absurd this (not_le.2 hη)
  refine ⟨f m - f z₀, sub_pos.2 hz₀lt, fun z hz => ?_⟩
  have hle : f z ≤ f z₀ := (isMaxOn_iff.1 hz₀) z hz
  linarith

end Maximizing

section TwoBounds

/-!
### The two bounds (paper Definition `def:bounds`, Proposition `prop:bounds`)

Along a trajectory of a fixed policy, `U t` is the set of terminal experiments still
achievable by continuations that agree with the policy for `t` steps (antitone in `t`),
and the policy's own terminal experiment `k` lies in every `U t`.  *Safety* toward a
frontier point `F` is `F ∈ U t` for all `t`; *liveness* is maximality of `k` in the
limit upper set `⋂ t, U t`.  Frontier attainment (maximality in `U 0`) is exactly
safety toward a dominating frontier point plus liveness; antitonicity is not even
needed for the equivalence, only `⋂ t, U t ⊆ U 0`.
-/

variable {X : Type*} [Preorder X]

/-- **Safety + liveness ⇒ frontier attainment.**  If a maximal element `F` of `U 0`
dominating `k` stays achievable forever and `k` is maximal among what stays
achievable, then `k` is maximal in `U 0`. -/
theorem maximal_of_safe_and_live (U : ℕ → Set X) {k F : X}
    (hF : ∀ t, F ∈ U t) (hFmax : ∀ y ∈ U 0, F ≤ y → y ≤ F) (hkF : k ≤ F)
    (hlive : ∀ y ∈ ⋂ t, U t, k ≤ y → y ≤ k) :
    ∀ y ∈ U 0, k ≤ y → y ≤ k := by
  have hFk : F ≤ k := hlive F (Set.mem_iInter.2 hF) hkF
  intro y hy hky
  exact (hFmax y hy (hFk.trans hky)).trans hFk

/-- **Frontier attainment ⇔ safety toward a dominating frontier point + liveness.** -/
theorem maximal_iff_safe_and_live (U : ℕ → Set X) {k : X} (hk : ∀ t, k ∈ U t) :
    (∀ y ∈ U 0, k ≤ y → y ≤ k) ↔
      (∃ F, (∀ t, F ∈ U t) ∧ k ≤ F ∧ ∀ y ∈ U 0, F ≤ y → y ≤ F) ∧
        ∀ y ∈ ⋂ t, U t, k ≤ y → y ≤ k := by
  constructor
  · intro hmax
    refine ⟨⟨k, hk, le_rfl, hmax⟩, fun y hy hky => hmax y (Set.mem_iInter.1 hy 0) hky⟩
  · rintro ⟨⟨F, hF, hkF, hFmax⟩, hlive⟩
    exact maximal_of_safe_and_live U hF hFmax hkF hlive

/-- **The attained-top case.**  If the top of `U 0` stays achievable (safety) and the
policy is live, its terminal experiment is equivalent to the top. -/
theorem top_le_of_safe_and_live (U : ℕ → Set X) {k top : X} (hk : ∀ t, k ∈ U t)
    (htop : ∀ y ∈ U 0, y ≤ top) (hsafe : ∀ t, top ∈ U t)
    (hlive : ∀ y ∈ ⋂ t, U t, k ≤ y → y ≤ k) : top ≤ k :=
  hlive top (Set.mem_iInter.2 hsafe) (htop k (hk 0))

/-- **The ε split.**  For any directed distance satisfying the triangle inequality
(Le Cam's deficiency does), the distance from the terminal experiment `k` to a frontier
point `F` is at most the liveness loss `δ k E` plus the safety loss `δ E F`, for every
`E` still achievable in the limit. -/
theorem split_le_of_triangle {δ : X → X → ℝ}
    (htri : ∀ a b c : X, δ a c ≤ δ a b + δ b c) (k E F : X) :
    δ k F ≤ δ k E + δ E F :=
  htri k E F

end TwoBounds

end IdExp
