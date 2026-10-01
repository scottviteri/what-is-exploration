import Mathlib

/-!
# Uniform prefix continuity on compact families: the ε-net core

Proposition "Uniform prefix continuity under compact domination"
(`Paper/draft/main.tex`, `prop:l1-prefix`; `TheoryDocs/native_test_geometry.tex`,
`prop:l1`) bounds `δ(K_{π,t}, K_{π,∞}) ≤ (1/2) sup_Q ‖E[f_Q | F_t] − f_Q‖₁` and sends
the right side to zero when the density family `{f_Q}` is compact in `L¹(P̄)`.

The abstract epsilon-net core is machine-checked here: a sequence of
1-Lipschitz (nonexpansive) self-maps of a pseudometric space that converges to the
identity pointwise converges uniformly on every compact set, by a finite ε-net.
`Formal.DominatedPrefix` supplies the full conditional-expectation instantiation,
regular conditional decoder, total-variation identity, displayed deficiency bound,
and convergence theorem.
-/

namespace IdExp

open Filter Metric Topology

/-- **Equi-nonexpansive pointwise convergence to the identity is uniform on compact
sets.**  Cover the compact set by finitely many `ε/3`-balls, wait until every center has
settled, and pay `2ε/3` for the trip to the nearest center and back. -/
theorem tendstoUniformlyOn_id_of_nonexpansive {X : Type*} [PseudoMetricSpace X]
    (T : ℕ → X → X) (hlip : ∀ t, LipschitzWith 1 (T t))
    (hpt : ∀ x, Tendsto (fun t => T t x) atTop (𝓝 x))
    {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t x => T t x) id atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨C, -, hCfin, hcover⟩ := hK.finite_cover_balls hε3
  have hev : ∀ᶠ n in atTop, ∀ c ∈ C, dist (T n c) c < ε / 3 := by
    rw [Filter.eventually_all_finite hCfin]
    intro c hc
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpt c) (ε / 3) hε3
    exact Filter.eventually_atTop.mpr ⟨N, hN⟩
  filter_upwards [hev] with n hn x hxK
  obtain ⟨c, hc, hxc⟩ : ∃ c ∈ C, x ∈ ball c (ε / 3) := by
    simpa using hcover hxK
  have h1 : dist x c < ε / 3 := mem_ball.mp hxc
  have h2 : dist c (T n c) < ε / 3 := by
    rw [dist_comm]; exact hn c hc
  have h3 : dist (T n c) (T n x) ≤ dist c x := by
    simpa using (hlip n).dist_le_mul c x
  have h3' : dist (T n c) (T n x) < ε / 3 := by
    refine lt_of_le_of_lt h3 ?_
    rwa [dist_comm]
  calc
    dist (id x) (T n x) = dist x (T n x) := rfl
    _ ≤ dist x c + dist c (T n c) + dist (T n c) (T n x) :=
        dist_triangle4 x c (T n c) (T n x)
    _ < ε / 3 + ε / 3 + ε / 3 := by
        exact add_lt_add (add_lt_add h1 h2) h3'
    _ = ε := by ring

end IdExp
