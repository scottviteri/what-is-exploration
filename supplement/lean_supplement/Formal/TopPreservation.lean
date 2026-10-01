/-
Abstract order lemmas behind the Blackwell "top-preservation" reading of
completeness (paper §2.2, §4): on any preorder with a feasible set that has a
greatest element, a monotone scalar objective that is strict at that top has
exactly the top's equivalence class as its argmax; and any strictly monotone
objective never selects a strictly dominated element (its maximizers lie on
the frontier).  Instances in the paper: mutual information, worst-pair
Hellinger separation, and deficiency to full revelation, each monotone under
garbling and strict at full revelation (Thms 7.1, 7.2, Prop. 2.6).

Also: Archimedean discounting cannot implement "terminal quality first" — a
reward stream that is zero for `D` steps has discounted value at most
`γ^D M/(1-γ)`, which is below any fixed positive value for `D` large enough.
-/
import Mathlib.Order.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.Antisymmetrization
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace IdExp

section Order

variable {X : Type*} [Preorder X]

/-- **Top preservation.**  If every feasible `x` is dominated by a feasible
`top`, `J` is monotone, and `J` is strict at the top on the feasible set
(`J x = J top` forces `top ≤ x`), then the maximizers of `J` over `S` are
exactly the feasible elements equivalent to `top`. -/
theorem argmax_eq_top_class {J : X → ℝ} (hmono : Monotone J) (S : Set X)
    (top : X) (htop : top ∈ S) (hdom : ∀ x ∈ S, x ≤ top)
    (hstrict : ∀ x ∈ S, J x = J top → top ≤ x) :
    {x | x ∈ S ∧ ∀ y ∈ S, J y ≤ J x} = {x | x ∈ S ∧ AntisymmRel (· ≤ ·) x top} := by
  ext x
  constructor
  · rintro ⟨hxS, hmax⟩
    have hle : J x ≤ J top := hmono (hdom x hxS)
    have hge : J top ≤ J x := hmax top htop
    exact ⟨hxS, hdom x hxS, hstrict x hxS (le_antisymm hle hge)⟩
  · rintro ⟨hxS, hxt, htx⟩
    refine ⟨hxS, fun y hy => ?_⟩
    calc J y ≤ J top := hmono (hdom y hy)
      _ ≤ J x := hmono htx

/-- **Frontier selection.**  A strictly monotone objective never selects a
strictly dominated element: every maximizer over `S` is maximal in `S`. -/
theorem maximizer_not_lt {J : X → ℝ} (hstrict : StrictMono J) {S : Set X} {x : X}
    (hmax : ∀ y ∈ S, J y ≤ J x) : ∀ y ∈ S, ¬ x < y := by
  intro y hy hlt
  exact absurd (hmax y hy) (not_le.2 (hstrict hlt))

end Order

section Archimedean

/-- A nonnegative reward stream bounded by `M` that vanishes for the first `D`
steps has every discounted partial sum bounded by `γ^D M / (1 - γ)`. -/
theorem discounted_sum_le_of_zero_before {γ M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r : ℕ → ℝ) (hr0 : ∀ t, 0 ≤ r t) (hrM : ∀ t, r t ≤ M) (D : ℕ)
    (hzero : ∀ t < D, r t = 0) (T : ℕ) :
    ∑ t ∈ Finset.range T, γ ^ t * r t ≤ γ ^ D * M / (1 - γ) := by
  classical
  have hM : 0 ≤ M := le_trans (hr0 0) (hrM 0)
  have hterm : ∀ t, γ ^ t * r t ≤ if D ≤ t then γ ^ t * M else 0 := by
    intro t
    by_cases ht : D ≤ t
    · rw [if_pos ht]
      exact mul_le_mul_of_nonneg_left (hrM t) (pow_nonneg hγ0 t)
    · rw [if_neg ht, hzero t (not_le.1 ht), mul_zero]
  calc ∑ t ∈ Finset.range T, γ ^ t * r t
      ≤ ∑ t ∈ Finset.range T, (if D ≤ t then γ ^ t * M else 0) :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = ∑ t ∈ Finset.Ico D T, γ ^ t * M := by
        rw [← Finset.sum_filter]
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        tauto
    _ = (∑ t ∈ Finset.Ico D T, γ ^ t) * M := by rw [Finset.sum_mul]
    _ ≤ γ ^ D / (1 - γ) * M :=
        mul_le_mul_of_nonneg_right (geom_sum_Ico_le_of_lt_one hγ0 hγ1) hM
    _ = γ ^ D * M / (1 - γ) := by ring

/-- **Archimedean discounting.**  For any fixed discount `γ < 1`, bound `M`, and
target value `v > 0`, a delay `D` exists beyond which every reward stream that
is silent for `D` steps is worth less than `v`.  So a discounted objective
prefers an early incomplete experiment worth `v` to any complete one delayed by
`D`, however the local reward is chosen. -/
theorem exists_delay_discounted_lt {γ M v : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : 0 ≤ M) (hv : 0 < v) :
    ∃ D : ℕ, ∀ (r : ℕ → ℝ), (∀ t, 0 ≤ r t) → (∀ t, r t ≤ M) →
      (∀ t < D, r t = 0) → ∀ T, ∑ t ∈ Finset.range T, γ ^ t * r t < v := by
  have h1γ : 0 < 1 - γ := sub_pos.2 hγ1
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one
    (show 0 < v * (1 - γ) / (M + 1) by positivity) hγ1
  refine ⟨D, fun r hr0 hrM hzero T => ?_⟩
  calc ∑ t ∈ Finset.range T, γ ^ t * r t
      ≤ γ ^ D * M / (1 - γ) := discounted_sum_le_of_zero_before hγ0 hγ1 r hr0 hrM D hzero T
    _ < v := by
        rw [div_lt_iff₀ h1γ]
        calc γ ^ D * M ≤ γ ^ D * (M + 1) := by
              exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hγ0 D)
          _ < v * (1 - γ) / (M + 1) * (M + 1) := by
              exact mul_lt_mul_of_pos_right hD (by positivity)
          _ = v * (1 - γ) := by field_simp

end Archimedean


/-! ### Winning regions as greatest fixed points

The identification winning region `W` of the paper (§6) is characterized by two
properties of the *block operator* `Φ` on sets of beliefs, `Φ S` = beliefs from
which some finite identification-safe `κ`-contracting tree has all its
positive-probability leaves in `S`: `W` is post-fixed (`W ≤ Φ W`, the block
extraction lemma) and every post-fixed set is winning (iterating blocks gives
`E[V_n] ≤ κ^n V_0`, hence identification).  Knaster–Tarski then makes `W` the
greatest fixed point of `Φ`.  The abstract order-theoretic step: -/

/-- A post-fixed point that contains every post-fixed point is the greatest fixed
point of a monotone map on a complete lattice. -/
theorem eq_gfp_of_postfixed_of_sound {β : Type*} [CompleteLattice β] (Φ : β →o β) (W : β)
    (hW : W ≤ Φ W) (hsound : ∀ S, S ≤ Φ S → S ≤ W) : W = OrderHom.gfp Φ :=
  le_antisymm (OrderHom.le_gfp Φ hW) (hsound _ (OrderHom.map_gfp Φ).ge)

/-- In particular such a `W` is a fixed point. -/
theorem fixed_of_postfixed_of_sound {β : Type*} [CompleteLattice β] (Φ : β →o β) (W : β)
    (hW : W ≤ Φ W) (hsound : ∀ S, S ≤ Φ S → S ≤ W) : Φ W = W := by
  rw [eq_gfp_of_postfixed_of_sound Φ W hW hsound]
  exact OrderHom.map_gfp Φ


/-! ### Prefix continuity: finite horizons approximate the terminal value

Paper Remark `rem:pc`: if an objective's values along the prefix chain are
monotone with supremum equal to the terminal value `M` (prefix continuity), and
the policy attains `M` in the limit, then it is `ε`-optimal from some finite
horizon on.  The abstract step is elementary and is what the indicator of the
top lacks (its finite-horizon values are all `0`, its supremum is `0 ≠ 1`). -/

/-- Monotone values with supremum `M` exceed `M - ε` from some horizon on. -/
theorem eventually_eps_optimal_of_prefixContinuous (a : ℕ → ℝ) (ha : Monotone a) (M : ℝ)
    (hsup : ⨆ t, a t = M) {ε : ℝ} (hε : 0 < ε) : ∃ T, ∀ t ≥ T, M - ε < a t := by
  have hlt : M - ε < ⨆ t, a t := by rw [hsup]; linarith
  obtain ⟨T, hT⟩ := exists_lt_of_lt_ciSup hlt
  exact ⟨T, fun t ht => lt_of_lt_of_le hT (ha ht)⟩

end IdExp

