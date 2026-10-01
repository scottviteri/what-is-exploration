import Formal.QuadraticReverseBound

/-!
# A spread modulus for every continuous strictly convex potential

For a potential `Φ` continuous and strictly convex on the world simplex, a
finitely supported law on the simplex with a small Jensen gap
`∑ c_s Φ(x_s) − Φ(∑ c_s x_s)` has a small spread `∑ c_s ‖x_s − mean‖²`,
uniformly over the number of atoms.  No measure-theoretic compactness is
used: compactness of the finite-dimensional simplex gives a positive
midpoint gap `η(r)` for pairs at ℓ¹ distance at least `r`; Jensen over
independent pairs gives `Jensen gap ≥ ∑ c_s c_{s'} midGap(x_s, x_{s'})`; and
a Markov-type count turns a large mean pairwise distance into a large gap.

The second half applies this to an exact garbling `F ↦ FG` on any finite
alphabets: if the potential lost by the garbling is small then the expected
squared posterior movement, which is the quadratic potential lost, is small.
-/

namespace IdExp

open Finset

universe u v

section Simplex

variable {Θ : Type*} [Fintype Θ]

/-- ℓ¹ distance on world vectors. -/
def l1 (x y : Θ → ℝ) : ℝ := ∑ θ, |x θ - y θ|

/-- The midpoint Jensen gap of `Φ` at a pair. -/
noncomputable def midGap (Φ : (Θ → ℝ) → ℝ) (x y : Θ → ℝ) : ℝ :=
  (Φ x + Φ y) / 2 - Φ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)

theorem l1_nonneg (x y : Θ → ℝ) : 0 ≤ l1 x y :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_self (x : Θ → ℝ) : l1 x x = 0 := by simp [l1]

theorem l1_le_two {x y : Θ → ℝ} (hx : x ∈ stdSimplex ℝ Θ) (hy : y ∈ stdSimplex ℝ Θ) :
    l1 x y ≤ 2 := by
  unfold l1
  calc ∑ θ, |x θ - y θ| ≤ ∑ θ, (x θ + y θ) :=
        Finset.sum_le_sum fun θ _ => (abs_sub _ _).trans (by
          rw [abs_of_nonneg (hx.1 θ), abs_of_nonneg (hy.1 θ)])
    _ = 2 := by rw [Finset.sum_add_distrib, hx.2, hy.2]; norm_num

theorem continuous_l1 : Continuous fun p : (Θ → ℝ) × (Θ → ℝ) => l1 p.1 p.2 := by
  unfold l1
  fun_prop

theorem midpoint_mem_stdSimplex {x y : Θ → ℝ} (hx : x ∈ stdSimplex ℝ Θ)
    (hy : y ∈ stdSimplex ℝ Θ) : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ stdSimplex ℝ Θ :=
  (convex_stdSimplex ℝ Θ) hx hy (by norm_num) (by norm_num) (by norm_num)

theorem midGap_nonneg (Φ : (Θ → ℝ) → ℝ) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ) {x y : Θ → ℝ}
    (hx : x ∈ stdSimplex ℝ Θ) (hy : y ∈ stdSimplex ℝ Θ) : 0 ≤ midGap Φ x y := by
  have h := hΦ.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  unfold midGap
  linarith

theorem midGap_pos (Φ : (Θ → ℝ) → ℝ) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ) {x y : Θ → ℝ}
    (hx : x ∈ stdSimplex ℝ Θ) (hy : y ∈ stdSimplex ℝ Θ) (hne : x ≠ y) : 0 < midGap Φ x y := by
  have h := hΦ.2 hx hy hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at h
  unfold midGap
  linarith

/-- **Positive midpoint gap at every positive ℓ¹ separation**, by compactness of
the finite-dimensional simplex. -/
theorem exists_midGap_pos (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ) (r : ℝ) (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ stdSimplex ℝ Θ, ∀ y ∈ stdSimplex ℝ Θ, r ≤ l1 x y →
      η ≤ midGap Φ x y := by
  set K : Set ((Θ → ℝ) × (Θ → ℝ)) :=
    (stdSimplex ℝ Θ ×ˢ stdSimplex ℝ Θ) ∩ {p | r ≤ l1 p.1 p.2} with hKdef
  by_cases hK : K.Nonempty
  · have hKc : IsCompact K := by
      refine ((isCompact_stdSimplex ℝ Θ).prod (isCompact_stdSimplex ℝ Θ)).of_isClosed_subset ?_
        Set.inter_subset_left
      exact ((isClosed_stdSimplex ℝ Θ).prod (isClosed_stdSimplex ℝ Θ)).inter
        (isClosed_le continuous_const continuous_l1)
    have hmem : ∀ p ∈ K, p.1 ∈ stdSimplex ℝ Θ ∧ p.2 ∈ stdSimplex ℝ Θ := fun p hp => hp.1
    have hcont : ContinuousOn (fun p : (Θ → ℝ) × (Θ → ℝ) => midGap Φ p.1 p.2) K := by
      have h1 : ContinuousOn (fun p : (Θ → ℝ) × (Θ → ℝ) => Φ p.1) K :=
        hΦc.comp continuousOn_fst fun p hp => (hmem p hp).1
      have h2 : ContinuousOn (fun p : (Θ → ℝ) × (Θ → ℝ) => Φ p.2) K :=
        hΦc.comp continuousOn_snd fun p hp => (hmem p hp).2
      have h3 : ContinuousOn
          (fun p : (Θ → ℝ) × (Θ → ℝ) => Φ ((1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2)) K := by
        refine hΦc.comp (f := fun p : (Θ → ℝ) × (Θ → ℝ) => (1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2)
          (by fun_prop) fun p hp => midpoint_mem_stdSimplex (hmem p hp).1 (hmem p hp).2
      exact ((h1.add h2).div_const 2).sub h3
    obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hK hcont
    refine ⟨midGap Φ p₀.1 p₀.2, ?_, fun x hx y hy hxy => hmin (show (x, y) ∈ K from ⟨⟨hx, hy⟩, hxy⟩)⟩
    have hne : p₀.1 ≠ p₀.2 := by
      intro h
      have h2 : r ≤ l1 p₀.1 p₀.2 := hp₀.2
      rw [h, l1_self] at h2
      linarith
    exact midGap_pos Φ hΦ hp₀.1.1 hp₀.1.2 hne
  · refine ⟨1, one_pos, fun x hx y hy hxy => ?_⟩
    exact (hK ⟨(x, y), ⟨hx, hy⟩, hxy⟩).elim

/-! ## Finitely supported laws on the simplex -/

variable {S : Type*} [Fintype S]

theorem sum_pair_weights_half (c : S → ℝ) (hc : ∑ s, c s = 1) (f : S → ℝ) :
    ∑ s, ∑ s', c s * c s' * ((f s + f s') / 2) = ∑ s, c s * f s := by
  have h1 : ∀ s, ∑ s', c s * c s' * ((f s + f s') / 2) =
      (c s * f s) / 2 + c s * (∑ s', c s' * f s') / 2 := by
    intro s
    have : ∀ s', c s * c s' * ((f s + f s') / 2) =
        (c s * f s) * c s' / 2 + c s * (c s' * f s') / 2 := fun s' => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hc, mul_one, ← Finset.sum_div,
      ← Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul, hc, one_mul]
  ring

theorem sum_pair_weights_eq_one (c : S → ℝ) (hc : ∑ s, c s = 1) :
    ∑ p : S × S, c p.1 * c p.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hc, mul_one]
  exact hc

omit [Fintype Θ] in
/-- The mean of a finitely supported law is the mean of the midpoints of
independent pairs. -/
theorem mean_eq_sum_pair_midpoints (c : S → ℝ) (hc : ∑ s, c s = 1) (x : S → Θ → ℝ) :
    ∑ s, c s • x s =
      ∑ p : S × S, (c p.1 * c p.2) • ((1 / 2 : ℝ) • x p.1 + (1 / 2 : ℝ) • x p.2) := by
  funext θ
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Fintype.sum_prod_type]
  rw [← sum_pair_weights_half c hc (fun s => x s θ)]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  ring

/-- **Pairwise Jensen**: the Jensen gap of a finitely supported law is at
least the mean midpoint gap over independent pairs. -/
theorem sum_pair_midGap_le_gap (Φ : (Θ → ℝ) → ℝ) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (c : S → ℝ) (hc : IsDist c) (x : S → Θ → ℝ) (hx : ∀ s, x s ∈ stdSimplex ℝ Θ) :
    ∑ s, ∑ s', c s * c s' * midGap Φ (x s) (x s') ≤
      ∑ s, c s * Φ (x s) - Φ (∑ s, c s • x s) := by
  have hJ := hΦ.map_sum_le (t := (Finset.univ : Finset (S × S))) (w := fun p => c p.1 * c p.2)
    (p := fun p => (1 / 2 : ℝ) • x p.1 + (1 / 2 : ℝ) • x p.2)
    (fun p _ => mul_nonneg (hc.1 p.1) (hc.1 p.2)) (sum_pair_weights_eq_one c hc.2)
    (fun p _ => midpoint_mem_stdSimplex (hx p.1) (hx p.2))
  rw [← mean_eq_sum_pair_midpoints c hc.2 x] at hJ
  simp only [smul_eq_mul, Fintype.sum_prod_type] at hJ
  have hval : ∑ s, ∑ s', c s * c s' * Φ ((1 / 2 : ℝ) • x s + (1 / 2 : ℝ) • x s') =
      ∑ s, c s * Φ (x s) - ∑ s, ∑ s', c s * c s' * midGap Φ (x s) (x s') := by
    rw [← sum_pair_weights_half c hc.2 (fun s => Φ (x s)), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    unfold midGap
    ring
  linarith

/-- Markov-type count: if the mean pairwise ℓ¹ distance is `U` then pairs at
distance at least `U / 2` carry weight at least `U / 4`. -/
theorem sum_pair_weights_far_ge (c : S → ℝ) (hc : IsDist c) (x : S → Θ → ℝ)
    (hx : ∀ s, x s ∈ stdSimplex ℝ Θ) {r : ℝ} (hr : 0 ≤ r) :
    (∑ s, ∑ s', c s * c s' * l1 (x s) (x s') - r) / 2 ≤
      ∑ p ∈ (Finset.univ : Finset (S × S)).filter (fun p => r ≤ l1 (x p.1) (x p.2)),
        c p.1 * c p.2 := by
  have hw : ∀ p : S × S, 0 ≤ c p.1 * c p.2 := fun p => mul_nonneg (hc.1 p.1) (hc.1 p.2)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (S × S))
    (fun p => r ≤ l1 (x p.1) (x p.2)) (fun p => c p.1 * c p.2 * l1 (x p.1) (x p.2))
  have hU : ∑ s, ∑ s', c s * c s' * l1 (x s) (x s') =
      ∑ p : S × S, c p.1 * c p.2 * l1 (x p.1) (x p.2) :=
    (Fintype.sum_prod_type (fun p : S × S => c p.1 * c p.2 * l1 (x p.1) (x p.2))).symm
  have hfar : ∑ p ∈ Finset.univ.filter (fun p : S × S => r ≤ l1 (x p.1) (x p.2)),
      c p.1 * c p.2 * l1 (x p.1) (x p.2) ≤
      ∑ p ∈ Finset.univ.filter (fun p : S × S => r ≤ l1 (x p.1) (x p.2)), c p.1 * c p.2 * 2 :=
    Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (l1_le_two (hx p.1) (hx p.2)) (hw p)
  have hnear : ∑ p ∈ Finset.univ.filter (fun p : S × S => ¬ r ≤ l1 (x p.1) (x p.2)),
      c p.1 * c p.2 * l1 (x p.1) (x p.2) ≤
      ∑ p ∈ Finset.univ.filter (fun p : S × S => ¬ r ≤ l1 (x p.1) (x p.2)), c p.1 * c p.2 * r :=
    Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left
      (le_of_lt (not_le.1 (Finset.mem_filter.1 hp).2)) (hw p)
  have hnear1 : ∑ p ∈ Finset.univ.filter (fun p : S × S => ¬ r ≤ l1 (x p.1) (x p.2)),
      c p.1 * c p.2 ≤ 1 := by
    rw [← sum_pair_weights_eq_one c hc.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => hw p
  rw [← Finset.sum_mul] at hfar hnear
  rw [hU, ← hsplit]
  nlinarith [hfar, hnear, hnear1, hr]

theorem coord_le_one {x : Θ → ℝ} (hx : x ∈ stdSimplex ℝ Θ) (θ : Θ) : x θ ≤ 1 := by
  have h := Finset.single_le_sum (f := x) (fun θ' _ => hx.1 θ') (Finset.mem_univ θ)
  rw [hx.2] at h
  exact h

/-- The spread about the mean is at most the mean pairwise ℓ¹ distance. -/
theorem spread_le_pair_l1 (c : S → ℝ) (hc : IsDist c) (x : S → Θ → ℝ)
    (hx : ∀ s, x s ∈ stdSimplex ℝ Θ) :
    ∑ s, c s * ∑ θ, (x s θ - (∑ s', c s' • x s') θ) ^ 2 ≤
      ∑ s, ∑ s', c s * c s' * l1 (x s) (x s') := by
  have hm : (∑ s', c s' • x s') ∈ stdSimplex ℝ Θ :=
    (convex_stdSimplex ℝ Θ).sum_mem (fun s _ => hc.1 s) hc.2 (fun s _ => hx s)
  refine Finset.sum_le_sum fun s _ => ?_
  have hxs := hx s
  have hd : ∀ θ, (x s θ - (∑ s', c s' • x s') θ) ^ 2 ≤ |x s θ - (∑ s', c s' • x s') θ| := by
    intro θ
    have h1 : |x s θ - (∑ s', c s' • x s') θ| ≤ 1 := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [hm.1 θ, coord_le_one hxs θ]
      · linarith [hxs.1 θ, coord_le_one hm θ]
    have h0 := abs_nonneg (x s θ - (∑ s', c s' • x s') θ)
    rw [← sq_abs]
    nlinarith
  have hb : l1 (x s) (∑ s', c s' • x s') ≤ ∑ s', c s' * l1 (x s) (x s') := by
    unfold l1
    calc ∑ θ, |x s θ - (∑ s', c s' • x s') θ|
        = ∑ θ, |∑ s', c s' * (x s θ - x s' θ)| := by
          refine Finset.sum_congr rfl fun θ _ => ?_
          congr 1
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
            Finset.sum_sub_distrib, ← Finset.sum_mul, hc.2, one_mul]
      _ ≤ ∑ θ, ∑ s', c s' * |x s θ - x s' θ| := by
          refine Finset.sum_le_sum fun θ _ => (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [abs_mul, abs_of_nonneg (hc.1 s')]
      _ = ∑ s', c s' * ∑ θ, |x s θ - x s' θ| := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
  calc c s * ∑ θ, (x s θ - (∑ s', c s' • x s') θ) ^ 2
      ≤ c s * l1 (x s) (∑ s', c s' • x s') :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun θ _ => hd θ) (hc.1 s)
    _ ≤ c s * ∑ s', c s' * l1 (x s) (x s') := mul_le_mul_of_nonneg_left hb (hc.1 s)
    _ = ∑ s', c s * c s' * l1 (x s) (x s') := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring

/-- **The spread modulus.**  Given a positive midpoint gap `ηm` at ℓ¹
separation `v / 2`, every finitely supported law on the simplex whose Jensen
gap is below `ηm v / 4` has spread below `v`. -/
theorem spread_lt_of_gap_lt (Φ : (Θ → ℝ) → ℝ) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    {v ηm : ℝ} (hv : 0 < v) (hηm : 0 < ηm)
    (hmid : ∀ x ∈ stdSimplex ℝ Θ, ∀ y ∈ stdSimplex ℝ Θ, v / 2 ≤ l1 x y → ηm ≤ midGap Φ x y)
    (c : S → ℝ) (hc : IsDist c) (x : S → Θ → ℝ) (hx : ∀ s, x s ∈ stdSimplex ℝ Θ)
    (hG : ∑ s, c s * Φ (x s) - Φ (∑ s, c s • x s) < ηm * v / 4) :
    ∑ s, c s * ∑ θ, (x s θ - (∑ s', c s' • x s') θ) ^ 2 < v := by
  have hVU := spread_le_pair_l1 c hc x hx
  suffices hUv : ∑ s, ∑ s', c s * c s' * l1 (x s) (x s') < v by linarith
  by_contra hcon
  have hcon' : v ≤ ∑ s, ∑ s', c s * c s' * l1 (x s) (x s') := not_lt.1 hcon
  have hfar := sum_pair_weights_far_ge c hc x hx (r := v / 2) (by linarith)
  have hgap := sum_pair_midGap_le_gap Φ hΦ c hc x hx
  have hw : ∀ p : S × S, 0 ≤ c p.1 * c p.2 := fun p => mul_nonneg (hc.1 p.1) (hc.1 p.2)
  have hlow : ηm * ∑ p ∈ (Finset.univ : Finset (S × S)).filter
      (fun p => v / 2 ≤ l1 (x p.1) (x p.2)), c p.1 * c p.2 ≤
      ∑ s, ∑ s', c s * c s' * midGap Φ (x s) (x s') := by
    rw [Finset.mul_sum, ← Fintype.sum_prod_type (fun p : S × S => c p.1 * c p.2 * midGap Φ (x p.1) (x p.2))]
    calc ∑ p ∈ Finset.univ.filter (fun p : S × S => v / 2 ≤ l1 (x p.1) (x p.2)),
          ηm * (c p.1 * c p.2)
        ≤ ∑ p ∈ Finset.univ.filter (fun p : S × S => v / 2 ≤ l1 (x p.1) (x p.2)),
          c p.1 * c p.2 * midGap Φ (x p.1) (x p.2) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hmid _ (hx p.1) _ (hx p.2) (Finset.mem_filter.1 hp).2)
            (hw p)
      _ ≤ ∑ p : S × S, c p.1 * c p.2 * midGap Φ (x p.1) (x p.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ =>
            mul_nonneg (hw p) (midGap_nonneg Φ hΦ (hx p.1) (hx p.2))
  nlinarith [hlow, hgap, hfar, hcon']

end Simplex

/-! ## Application to an exact garbling -/

section Garbling

variable {Θ : Type v} [Fintype Θ] {S T : Type u} [Fintype S] [Fintype T]

/-- The posterior atom of a signal, with the prior at null mass so that every
atom lies in the simplex. -/
noncomputable def atom (α : Θ → ℝ) (F : FiniteExperiment Θ S) (s : S) : Θ → ℝ :=
  if finiteBayesMass α F s = 0 then α else finiteBayesPosterior α F s

theorem atom_mem_simplex (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (s : S) : atom α F s ∈ stdSimplex ℝ Θ := by
  unfold atom
  split_ifs with h
  · exact hα
  · exact finiteBayesPosterior_mem_simplex α F hα.1 (fun θ s => (hF θ).1 s) s h

omit [Fintype S] [Fintype T] in
theorem garbleJoint_mul_atom (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) (s : S)
    (t : T) (θ : Θ) :
    garbleJoint α F G s t * atom α F s θ = garbleJoint α F G s t * finiteBayesPosterior α F s θ := by
  unfold atom garbleJoint
  split_ifs with h
  · rw [h]
    ring
  · rfl

theorem sum_garbleJoint_mul_posterior (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (t : T) (θ : Θ) :
    ∑ s, garbleJoint α F G s t * finiteBayesPosterior α F s θ =
      finiteBayesMass α (finiteDecisionLaw F G) t *
        finiteBayesPosterior α (finiteDecisionLaw F G) t θ := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  rw [finiteBayesMass_mul_posterior α hα.1 (finiteDecisionLaw F G) (fun θ t => (hFG θ).1 t) t θ]
  show _ = α θ * ∑ s, F θ s * G s t
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold garbleJoint
  rw [mul_comm (finiteBayesMass α F s) (G s t), mul_assoc,
    finiteBayesMass_mul_posterior α hα.1 F (fun θ s => (hF θ).1 s) s θ]
  ring

theorem garbleJoint_eq_zero_of_mass_zero (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (t : T)
    (ht : finiteBayesMass α (finiteDecisionLaw F G) t = 0) (s : S) : garbleJoint α F G s t = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun s _ => garbleJoint_nonneg α hα.1 F hF G hG s t).1
    (by rw [sum_garbleJoint_left]; exact ht) s (Finset.mem_univ s)

/-- Conditional weights of signals given the garbled symbol. -/
noncomputable def condW (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) (t : T) (s : S) :
    ℝ :=
  garbleJoint α F G s t / finiteBayesMass α (finiteDecisionLaw F G) t

theorem condW_isDist (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (t : T)
    (ht : finiteBayesMass α (finiteDecisionLaw F G) t ≠ 0) : IsDist (condW α F G t) := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  refine ⟨fun s => div_nonneg (garbleJoint_nonneg α hα.1 F hF G hG s t)
    (finiteBayesMass_nonneg α _ hα.1 (fun θ t => (hFG θ).1 t) t), ?_⟩
  unfold condW
  rw [← Finset.sum_div, sum_garbleJoint_left, div_self ht]

theorem sum_condW_smul_atom (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (t : T)
    (ht : finiteBayesMass α (finiteDecisionLaw F G) t ≠ 0) :
    ∑ s, condW α F G t s • atom α F s = finiteBayesPosterior α (finiteDecisionLaw F G) t := by
  funext θ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold condW
  have h : ∀ s, garbleJoint α F G s t / finiteBayesMass α (finiteDecisionLaw F G) t *
      atom α F s θ = (garbleJoint α F G s t * finiteBayesPosterior α F s θ) /
        finiteBayesMass α (finiteDecisionLaw F G) t := by
    intro s
    rw [div_mul_eq_mul_div, garbleJoint_mul_atom]
  simp_rw [h]
  rw [← Finset.sum_div, sum_garbleJoint_mul_posterior α hα F hF G hG t θ,
    mul_div_cancel_left₀ _ ht]

/-- The conditional Jensen gap at a garbled symbol. -/
noncomputable def condGap (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (F : FiniteExperiment Θ S)
    (G : S → T → ℝ) (t : T) : ℝ :=
  if finiteBayesMass α (finiteDecisionLaw F G) t = 0 then 0
  else ∑ s, condW α F G t s * Φ (atom α F s) - Φ (finiteBayesPosterior α (finiteDecisionLaw F G) t)

/-- The conditional squared spread at a garbled symbol. -/
noncomputable def condSpread (α : Θ → ℝ) (F : FiniteExperiment Θ S) (G : S → T → ℝ) (t : T) :
    ℝ :=
  if finiteBayesMass α (finiteDecisionLaw F G) t = 0 then 0
  else ∑ s, condW α F G t s *
    ∑ θ, (atom α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2

theorem mass_mul_condGap (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) (t : T) :
    finiteBayesMass α (finiteDecisionLaw F G) t * condGap Φ α F G t =
      ∑ s, garbleJoint α F G s t * Φ (atom α F s) -
        finiteBayesMass α (finiteDecisionLaw F G) t *
          Φ (finiteBayesPosterior α (finiteDecisionLaw F G) t) := by
  unfold condGap
  split_ifs with ht
  · rw [ht, zero_mul, zero_mul, sub_zero]
    symm
    exact Finset.sum_eq_zero fun s _ => by
      rw [garbleJoint_eq_zero_of_mass_zero α hα F hF G hG t ht s, zero_mul]
  · rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold condW
    field_simp

theorem sum_mass_mul_condGap (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) :
    ∑ t, finiteBayesMass α (finiteDecisionLaw F G) t * condGap Φ α F G t =
      finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw F G) := by
  simp_rw [mass_mul_condGap Φ α hα F hF G hG]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul, sum_garbleJoint_right α F G hG s]
  unfold atom
  split_ifs with h
  · rw [h, zero_mul, zero_mul]
  · rfl

theorem mass_mul_condSpread (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (t : T) :
    finiteBayesMass α (finiteDecisionLaw F G) t * condSpread α F G t =
      ∑ s, garbleJoint α F G s t *
        ∑ θ, (finiteBayesPosterior α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2 := by
  unfold condSpread
  split_ifs with ht
  · rw [mul_zero]
    symm
    exact Finset.sum_eq_zero fun s _ => by
      rw [garbleJoint_eq_zero_of_mass_zero α hα F hF G hG t ht s, zero_mul]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold condW
    by_cases hs : finiteBayesMass α F s = 0
    · have hw : garbleJoint α F G s t = 0 := by
        unfold garbleJoint
        rw [hs, zero_mul]
      rw [hw]
      simp
    · have hatom : atom α F s = finiteBayesPosterior α F s := by
        unfold atom
        rw [if_neg hs]
      rw [hatom]
      field_simp

theorem sum_mass_mul_condSpread (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) :
    ∑ t, finiteBayesMass α (finiteDecisionLaw F G) t * condSpread α F G t =
      finiteBayesPotential posteriorQuadraticPotential α F -
        finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G) := by
  simp_rw [mass_mul_condSpread α hα F hF G hG]
  rw [Finset.sum_comm]
  exact sum_garbleJoint_sq_dist α hα F hF G hG

theorem sq_dist_le_two {x y : Θ → ℝ} (hx : x ∈ stdSimplex ℝ Θ) (hy : y ∈ stdSimplex ℝ Θ) :
    ∑ θ, (x θ - y θ) ^ 2 ≤ 2 := by
  calc ∑ θ, (x θ - y θ) ^ 2 ≤ ∑ θ, |x θ - y θ| := by
        refine Finset.sum_le_sum fun θ _ => ?_
        have h1 : |x θ - y θ| ≤ 1 := by
          rw [abs_sub_le_iff]
          constructor
          · linarith [hy.1 θ, coord_le_one hx θ]
          · linarith [hx.1 θ, coord_le_one hy θ]
        have h0 := abs_nonneg (x θ - y θ)
        rw [← sq_abs]
        nlinarith
    _ ≤ 2 := l1_le_two hx hy

theorem condSpread_le_two (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S)
    (hF : IsFiniteExperiment F) (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) (t : T) :
    condSpread α F G t ≤ 2 := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  unfold condSpread
  split_ifs with ht
  · norm_num
  · have hc := condW_isDist α hα F hF G hG t ht
    have hq : finiteBayesPosterior α (finiteDecisionLaw F G) t ∈ stdSimplex ℝ Θ :=
      finiteBayesPosterior_mem_simplex α _ hα.1 (fun θ t => (hFG θ).1 t) t ht
    calc ∑ s, condW α F G t s *
          ∑ θ, (atom α F s θ - finiteBayesPosterior α (finiteDecisionLaw F G) t θ) ^ 2
        ≤ ∑ s, condW α F G t s * 2 :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
            (sq_dist_le_two (atom_mem_simplex α hα F hF s) hq) (hc.1 s)
      _ = 2 := by rw [← Finset.sum_mul, hc.2, one_mul]

theorem condGap_nonneg (Φ : (Θ → ℝ) → ℝ) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ) (α : Θ → ℝ)
    (hα : IsDist α) (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) (t : T) : 0 ≤ condGap Φ α F G t := by
  unfold condGap
  split_ifs with ht
  · exact le_rfl
  · have hc := condW_isDist α hα F hF G hG t ht
    have hJ := hΦ.map_sum_le (t := (Finset.univ : Finset S)) (w := condW α F G t)
      (p := atom α F) (fun s _ => hc.1 s) hc.2 (fun s _ => atom_mem_simplex α hα F hF s)
    rw [sum_condW_smul_atom α hα F hF G hG t ht] at hJ
    simp only [smul_eq_mul] at hJ
    linarith

theorem condSpread_lt_of_condGap_lt (Φ : (Θ → ℝ) → ℝ) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F)
    (G : S → T → ℝ) (hG : G ∈ stochasticRules S T) {v ηm : ℝ} (hv : 0 < v) (hηm : 0 < ηm)
    (hmid : ∀ x ∈ stdSimplex ℝ Θ, ∀ y ∈ stdSimplex ℝ Θ, v / 2 ≤ l1 x y → ηm ≤ midGap Φ x y)
    (t : T) (hgap : condGap Φ α F G t < ηm * v / 4) : condSpread α F G t < v := by
  unfold condGap at hgap
  unfold condSpread
  split_ifs at hgap ⊢ with ht
  · exact hv
  · have hc := condW_isDist α hα F hF G hG t ht
    have h := spread_lt_of_gap_lt Φ hΦ hv hηm hmid (condW α F G t) hc (atom α F)
      (fun s => atom_mem_simplex α hα F hF s)
      (by rw [sum_condW_smul_atom α hα F hF G hG t ht]; exact hgap)
    rw [sum_condW_smul_atom α hα F hF G hG t ht] at h
    exact h

/-- **Small potential loss forces small squared posterior movement**, for any
convex potential with a positive midpoint gap at separation `v / 4`. -/
theorem quadGap_lt_of_potentialGap_lt_aux (Φ : (Θ → ℝ) → ℝ)
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ) (α : Θ → ℝ) (hα : IsDist α)
    (F : FiniteExperiment Θ S) (hF : IsFiniteExperiment F) (G : S → T → ℝ)
    (hG : G ∈ stochasticRules S T) {v ηm : ℝ} (hv : 0 < v) (hηm : 0 < ηm)
    (hmid : ∀ x ∈ stdSimplex ℝ Θ, ∀ y ∈ stdSimplex ℝ Θ, v / 4 ≤ l1 x y → ηm ≤ midGap Φ x y)
    (hgap : finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw F G) <
      v * (ηm * (v / 2) / 4) / 4) :
    finiteBayesPotential posteriorQuadraticPotential α F -
      finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G) < v := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  set ηL := ηm * (v / 2) / 4 with hηL
  have hηLpos : 0 < ηL := by positivity
  rw [← sum_mass_mul_condSpread α hα F hF G hG]
  rw [← sum_mass_mul_condGap Φ α hα F hF G hG] at hgap
  have hm0 : ∀ t, 0 ≤ finiteBayesMass α (finiteDecisionLaw F G) t :=
    fun t => finiteBayesMass_nonneg α _ hα.1 (fun θ t => (hFG θ).1 t) t
  have hm1 : ∑ t, finiteBayesMass α (finiteDecisionLaw F G) t = 1 :=
    (finiteBayesMass_isDist α hα _ hFG).2
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset T)
    (fun t => condSpread α F G t < v / 2)
    (fun t => finiteBayesMass α (finiteDecisionLaw F G) t * condSpread α F G t)
  have hA : ∑ t ∈ Finset.univ.filter (fun t => condSpread α F G t < v / 2),
      finiteBayesMass α (finiteDecisionLaw F G) t * condSpread α F G t ≤
      (∑ t ∈ Finset.univ.filter (fun t => condSpread α F G t < v / 2),
        finiteBayesMass α (finiteDecisionLaw F G) t) * (v / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun t ht =>
      mul_le_mul_of_nonneg_left (le_of_lt (Finset.mem_filter.1 ht).2) (hm0 t)
  have hA1 : ∑ t ∈ Finset.univ.filter (fun t => condSpread α F G t < v / 2),
      finiteBayesMass α (finiteDecisionLaw F G) t ≤ 1 := by
    rw [← hm1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun t _ _ => hm0 t
  have hB : ∑ t ∈ Finset.univ.filter (fun t => ¬ condSpread α F G t < v / 2),
      finiteBayesMass α (finiteDecisionLaw F G) t * condSpread α F G t ≤
      (∑ t ∈ Finset.univ.filter (fun t => ¬ condSpread α F G t < v / 2),
        finiteBayesMass α (finiteDecisionLaw F G) t) * 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (condSpread_le_two α hα F hF G hG t) (hm0 t)
  have hB' : (∑ t ∈ Finset.univ.filter (fun t => ¬ condSpread α F G t < v / 2),
      finiteBayesMass α (finiteDecisionLaw F G) t) * ηL ≤
      ∑ t, finiteBayesMass α (finiteDecisionLaw F G) t * condGap Φ α F G t := by
    rw [Finset.sum_mul]
    calc ∑ t ∈ Finset.univ.filter (fun t => ¬ condSpread α F G t < v / 2),
          finiteBayesMass α (finiteDecisionLaw F G) t * ηL
        ≤ ∑ t ∈ Finset.univ.filter (fun t => ¬ condSpread α F G t < v / 2),
          finiteBayesMass α (finiteDecisionLaw F G) t * condGap Φ α F G t := by
          refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (hm0 t)
          by_contra hlt
          have hlt' : condGap Φ α F G t < ηm * (v / 2) / 4 := not_le.1 hlt
          have := condSpread_lt_of_condGap_lt Φ hΦ α hα F hF G hG (half_pos hv) hηm
            (by intro x hx y hy hxy; exact hmid x hx y hy (by linarith)) t hlt'
          exact (Finset.mem_filter.1 ht).2 this
      _ ≤ ∑ t, finiteBayesMass α (finiteDecisionLaw F G) t * condGap Φ α F G t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun t _ _ =>
            mul_nonneg (hm0 t) (condGap_nonneg Φ hΦ α hα F hF G hG t)
  have hNeg : ∑ t ∈ Finset.univ.filter (fun t => ¬ condSpread α F G t < v / 2),
      finiteBayesMass α (finiteDecisionLaw F G) t ≤
      (∑ t, finiteBayesMass α (finiteDecisionLaw F G) t * condGap Φ α F G t) / ηL := by
    rw [le_div_iff₀ hηLpos]
    exact hB'
  have hgap' : (∑ t, finiteBayesMass α (finiteDecisionLaw F G) t * condGap Φ α F G t) / ηL <
      v / 4 := by
    rw [div_lt_iff₀ hηLpos]
    linarith
  rw [← hsplit]
  have hA0 : 0 ≤ ∑ t ∈ Finset.univ.filter (fun t => condSpread α F G t < v / 2),
      finiteBayesMass α (finiteDecisionLaw F G) t := Finset.sum_nonneg fun t _ => hm0 t
  nlinarith [hA, hA1, hB, hNeg, hgap', hA0, hv]

/-- **The quadratic-gap modulus of a continuous strictly convex potential**:
for every `v > 0` there is `η > 0` such that any exact garbling on any finite
alphabets that loses less than `η` of the potential moves the posterior by
less than `v` in expected squared distance. -/
theorem exists_quadGap_modulus (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ) (α : Θ → ℝ) (hα : IsDist α) (v : ℝ)
    (hv : 0 < v) :
    ∃ η : ℝ, 0 < η ∧ ∀ {S T : Type u} [Fintype S] [Fintype T] (F : FiniteExperiment Θ S),
      IsFiniteExperiment F → ∀ (G : S → T → ℝ), G ∈ stochasticRules S T →
        finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw F G) < η →
          finiteBayesPotential posteriorQuadraticPotential α F -
            finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G) < v := by
  obtain ⟨ηm, hηm, hmid⟩ := exists_midGap_pos Φ hΦc hΦ (v / 4) (by positivity)
  refine ⟨v * (ηm * (v / 2) / 4) / 4, by positivity, ?_⟩
  intro S T _ _ F hF G hG hgap
  exact quadGap_lt_of_potentialGap_lt_aux Φ hΦ.convexOn α hα F hF G hG hv hηm hmid hgap

end Garbling

end IdExp
