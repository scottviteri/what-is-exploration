import Formal.CausalProfile

/-!
# Approach schemes: what replaces one policy in the approach case

`CausalProfile.lean` defines the completed attainable set
`causalProfileClosure` as the product-topology closure of the raw profiles
`causalPolicyProfile` of valid causal policies, and the frontier
`causalParetoFrontier` as its Pareto-minimal points.  A frontier point need
not be attained by any single policy (the paper's wait-then-switch example).
This module answers, at the definitional level, what object replaces the
single policy in that case and when it collapses back to one policy.

* **The object.**  An *approach scheme* for a profile `p` is a sequence of
  valid causal policies whose profiles converge to `p` in the product
  topology (`IsApproachScheme`).  Because the profile cube `ℕ → [0,1]` is
  metrizable, closure is sequential closure, so `p` lies in the completed
  attainable set **iff** some approach scheme converges to it
  (`mem_causalProfileClosure_iff_exists_approachScheme`).  Equivalently a
  scheme is a tolerance-indexed family: for every finite coordinate set `J`
  and every `ε > 0` the scheme is eventually within `ε` of `p` on `J`
  (`approachScheme_eventually_close`; converse
  `isApproachScheme_of_eventually_close`), and each member of a scheme can
  be read off at a finite horizon
  (`exists_policy_horizon_testDeficiency_lt_add`).

* **Finite-horizon members suffice.**  The horizon-`t` experiment depends
  only on the policy's rows at histories shorter than `t`
  (`causalFiniteExperiment_congr_of_agree`), so truncating a policy to
  horizon `t` (`truncateCausalPolicy`, a valid policy following the fixed
  default row afterwards) leaves that experiment unchanged
  (`causalFiniteExperiment_truncate`).  Hence every point of the completed
  attainable set is one-sidedly `ε`-approximated, on any finite coordinate
  set, by a valid policy of some finite horizon
  (`exists_finiteHorizon_policy_testDeficiency_lt_add`), and every frontier
  point is the limit of an approach scheme all of whose members are
  finite-horizon policies (`exists_finiteHorizon_approachScheme_of_pareto`).
  The approximation is one-sided at general points of the closure; it is
  two-sided at frontier points by the next item.

* **One-sided approach of a frontier point is two-sided.**  If `m` is
  Pareto-minimal in a closed subset of the cube and a sequence of the set
  satisfies `x_k ≤ m + ε_k` coordinatewise with `ε_k → 0`, then `x_k → m`
  (`tendsto_of_forall_le_add_of_pareto`; compactness plus closedness of the
  coordinatewise order).  Consequently a one-sided synthesis guarantee at
  finite horizons — `Def(K_{π_k,t_k}, T_j) ≤ p_j + ε_k` — already produces a
  genuine approach scheme for any frontier point `p`
  (`isApproachScheme_of_testDeficiency_le_add_of_pareto`).

* **Collapse under sequential dominance.**  If one policy `π⋆` has, for
  every member `π_k`, a horizon `s_k` at which its collected experiment
  simulates the member's horizon-`t_k` experiment exactly, then every
  profile coordinate of `π⋆` is at most the member's horizon-`t_k`
  deficiency (`causalPolicyProfileValue_le_of_dominates`, by the triangle
  inequality).  If those member deficiencies converge to `p` then
  `p(π⋆) ≤ p`, and if `p` is a frontier point then `p(π⋆) = p`: the scheme
  collapses to the single policy `π⋆` and the frontier point is attained
  (`causalPolicyProfile_eq_of_dominates_of_pareto`).  This isolates the
  causal hypothesis a renewal structure (reset word, episodic interface)
  has to supply.

Nothing here assumes compactness or closedness of the raw policy space.
-/

namespace IdExp

open Filter Set Topology

set_option linter.unusedSectionVars false

/-! ### Cube-level lemmas -/

/-- Coordinatewise up-sets of the profile cube are closed. -/
theorem isClosed_Ici_profile (q : ProfileCube) : IsClosed (Ici q) := by
  have h : Ici q = ⋂ j, {p : ProfileCube | ((q j : ℝ)) ≤ ((p j : ℝ))} := by
    ext p
    simp only [mem_Ici, Set.mem_iInter, Set.mem_ofPred_eq, Pi.le_def]
    exact forall_congr' fun j => Iff.symm Subtype.coe_le_coe
  rw [h]
  exact isClosed_iInter fun j =>
    isClosed_le continuous_const (continuous_subtype_val.comp (continuous_apply j))

/-- A lower bound of every term of a convergent sequence is a lower bound of
its limit. -/
theorem le_of_forall_le_of_tendsto {x : ℕ → ProfileCube} {p y : ProfileCube}
    (hx : Tendsto x atTop (𝓝 p)) (h : ∀ i, y ≤ x i) : y ≤ p :=
  (isClosed_Ici_profile y).mem_of_tendsto hx (Eventually.of_forall h)

/-- Any point of a set below a Pareto-minimal point of that set equals it. -/
theorem eq_of_le_of_pareto {S : Set ProfileCube} {m y : ProfileCube}
    (hmin : ∀ q ∈ S, q ≤ m → m ≤ q) (hy : y ∈ S) (hym : y ≤ m) : y = m :=
  le_antisymm hym (hmin y hy hym)

/-! ### One-sided approach of a Pareto-minimal point is two-sided -/

/-- If a sequence in a closed set `S` is, coordinate by coordinate, eventually
below `m + ε_k` with `ε_k → 0`, and `m` is Pareto-minimal in `S`, then the
sequence converges to `m`.  (Membership `m ∈ S` is not needed: every
subsequential limit lies in `S` below `m`, and minimality forces it to equal
`m`.) -/
theorem tendsto_of_eventually_le_add_of_pareto {S : Set ProfileCube} (hS : IsClosed S)
    {m : ProfileCube} (hmin : ∀ q ∈ S, q ≤ m → m ≤ q)
    {x : ℕ → ProfileCube} (hxS : ∀ k, x k ∈ S)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hle : ∀ j, ∀ᶠ k in atTop, ((x k j : ℝ)) ≤ (m j : ℝ) + ε k) :
    Tendsto x atTop (𝓝 m) := by
  -- every subsequence has a further subsequence converging in `S` below `m`, hence to `m`
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨y, hyS, φ, hφ, hlim⟩ :=
    (hS.isCompact).tendsto_subseq (fun k => hxS (ns k))
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hym : y ≤ m := by
    intro j
    have hcoord : Tendsto (fun k => ((x (ns (φ k)) j : ℝ))) atTop (𝓝 ((y j : ℝ))) :=
      tendsto_subtype_rng.mp ((tendsto_pi_nhds.mp hlim) j)
    have hεsub : Tendsto (fun k => ε (ns (φ k))) atTop (𝓝 0) := hε.comp hsub
    have hbound : Tendsto (fun k => (m j : ℝ) + ε (ns (φ k))) atTop (𝓝 ((m j : ℝ) + 0)) :=
      tendsto_const_nhds.add hεsub
    rw [add_zero] at hbound
    have : ((y j : ℝ)) ≤ (m j : ℝ) :=
      le_of_tendsto_of_tendsto hcoord hbound (hsub.eventually (hle j))
    exact Subtype.coe_le_coe.mp this
  have : y = m := eq_of_le_of_pareto hmin hyS hym
  rw [this] at hlim
  exact hlim

/-- **One-sided approach of a Pareto-minimal point is two-sided.**  If a
sequence in a closed set `S` is coordinatewise below `m + ε_k` with
`ε_k → 0`, and `m` is Pareto-minimal in `S`, then the sequence converges to
`m`. -/
theorem tendsto_of_forall_le_add_of_pareto {S : Set ProfileCube} (hS : IsClosed S)
    {m : ProfileCube} (hmin : ∀ q ∈ S, q ≤ m → m ≤ q)
    {x : ℕ → ProfileCube} (hxS : ∀ k, x k ∈ S)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hle : ∀ k j, ((x k j : ℝ)) ≤ (m j : ℝ) + ε k) :
    Tendsto x atTop (𝓝 m) :=
  tendsto_of_eventually_le_add_of_pareto hS hmin hxS hε
    (fun j => Eventually.of_forall fun k => hle k j)

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O] [Nonempty Θ]

/-! ### Approach schemes and the completed attainable set -/

/-- An approach scheme for a profile `p`: a sequence of valid causal policies
whose profiles converge to `p` in the product topology (coordinatewise). -/
def IsApproachScheme (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ℕ → ValidCausalPolicy A O) (p : ProfileCube) : Prop :=
  Tendsto (fun k => causalPolicyProfile Qs hQ e (π k)) atTop (𝓝 p)

/-- **The object replacing one policy.**  A profile lies in the completed
attainable set exactly when some approach scheme converges to it.  The cube
is metrizable, so closure is sequential closure. -/
theorem mem_causalProfileClosure_iff_exists_approachScheme
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (p : ProfileCube) :
    p ∈ causalProfileClosure Qs hQ e ↔
      ∃ π : ℕ → ValidCausalPolicy A O, IsApproachScheme Qs hQ e π p := by
  unfold causalProfileClosure causalPolicyProfiles
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨x, hx, hlim⟩
    choose π hπ using hx
    refine ⟨π, ?_⟩
    unfold IsApproachScheme
    have : (fun k => causalPolicyProfile Qs hQ e (π k)) = x := funext hπ
    rw [this]; exact hlim
  · rintro ⟨π, hπ⟩
    exact ⟨fun k => causalPolicyProfile Qs hQ e (π k), fun k => ⟨π k, rfl⟩, hπ⟩

/-- A single policy is a constant approach scheme for its own profile. -/
theorem isApproachScheme_const
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ValidCausalPolicy A O) :
    IsApproachScheme Qs hQ e (fun _ => π) (causalPolicyProfile Qs hQ e π) :=
  tendsto_const_nhds

/-- **Finite-coordinate tolerance reading.**  An approach scheme for `p` is,
for every finite coordinate set `J` and every `ε > 0`, eventually within `ε`
of `p` on every coordinate of `J`. -/
theorem approachScheme_eventually_close
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ℕ → ValidCausalPolicy A O) (p : ProfileCube)
    (h : IsApproachScheme Qs hQ e π p) (J : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j ∈ J,
      |causalPolicyProfileValue (π k) Qs e j - ((p j : Set.Icc (0:ℝ) 1) : ℝ)| < ε := by
  rw [Filter.eventually_all_finset]
  intro j _
  have hj : Tendsto (fun k => ((causalPolicyProfile Qs hQ e (π k) j : Set.Icc (0:ℝ) 1) : ℝ)) atTop
      (𝓝 ((p j : Set.Icc (0:ℝ) 1) : ℝ)) := by
    have := (tendsto_pi_nhds.mp h) j
    exact tendsto_subtype_rng.mp this
  have := (Metric.tendsto_nhds.mp hj) ε hε
  simpa [Real.dist_eq, causalPolicyProfile_coe] using this

/-- Converse tolerance reading: coordinatewise `ε`-closeness on every finite
set, eventually, is exactly convergence of the scheme. -/
theorem isApproachScheme_of_eventually_close
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ℕ → ValidCausalPolicy A O) (p : ProfileCube)
    (h : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      |causalPolicyProfileValue (π k) Qs e j - ((p j : Set.Icc (0:ℝ) 1) : ℝ)| < ε) :
    IsApproachScheme Qs hQ e π p := by
  unfold IsApproachScheme
  rw [tendsto_pi_nhds]
  intro j
  refine tendsto_subtype_rng.mpr ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  simpa [Real.dist_eq, causalPolicyProfile_coe] using h j ε hε

/-! ### Scheme members at finite horizons -/

/-- Each profile coordinate is bounded by every finite-horizon deficiency. -/
theorem causalPolicyProfileValue_le_testDeficiency
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ValidCausalPolicy A O) (j t : ℕ) :
    causalPolicyProfileValue π Qs e j ≤ causalPolicyTestDeficiency π Qs (e j) t := by
  have hbdd : BddBelow (Set.range (causalPolicyTestDeficiency π Qs (e j))) := by
    refine ⟨0, ?_⟩
    rintro d ⟨u, rfl⟩
    exact finiteDeficiency_nonneg_of_valid _ _
      (causalFiniteExperiment_valid π.1 π.2 Qs hQ u)
      (causalNativeTestExperiment_valid Qs hQ (e j))
  exact csInf_le hbdd ⟨t, rfl⟩

/-- For a policy and a finite coordinate set, one horizon brings every listed
finite-horizon deficiency within `ε` above the limiting coordinate. -/
theorem exists_horizon_testDeficiency_lt_add
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ValidCausalPolicy A O)
    (J : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, ∀ j ∈ J,
      causalPolicyTestDeficiency π Qs (e j) t < causalPolicyProfileValue π Qs e j + ε := by
  have h : ∀ᶠ t in atTop, ∀ j ∈ J,
      causalPolicyTestDeficiency π Qs (e j) t < causalPolicyProfileValue π Qs e j + ε := by
    rw [Filter.eventually_all_finset]
    intro j _
    exact (causalPolicyProfileValue_tendsto π Qs hQ e j).eventually
      (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  exact h.exists

/-- **Finite-horizon members.**  Every point of the completed attainable set
is, on any finite coordinate set and to any tolerance, one-sidedly
`ε`-approximated by the finite-horizon experiment of a single valid policy:
`Def(K_{π,t}, T_j) < p_j + ε` for all `j ∈ J`.  This is the ingredient the
paper's enumeration argument needs; it does not yet truncate `π` to horizon
`t`. -/
theorem exists_policy_horizon_testDeficiency_lt_add
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) {p : ProfileCube}
    (hp : p ∈ causalProfileClosure Qs hQ e) (J : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (π : ValidCausalPolicy A O) (t : ℕ), ∀ j ∈ J,
      causalPolicyTestDeficiency π Qs (e j) t < ((p j : Set.Icc (0:ℝ) 1) : ℝ) + ε := by
  obtain ⟨π, hπ⟩ := (mem_causalProfileClosure_iff_exists_approachScheme Qs hQ e p).mp hp
  obtain ⟨k, hk⟩ :=
    (approachScheme_eventually_close Qs hQ e π p hπ J (ε / 2) (by positivity)).exists
  obtain ⟨t, ht⟩ := exists_horizon_testDeficiency_lt_add Qs hQ e (π k) J (ε / 2) (by positivity)
  refine ⟨π k, t, fun j hj => ?_⟩
  have h1 := ht j hj
  have h2 := (abs_lt.mp (hk j hj)).2
  linarith

/-! ### One-sided finite-horizon guarantees suffice at a frontier point -/

/-- If one-sided finite-horizon bounds `Def(K_{π_k,t_k}, T_j) ≤ p_j + ε_k`
hold for a frontier point `p` with `ε_k → 0`, the policies form a genuine
(two-sided) approach scheme for `p`.  This is why an enumeration that only
certifies upper bounds already synthesises the approach. -/
theorem isApproachScheme_of_testDeficiency_le_add_of_pareto
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    {p : ProfileCube} (hp : p ∈ causalParetoFrontier Qs hQ e)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hle : ∀ k j, causalPolicyTestDeficiency (π k) Qs (e j) (t k) ≤
      ((p j : Set.Icc (0:ℝ) 1) : ℝ) + ε k) :
    IsApproachScheme Qs hQ e π p := by
  refine tendsto_of_forall_le_add_of_pareto (causalProfileClosure_isClosed Qs hQ e) hp.2
    (fun k => subset_closure ⟨π k, rfl⟩) hε (fun k j => ?_)
  rw [causalPolicyProfile_coe]
  exact (causalPolicyProfileValue_le_testDeficiency Qs hQ e (π k) j (t k)).trans (hle k j)

/-- The same statement with the bound on limiting profile coordinates. -/
theorem isApproachScheme_of_profile_le_add_of_pareto
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ℕ → ValidCausalPolicy A O)
    {p : ProfileCube} (hp : p ∈ causalParetoFrontier Qs hQ e)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hle : ∀ k j, causalPolicyProfileValue (π k) Qs e j ≤
      ((p j : Set.Icc (0:ℝ) 1) : ℝ) + ε k) :
    IsApproachScheme Qs hQ e π p :=
  tendsto_of_forall_le_add_of_pareto (causalProfileClosure_isClosed Qs hQ e) hp.2
    (fun k => subset_closure ⟨π k, rfl⟩) hε (fun k j => by
      rw [causalPolicyProfile_coe]; exact hle k j)

/-! ### Finite-horizon scheme members (truncation) -/

/-- Two policies agreeing on every history shorter than `n` assign the same
probability to every continuation that stays within length `n`. -/
theorem causalTraceProbFrom_congr_of_agree (π π' : CausalPolicy A O) (Q : CausalResponse A O)
    (n : ℕ) (hagree : ∀ h : CausalHistory A O, h.length < n → π h = π' h)
    (rest : CausalHistory A O) :
    ∀ pre : CausalHistory A O, pre.length + rest.length ≤ n →
      causalTraceProbFrom π Q pre rest = causalTraceProbFrom π' Q pre rest := by
  induction rest with
  | nil => intro pre _; rfl
  | cons ao rest ih =>
    intro pre hlen
    simp only [List.length_cons] at hlen
    simp only [causalTraceProbFrom]
    have hlen' : (pre ++ [ao]).length + rest.length ≤ n := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [hagree pre (by omega), ih (pre ++ [ao]) hlen']

/-- The horizon-`n` experiment depends only on the policy's rows at histories
shorter than `n`. -/
theorem causalFiniteExperiment_congr_of_agree (π π' : CausalPolicy A O)
    (Qs : Θ → CausalResponse A O) (n : ℕ)
    (hagree : ∀ h : CausalHistory A O, h.length < n → π h = π' h) :
    causalFiniteExperiment π Qs n = causalFiniteExperiment π' Qs n := by
  funext θ w
  unfold causalFiniteExperiment causalTraceProb
  exact causalTraceProbFrom_congr_of_agree π π' (Qs θ) n hagree (List.ofFn w) []
    (by simp)

/-- A policy is of horizon `t` when it follows the fixed default row on every
history of length at least `t`. -/
def IsFiniteHorizonPolicy (π : ValidCausalPolicy A O) (t : ℕ) : Prop :=
  ∀ h : CausalHistory A O, t ≤ h.length → π.1 h = defaultValidCausalPolicy.1 h

/-- Horizon-`t` truncation of a valid policy: follow `π` on histories shorter
than `t`, then the fixed default row. -/
noncomputable def truncateCausalPolicy (π : ValidCausalPolicy A O) (t : ℕ) :
    ValidCausalPolicy A O :=
  ⟨fun h => if h.length < t then π.1 h else defaultValidCausalPolicy.1 h, by
    intro h
    dsimp only
    split_ifs
    · exact π.2 h
    · exact defaultValidCausalPolicy.2 h⟩

theorem truncateCausalPolicy_isFiniteHorizon (π : ValidCausalPolicy A O) (t : ℕ) :
    IsFiniteHorizonPolicy (truncateCausalPolicy π t) t := by
  intro h ht
  simp [truncateCausalPolicy, not_lt.mpr ht]

/-- The truncation collects exactly the same horizon-`t` experiment. -/
theorem causalFiniteExperiment_truncate (π : ValidCausalPolicy A O)
    (Qs : Θ → CausalResponse A O) (t : ℕ) :
    causalFiniteExperiment (truncateCausalPolicy π t).1 Qs t =
      causalFiniteExperiment π.1 Qs t :=
  causalFiniteExperiment_congr_of_agree _ _ Qs t fun h hh => by
    simp [truncateCausalPolicy, hh]

theorem causalPolicyTestDeficiency_truncate (π : ValidCausalPolicy A O)
    (Qs : Θ → CausalResponse A O) (q : CausalNativeTest A O) (t : ℕ) :
    causalPolicyTestDeficiency (truncateCausalPolicy π t) Qs q t =
      causalPolicyTestDeficiency π Qs q t := by
  unfold causalPolicyTestDeficiency
  rw [causalFiniteExperiment_truncate]

/-- The truncation's limiting profile is bounded by the original policy's
horizon-`t` deficiencies. -/
theorem causalPolicyProfileValue_truncate_le
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) (π : ValidCausalPolicy A O) (t j : ℕ) :
    causalPolicyProfileValue (truncateCausalPolicy π t) Qs e j ≤
      causalPolicyTestDeficiency π Qs (e j) t := by
  rw [← causalPolicyTestDeficiency_truncate π Qs (e j) t]
  exact causalPolicyProfileValue_le_testDeficiency Qs hQ e _ j t

/-- **Finite-horizon randomized policies suffice for scheme members.**  Every
point of the completed attainable set is, on any finite coordinate set and to
any tolerance, one-sidedly `ε`-approximated at horizon `t` by a valid policy
of horizon `t`. -/
theorem exists_finiteHorizon_policy_testDeficiency_lt_add
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) {p : ProfileCube}
    (hp : p ∈ causalProfileClosure Qs hQ e) (J : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (t : ℕ) (π : ValidCausalPolicy A O), IsFiniteHorizonPolicy π t ∧ ∀ j ∈ J,
      causalPolicyTestDeficiency π Qs (e j) t < ((p j : Set.Icc (0:ℝ) 1) : ℝ) + ε := by
  obtain ⟨π, t, hπ⟩ := exists_policy_horizon_testDeficiency_lt_add Qs hQ e hp J ε hε
  refine ⟨t, truncateCausalPolicy π t, truncateCausalPolicy_isFiniteHorizon π t,
    fun j hj => ?_⟩
  rw [causalPolicyTestDeficiency_truncate]
  exact hπ j hj

/-- **Finite-horizon approach schemes for frontier points.**  Every frontier
point is the limit of an approach scheme whose `k`-th member is a policy of
some finite horizon `t k`, one-sidedly within `1/(k+1)` of `p` on the first
`k` coordinates at that horizon. -/
theorem exists_finiteHorizon_approachScheme_of_pareto
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O) {p : ProfileCube}
    (hp : p ∈ causalParetoFrontier Qs hQ e) :
    ∃ (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ),
      (∀ k, IsFiniteHorizonPolicy (π k) (t k)) ∧ IsApproachScheme Qs hQ e π p := by
  have hchoice : ∀ k : ℕ, ∃ (t : ℕ) (π : ValidCausalPolicy A O), IsFiniteHorizonPolicy π t ∧
      ∀ j ∈ Finset.range k, causalPolicyTestDeficiency π Qs (e j) t <
        ((p j : Set.Icc (0:ℝ) 1) : ℝ) + 1 / ((k : ℝ) + 1) := fun k =>
    exists_finiteHorizon_policy_testDeficiency_lt_add Qs hQ e hp.1 (Finset.range k)
      (1 / ((k : ℝ) + 1)) (by positivity)
  choose t π hfin hlt using hchoice
  refine ⟨π, t, hfin, ?_⟩
  refine tendsto_of_eventually_le_add_of_pareto (causalProfileClosure_isClosed Qs hQ e) hp.2
    (fun k => subset_closure ⟨π k, rfl⟩) tendsto_one_div_add_atTop_nhds_zero_nat (fun j => ?_)
  filter_upwards [eventually_gt_atTop j] with k hk
  rw [causalPolicyProfile_coe]
  exact (causalPolicyProfileValue_le_testDeficiency Qs hQ e (π k) j (t k)).trans
    (hlt k j (Finset.mem_range.mpr hk)).le

/-! ### Collapse under sequential dominance -/

/-- **Scheme collapse under sequential dominance, coordinate form.**  If one
policy `π⋆` has, for every scheme member `π k`, a horizon `s k` at which its
collected experiment simulates the member's horizon-`t k` experiment
exactly, then each profile coordinate of `π⋆` is at most the member's
horizon-`t k` deficiency to that test, for every `k`. -/
theorem causalPolicyProfileValue_le_of_dominates
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O)
    (πs : ValidCausalPolicy A O) (π : ℕ → ValidCausalPolicy A O) (s t : ℕ → ℕ)
    (hdom : ∀ k, finiteDeficiency (causalFiniteExperiment πs.1 Qs (s k))
      (causalFiniteExperiment (π k).1 Qs (t k)) = 0) (j k : ℕ) :
    causalPolicyProfileValue πs Qs e j ≤ causalPolicyTestDeficiency (π k) Qs (e j) (t k) := by
  calc
    causalPolicyProfileValue πs Qs e j ≤ causalPolicyTestDeficiency πs Qs (e j) (s k) :=
      causalPolicyProfileValue_le_testDeficiency Qs hQ e πs j (s k)
    _ ≤ finiteDeficiency (causalFiniteExperiment πs.1 Qs (s k))
          (causalFiniteExperiment (π k).1 Qs (t k)) +
        causalPolicyTestDeficiency (π k) Qs (e j) (t k) :=
      finiteDeficiency_triangle _ _ _
        (causalFiniteExperiment_valid πs.1 πs.2 Qs hQ (s k))
        (causalFiniteExperiment_valid (π k).1 (π k).2 Qs hQ (t k))
        (causalNativeTestExperiment_valid Qs hQ (e j))
    _ = causalPolicyTestDeficiency (π k) Qs (e j) (t k) := by rw [hdom k, zero_add]

/-- If the member deficiencies converge coordinatewise to a profile `p`, the
dominating policy's profile lies below `p`. -/
theorem causalPolicyProfile_le_of_dominates_of_tendsto
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O)
    (πs : ValidCausalPolicy A O) (π : ℕ → ValidCausalPolicy A O) (s t : ℕ → ℕ)
    (hdom : ∀ k, finiteDeficiency (causalFiniteExperiment πs.1 Qs (s k))
      (causalFiniteExperiment (π k).1 Qs (t k)) = 0)
    (p : ProfileCube)
    (hlim : ∀ j, Tendsto (fun k => causalPolicyTestDeficiency (π k) Qs (e j) (t k)) atTop
      (𝓝 ((p j : ℝ)))) :
    causalPolicyProfile Qs hQ e πs ≤ p := by
  intro j
  apply Subtype.coe_le_coe.mp
  change causalPolicyProfileValue πs Qs e j ≤ (p j : ℝ)
  exact ge_of_tendsto (hlim j)
    (Eventually.of_forall fun k => causalPolicyProfileValue_le_of_dominates Qs hQ e πs π s t hdom j k)

/-- **Collapse criterion.**  A policy sequentially dominating a scheme whose
member deficiencies converge to a frontier point `p` attains `p` exactly:
the scheme collapses to the single policy `π⋆`. -/
theorem causalPolicyProfile_eq_of_dominates_of_pareto
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O)
    (πs : ValidCausalPolicy A O) (π : ℕ → ValidCausalPolicy A O) (s t : ℕ → ℕ)
    (hdom : ∀ k, finiteDeficiency (causalFiniteExperiment πs.1 Qs (s k))
      (causalFiniteExperiment (π k).1 Qs (t k)) = 0)
    (p : ProfileCube) (hp : p ∈ causalParetoFrontier Qs hQ e)
    (hlim : ∀ j, Tendsto (fun k => causalPolicyTestDeficiency (π k) Qs (e j) (t k)) atTop
      (𝓝 ((p j : ℝ)))) :
    causalPolicyProfile Qs hQ e πs = p :=
  eq_of_le_of_pareto hp.2 (subset_closure ⟨πs, rfl⟩)
    (causalPolicyProfile_le_of_dominates_of_tendsto Qs hQ e πs π s t hdom p hlim)

/-- Collapse criterion in scheme form: if `π⋆` sequentially dominates an
approach scheme for a frontier point `p`, with the member horizons chosen so
that the member's horizon-`t k` deficiencies are within `ε k → 0` of its
limiting coordinates, then `π⋆` attains `p`. -/
theorem causalPolicyProfile_eq_of_dominates_approachScheme
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O)
    (πs : ValidCausalPolicy A O) (π : ℕ → ValidCausalPolicy A O) (s t : ℕ → ℕ)
    (hdom : ∀ k, finiteDeficiency (causalFiniteExperiment πs.1 Qs (s k))
      (causalFiniteExperiment (π k).1 Qs (t k)) = 0)
    {p : ProfileCube} (hp : p ∈ causalParetoFrontier Qs hQ e)
    (hπ : IsApproachScheme Qs hQ e π p)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (ht : ∀ k j, causalPolicyTestDeficiency (π k) Qs (e j) (t k) ≤
      causalPolicyProfileValue (π k) Qs e j + ε k) :
    causalPolicyProfile Qs hQ e πs = p := by
  refine eq_of_le_of_pareto hp.2 (subset_closure ⟨πs, rfl⟩) (fun j => ?_)
  apply Subtype.coe_le_coe.mp
  change causalPolicyProfileValue πs Qs e j ≤ (p j : ℝ)
  have hlim : Tendsto (fun k => causalPolicyProfileValue (π k) Qs e j + ε k) atTop
      (𝓝 ((p j : ℝ) + 0)) := by
    refine Tendsto.add ?_ hε
    have := tendsto_subtype_rng.mp ((tendsto_pi_nhds.mp hπ) j)
    simpa [causalPolicyProfile_coe] using this
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun k =>
    (causalPolicyProfileValue_le_of_dominates Qs hQ e πs π s t hdom j k).trans (ht k j))

end IdExp
