import Formal.ScoreProcessMonotonicity
import Formal.PolicySimplexRowFamily
import Formal.WeightedObjectives

/-!
# A bounded strictly finitary objective

`thm:strict-finitary-objective`.  For a policy `π` and a finite target
experiment `T` on a record alphabet, the eventual loss
`ℓ_T(π) = inf_t δ(K_{π,t}, T)` is the limit of the nonincreasing sequence of
prefix deficiencies (prefix marginalization is an exact garbling).  If a
countable family `T_{n,k}` of depth-`n` record experiments is dense among all
depth-`n` policy records in uniform row TV, then

`π ⪰_fin σ  ⟺  ℓ_{n,k}(π) ≤ ℓ_{n,k}(σ) for all n, k`,

by the triangle inequality one way and the target perturbation bound the
other.  Such a family exists for every nonempty world class and response
class, because the compact polytope of horizon-`n` policy tables is separable
and the record map is Lipschitz in the table. Consequently, for strictly
positive summable weights `w` normalized by `sum' w = 1`, the objective
`J_w(π) = 1 − Σ w_{n,k} ℓ_{n,k}(π)` is `[0,1]`-valued, monotone for the
finitary order, and strictly rewards every
strict finitary improvement — with no prior, no finite class, no attainable
top, and no learner. Normalization supplies the stated unit-interval bound;
strict monotonicity itself only requires positive summable weights.
`StrictFinitaryRegularity` supplies continuous finite-time
approximants and lower semicontinuity in the policy product topology.
-/

namespace IdExp

open Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O] [Nonempty Θ]

/-! ## Prefix deficiencies are nonincreasing -/

theorem finiteDeficiency_eq_zero_of_blackwellLE' {X Y : Type*} [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) (h : FiniteBlackwellLE F E) :
    finiteDeficiency E F = 0 := by
  obtain ⟨G, hG, hGF⟩ := h
  haveI := nonempty_of_isFiniteExperiment F hF
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder E F G hG 0
    intro θ
    change finiteTV (finiteDecisionLaw E G θ) (F θ) ≤ 0
    rw [hGF]
    simp [finiteTV]
  · exact finiteDeficiency_nonneg_of_valid E F hE hF

/-- Deficiency of a policy's records to a fixed target is nonincreasing in the
horizon: the later record garbles exactly to the earlier one. -/
theorem deficiency_record_antitone {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) :
    Antitone fun t => finiteDeficiency (causalFiniteExperiment π.1 Qs t) F := by
  intro s t hst
  have h0 := finiteDeficiency_eq_zero_of_blackwellLE' (causalFiniteExperiment π.1 Qs t)
    (causalFiniteExperiment π.1 Qs s) (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ s)
    (causalFiniteExperiment_prefix_blackwell_of_le π.1 π.2 Qs hQ hst)
  have htri := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs t)
    (causalFiniteExperiment π.1 Qs s) F (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ s) hF
  show finiteDeficiency (causalFiniteExperiment π.1 Qs t) F ≤
    finiteDeficiency (causalFiniteExperiment π.1 Qs s) F
  linarith

/-! ## Eventual losses -/

/-- `ℓ_T(π) = inf_t δ(K_{π,t}, T)`. -/
def eventualLoss {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (π : ValidCausalPolicy A O) (F : FiniteExperiment Θ Y) : ℝ :=
  ⨅ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 Qs t) F

theorem eventualLoss_bddBelow {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) :
    BddBelow (Set.range fun t => finiteDeficiency (causalFiniteExperiment π.1 Qs t) F) := by
  haveI := nonempty_of_isFiniteExperiment F hF
  refine ⟨0, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact finiteDeficiency_nonneg_of_valid _ _ (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) hF

theorem eventualLoss_le {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) (t : ℕ) :
    eventualLoss Qs π F ≤ finiteDeficiency (causalFiniteExperiment π.1 Qs t) F :=
  ciInf_le (eventualLoss_bddBelow Qs hQ π F hF) t

theorem le_eventualLoss {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (π : ValidCausalPolicy A O) (F : FiniteExperiment Θ Y) (c : ℝ)
    (h : ∀ t, c ≤ finiteDeficiency (causalFiniteExperiment π.1 Qs t) F) :
    c ≤ eventualLoss Qs π F :=
  le_ciInf h

theorem eventualLoss_nonneg {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) : 0 ≤ eventualLoss Qs π F := by
  haveI := nonempty_of_isFiniteExperiment F hF
  exact le_eventualLoss Qs π F 0 fun t =>
    finiteDeficiency_nonneg_of_valid _ _ (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) hF

theorem eventualLoss_le_one {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) : eventualLoss Qs π F ≤ 1 := by
  haveI := nonempty_of_isFiniteExperiment F hF
  exact (eventualLoss_le Qs hQ π F hF 0).trans
    (finiteDeficiency_le_one_of_valid _ _ (causalFiniteExperiment_valid π.1 π.2 Qs hQ 0) hF)

/-- The eventual loss is the limit of the prefix deficiencies. -/
theorem tendsto_eventualLoss {Y : Type*} [Fintype Y] (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) :
    Tendsto (fun t => finiteDeficiency (causalFiniteExperiment π.1 Qs t) F) atTop
      (𝓝 (eventualLoss Qs π F)) :=
  tendsto_atTop_ciInf (deficiency_record_antitone Qs hQ π F hF)
    (eventualLoss_bddBelow Qs hQ π F hF)

/-! ## Dense record families recover the finitary order -/

/-- A countable family of depth-`n` record experiments, dense among all
depth-`n` policy records in uniform row TV. -/
def DenseRecordFamily (Qs : Θ → CausalResponse A O)
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n)) : Prop :=
  (∀ n k, IsFiniteExperiment (T n k)) ∧
  ∀ (σ : ValidCausalPolicy A O) (n : ℕ) (η : ℝ), 0 < η →
    ∃ k, ∀ θ, finiteTV (T n k θ) (causalFiniteExperiment σ.1 Qs n θ) ≤ η

/-- **The finitary order is recovered by the eventual losses** against any
dense record family. -/
theorem causalFinitaryDominates_iff_eventualLoss (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n))
    (hT : DenseRecordFamily Qs T) (π σ : ValidCausalPolicy A O) :
    CausalFinitaryDominates Qs π σ ↔
      ∀ n k, eventualLoss Qs π (T n k) ≤ eventualLoss Qs σ (T n k) := by
  constructor
  · intro hdom n k
    apply le_eventualLoss
    intro s
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨t₀, ht₀⟩ := hdom s ε hε
    have h1 := eventualLoss_le Qs hQ π (T n k) (hT.1 n k) t₀
    have htri := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs t₀)
      (causalFiniteExperiment σ.1 Qs s) (T n k) (causalFiniteExperiment_valid π.1 π.2 Qs hQ t₀)
      (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ s) (hT.1 n k)
    have h2 := ht₀ t₀ le_rfl
    linarith
  · intro hl n ε hε
    obtain ⟨k, hk⟩ := hT.2 σ n (ε / 4) (by positivity)
    have hσ : eventualLoss Qs σ (T n k) ≤ ε / 4 :=
      (eventualLoss_le Qs hQ σ (T n k) (hT.1 n k) n).trans
        (finiteDeficiency_le_of_rowTV _ _ (ε / 4) fun θ => by
          rw [finiteTV_symm]; exact hk θ)
    have hπ : eventualLoss Qs π (T n k) ≤ ε / 4 := (hl n k).trans hσ
    have hlt : eventualLoss Qs π (T n k) < eventualLoss Qs π (T n k) + ε / 4 := by linarith
    obtain ⟨t₀, ht₀⟩ := exists_lt_of_ciInf_lt hlt
    refine ⟨t₀, fun t ht => ?_⟩
    have hanti := deficiency_record_antitone Qs hQ π (causalFiniteExperiment σ.1 Qs n)
      (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ n) ht
    have hpert := abs_finiteDeficiency_sub_le_of_rowTV_target
      (causalFiniteExperiment π.1 Qs t₀) (T n k) (causalFiniteExperiment σ.1 Qs n)
      (causalFiniteExperiment_valid π.1 π.2 Qs hQ t₀) (hT.1 n k)
      (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ n) (ε / 4) hk
    have h3 := (abs_le.1 hpert).1
    show finiteDeficiency (causalFiniteExperiment π.1 Qs t) (causalFiniteExperiment σ.1 Qs n) < ε
    linarith

/-! ## Existence of a dense record family -/

/-- **Every nonempty class has a countable dense record family**, from
separability of the compact table polytope and the Lipschitz record map. -/
theorem exists_densePolicyRecordFamily (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    ∃ ρ : ℕ → ℕ → ValidCausalPolicy A O,
      DenseRecordFamily Qs (fun n k => causalFiniteExperiment (ρ n k).1 Qs n) := by
  classical
  have hsep : ∀ n : ℕ, ∃ f : ℕ → SilentHorizonPolicyRows A O n, Dense (Set.range f) := by
    intro n
    haveI : Nonempty (SilentHorizonPolicyRows A O n) :=
      ⟨silentHorizonRowsOfPolicy n defaultValidCausalPolicy⟩
    obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (SilentHorizonPolicyRows A O n)
    obtain ⟨f, hf⟩ := hsc.exists_eq_range hsd.nonempty
    exact ⟨f, hf ▸ hsd⟩
  choose f hf using hsep
  refine ⟨fun n k => silentHorizonPolicyOfRows n (f n k),
    fun n k => policyRowExperiment_valid Qs hQ n (f n k), ?_⟩
  intro σ n η hη
  set x : SilentHorizonPolicyRows A O n := silentHorizonRowsOfPolicy n σ with hxdef
  have hx : policyRowExperiment Qs n x = causalFiniteExperiment σ.1 Qs n := by
    exact policyRowExperiment_rowsOfPolicy Qs n σ
  set C : ℝ := (n : ℝ) * ((Fintype.card A : ℝ) / 2) with hC
  have hC0 : 0 ≤ C := by positivity
  have hr : 0 < η / (C + 1) := by positivity
  obtain ⟨y, hyb, k, rfl⟩ := Metric.dense_iff.1 (hf n) x _ hr
  refine ⟨k, fun θ => ?_⟩
  rw [← hx]
  have hd : dist (f n k) x < η / (C + 1) := hyb
  have h := finiteTV_silentHorizonPolicyOfRows_experiment_le Qs hQ n (f n k) x θ
  have hCd : C * dist (f n k) x ≤ C * (η / (C + 1)) := mul_le_mul_of_nonneg_left hd.le hC0
  have hfrac : C * (η / (C + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < C + 1)]
    nlinarith
  calc finiteTV (policyRowExperiment Qs n (f n k) θ) (policyRowExperiment Qs n x θ)
      ≤ (n : ℝ) * (((Fintype.card A : ℝ) / 2) * dist (f n k) x) := h
    _ = C * dist (f n k) x := by rw [hC]; ring
    _ ≤ η := hCd.trans hfrac

/-- The native-policy construction also supplies an abstract dense record family. -/
theorem exists_denseRecordFamily (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    ∃ T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n), DenseRecordFamily Qs T := by
  obtain ⟨ρ, hρ⟩ := exists_densePolicyRecordFamily Qs hQ
  exact ⟨fun n k => causalFiniteExperiment (ρ n k).1 Qs n, hρ⟩

/-! ## The weighted objective -/

/-- `J_w(π) = 1 − Σ_{n,k} w(n,k) ℓ_{n,k}(π)`. -/
def weightedFinitaryObjective (Qs : Θ → CausalResponse A O)
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n)) (w : ℕ × ℕ → ℝ)
    (π : ValidCausalPolicy A O) : ℝ :=
  1 - ∑' p : ℕ × ℕ, w p * eventualLoss Qs π (T p.1 p.2)

theorem summable_weightedLoss (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n))
    (hT : ∀ n k, IsFiniteExperiment (T n k)) (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw : Summable w) (π : ValidCausalPolicy A O) :
    Summable fun p : ℕ × ℕ => w p * eventualLoss Qs π (T p.1 p.2) := summable_weightedScore_loss hw0 hw
    (fun p π => ⟨eventualLoss_nonneg Qs hQ π _ (hT p.1 p.2),
      eventualLoss_le_one Qs hQ π _ (hT p.1 p.2)⟩) π

theorem weightedFinitaryObjective_mem_unitInterval (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n))
    (hT : ∀ n k, IsFiniteExperiment (T n k)) (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw : Summable w) (hw1 : ∑' p, w p = 1) (π : ValidCausalPolicy A O) :
    weightedFinitaryObjective Qs T w π ∈ Set.Icc (0 : ℝ) 1 := weightedScore_mem_Icc hw0 hw hw1
    (fun p π => ⟨eventualLoss_nonneg Qs hQ π _ (hT p.1 p.2),
      eventualLoss_le_one Qs hQ π _ (hT p.1 p.2)⟩) π

/-- **Monotone for the finitary order.** -/
theorem weightedFinitaryObjective_mono (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n))
    (hT : DenseRecordFamily Qs T) (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ) :
    weightedFinitaryObjective Qs T w σ ≤ weightedFinitaryObjective Qs T w π := by
  exact weightedScore_le_of_loss_le hw0 hw
    (fun p π => ⟨eventualLoss_nonneg Qs hQ π _ (hT.1 p.1 p.2),
      eventualLoss_le_one Qs hQ π _ (hT.1 p.1 p.2)⟩)
    (fun p => (causalFinitaryDominates_iff_eventualLoss Qs hQ T hT π σ).1 hdom p.1 p.2)

/-- **Strictly finitarily monotone**: every strict finitary improvement is
strictly rewarded. -/
theorem weightedFinitaryObjective_strict (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n))
    (hT : DenseRecordFamily Qs T) (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 < w p) (hw : Summable w)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ)
    (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    weightedFinitaryObjective Qs T w σ < weightedFinitaryObjective Qs T w π := by
  apply weightedScore_lt_of_representation (R := CausalFinitaryDominates Qs) hw0 hw
    (fun p π => ⟨eventualLoss_nonneg Qs hQ π _ (hT.1 p.1 p.2),
      eventualLoss_le_one Qs hQ π _ (hT.1 p.1 p.2)⟩) ?_ hdom hnot
  intro π σ
  simpa only [Prod.forall] using causalFinitaryDominates_iff_eventualLoss Qs hQ T hT π σ

/-- **`thm:strict-finitary-objective`.**  For any nonempty class and positive
summable weights summing to one, there is a countable family of finite native
record experiments whose eventual losses recover the finitary order, and the
weighted objective `1 − Σ w ℓ` is `[0,1]`-valued, finitarily monotone, and
strictly finitarily monotone. -/
theorem exists_strictly_finitary_objective (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 < w p)
    (hw : Summable w) (hw1 : ∑' p, w p = 1) :
    ∃ T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n),
      (∀ n k, IsFiniteExperiment (T n k)) ∧
      (∀ π σ : ValidCausalPolicy A O, CausalFinitaryDominates Qs π σ ↔
        ∀ n k, eventualLoss Qs π (T n k) ≤ eventualLoss Qs σ (T n k)) ∧
      (∀ π, weightedFinitaryObjective Qs T w π ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ π σ, CausalFinitaryDominates Qs π σ →
        weightedFinitaryObjective Qs T w σ ≤ weightedFinitaryObjective Qs T w π) ∧
      (∀ π σ, CausalFinitaryDominates Qs π σ → ¬ CausalFinitaryDominates Qs σ π →
        weightedFinitaryObjective Qs T w σ < weightedFinitaryObjective Qs T w π) := by
  obtain ⟨T, hT⟩ := exists_denseRecordFamily Qs hQ
  refine ⟨T, hT.1, fun π σ => causalFinitaryDominates_iff_eventualLoss Qs hQ T hT π σ,
    fun π => weightedFinitaryObjective_mem_unitInterval Qs hQ T hT.1 w (fun p => (hw0 p).le) hw hw1 π,
    fun π σ hdom => weightedFinitaryObjective_mono Qs hQ T hT w (fun p => (hw0 p).le) hw hdom,
    fun π σ hdom hnot => weightedFinitaryObjective_strict Qs hQ T hT w hw0 hw hdom hnot⟩

end

end IdExp
