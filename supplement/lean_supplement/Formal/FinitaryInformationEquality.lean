import Formal.PriorAverageInformation
import Formal.IndexedFiniteExperiment
import Formal.FinitaryObjectiveCore

/-!
# Finite total information detects prior-average finitary equivalence

The argument retains arbitrary measurable worlds and growing finite signal
alphabets. It uses actual information, actual decoder errors, and two ordered
finite-prefix limits; no terminal reconstruction or world identification is
assumed. Finite total information is expressed by bounded prefix information.
-/
namespace IdExp
open MeasureTheory Set Finset Filter Topology
noncomputable section
set_option linter.unusedSectionVars false

/-- Growing finite experiments, with validity and measurability retained. -/
structure MeasurableFiniteProcess (Θ P : Type*) [MeasurableSpace Θ]
    (S : ℕ → Type*) [∀ n, Fintype (S n)] where
  experiment : P → ∀ (n : ℕ), FiniteExperiment Θ (S n)
  valid : ∀ π n, IsFiniteExperiment (experiment π n)
  measurable : ∀ π n x, Measurable (fun θ => experiment π n θ x)
  refines : ∀ π m n, m ≤ n → FiniteBlackwellLE (experiment π m) (experiment π n)

/-- Passage to zero through positive tolerances, with a fixed continuous modulus. -/
theorem le_of_le_continuousAt_zero_pos {a : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousAt f 0)
    (h : ∀ r, 0 < r → r ≤ 1/2 → a ≤ f r) : a ≤ f 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d, hd, hc⟩ := Metric.continuousAt_iff.mp hf ε hε
  let r := min (d/2) (1/2 : ℝ)
  have hr : 0 < r := lt_min (half_pos hd) (by norm_num)
  have hrh : r ≤ 1/2 := min_le_right _ _
  have hrd : r < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  have hdist : dist r 0 < d := by simpa [Real.dist_eq, abs_of_pos hr] using hrd
  have habs : |f r - f 0| < ε := by simpa only [Real.dist_eq] using hc hdist
  have hb := h r hr hrh
  have hu := (abs_lt.mp habs).2
  linarith

namespace MeasurableFiniteProcess
variable {Θ P : Type*} [MeasurableSpace Θ]
  {S : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
  (M : MeasurableFiniteProcess Θ P S) (μ : Measure Θ) [IsProbabilityMeasure μ]

def indexed (π : P) (n : ℕ) : IndexedFiniteExperiment Θ S :=
  ⟨n, M.experiment π n, M.valid π n⟩

def averageDistance (E F : IndexedFiniteExperiment Θ S) : ℝ :=
  priorAverageDeficiency μ E.2.1 F.2.1

def AverageDominates (π ρ : P) : Prop :=
  FinitaryDominates M.indexed (averageDistance μ) π ρ

def UniformDominates (π ρ : P) : Prop :=
  FinitaryDominates M.indexed indexedFiniteDeficiency π ρ

def prefixInformation (π : P) (n : ℕ) : ℝ :=
  infinitePriorInformation μ (M.experiment π n)

def InformationBounded (π : P) : Prop := BddAbove (range (M.prefixInformation μ π))

/-- Real supremum, used only with a proved boundedness hypothesis. -/
def completeInformation (π : P) : ℝ := ⨆ n, M.prefixInformation μ π n

theorem prefixInformation_nonneg (π : P) (n : ℕ) : 0 ≤ M.prefixInformation μ π n :=
  measurable_infinitePriorInformation_nonneg μ _ (M.valid π n) (M.measurable π n)

theorem prefixInformation_mono (π : P) : Monotone (M.prefixInformation μ π) := by
  intro m n hmn
  obtain ⟨G, hG, he⟩ := M.refines π m n hmn
  have h := infinitePriorInformation_mono_garbling μ (M.experiment π n)
    (M.valid π n) (M.measurable π n) G hG
  rwa [he] at h

theorem prefixInformation_le_complete (π : P) (hb : M.InformationBounded μ π) (n : ℕ) :
    M.prefixInformation μ π n ≤ M.completeInformation μ π := le_ciSup hb n

theorem completeInformation_nonneg (π : P) (hb : M.InformationBounded μ π) :
    0 ≤ M.completeInformation μ π :=
  (M.prefixInformation_nonneg μ π 0).trans (M.prefixInformation_le_complete μ π hb 0)

theorem tendsto_prefixInformation (π : P) (hb : M.InformationBounded μ π) :
    Tendsto (M.prefixInformation μ π) atTop (𝓝 (M.completeInformation μ π)) :=
  tendsto_atTop_ciSup (M.prefixInformation_mono μ π) hb

theorem averageDominates_of_uniform [Nonempty Θ] {π ρ : P}
    (h : M.UniformDominates π ρ) : M.AverageDominates μ π ρ := by
  intro n ε hε
  obtain ⟨T, hT⟩ := h n ε hε
  refine ⟨T, fun t ht => ?_⟩
  exact (priorAverageDeficiency_le_finiteDeficiency μ _ _
    (M.valid π t) (M.valid ρ n) (M.measurable π t) (M.measurable ρ n)).trans_lt (hT t ht)

/-- A fixed finite target's information cannot exceed a bounded dominating total. -/
theorem prefixInformation_le_of_averageDominates {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) (n : ℕ) :
    M.prefixInformation μ ρ n ≤ M.completeInformation μ π := by
  classical
  have hl := le_of_le_continuousAt_zero_pos
    (a := M.prefixInformation μ ρ n)
    (f := fun r => M.completeInformation μ π + fanoModulus (Fintype.card (S n)) r)
    ((continuous_const.add (continuous_fanoModulus _)).continuousAt) (by
      intro r hr hrh
      obtain ⟨T, hT⟩ := h n r hr
      obtain ⟨G, hG, he⟩ := exists_decoder_lt_of_priorAverageDeficiency_lt μ
        (M.experiment π T) (M.experiment ρ n) (hT T le_rfl)
      have hEG := finiteDecisionLaw_valid _ (M.valid π T) G hG
      have hmEG := measurable_finiteDecisionLaw _ (M.measurable π T) G
      have hc := infinitePriorInformation_sub_le_fano_of_average_pos μ
        (M.experiment ρ n) (finiteDecisionLaw (M.experiment π T) G)
        (M.valid ρ n) hEG (M.measurable ρ n) hmEG r hr hrh (by
          have hs : priorAverageDecodeErr μ (M.experiment π T) (M.experiment ρ n) G ≤ r := he.le
          convert hs using 1
          apply integral_congr_ae
          filter_upwards with θ
          simp only [decodeErr, finiteTV, finiteDecisionLaw, abs_sub_comm])
      have hg := infinitePriorInformation_mono_garbling μ _ (M.valid π T)
        (M.measurable π T) G hG
      have hi := M.prefixInformation_le_complete μ π hb T
      dsimp [prefixInformation] at hi ⊢
      linarith)
  simpa using hl

theorem informationBounded_of_averageDominates {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) :
    M.InformationBounded μ ρ :=
  ⟨M.completeInformation μ π, by
    rintro _ ⟨n, rfl⟩
    exact M.prefixInformation_le_of_averageDominates μ hb h n⟩

theorem completeInformation_mono_of_averageDominates {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) :
    M.completeInformation μ ρ ≤ M.completeInformation μ π := by
  apply ciSup_le
  intro n
  exact M.prefixInformation_le_of_averageDominates μ hb h n

/-- Fix both record horizons, then send the forward simulation error to zero.
The source alphabet of the forward target remains fixed during this limit. -/
theorem reverse_prefix_le_information_tail {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) (m n : ℕ) :
    priorAverageDeficiency μ (M.experiment ρ m) (M.experiment π n) ≤
      Real.sqrt ((M.completeInformation μ π - M.prefixInformation μ ρ m)/2) := by
  classical
  have hl := le_of_le_continuousAt_zero_pos
    (a := priorAverageDeficiency μ (M.experiment ρ m) (M.experiment π n))
    (f := fun r => r + Real.sqrt ((M.completeInformation μ π -
      M.prefixInformation μ ρ m + fanoModulus (Fintype.card (S m)) r)/2))
    ((continuous_id.add (Real.continuous_sqrt.comp
      ((continuous_const.add (continuous_fanoModulus _)).div_const 2))).continuousAt) (by
      intro r hr hrh
      obtain ⟨T, hT⟩ := h m r hr
      let t := max n T
      obtain ⟨G, hG, he⟩ := exists_decoder_lt_of_priorAverageDeficiency_lt μ
        (M.experiment π t) (M.experiment ρ m) (hT t (le_max_right _ _))
      have hrev := priorAverageDeficiency_reverse_le μ
        (M.experiment π t) (M.experiment ρ m) (M.valid π t) (M.valid ρ m)
        (M.measurable π t) (M.measurable ρ m) G hG r hr hrh he.le
      have hzero := priorAverageDeficiency_eq_zero_of_blackwell μ _ _
        (M.refines π n t (le_max_left _ _))
      have htri := priorAverageDeficiency_triangle μ
        (M.experiment ρ m) (M.experiment π t) (M.experiment π n)
        (M.valid ρ m) (M.valid π t) (M.valid π n)
        (M.measurable ρ m) (M.measurable π t) (M.measurable π n)
      rw [hzero, add_zero] at htri
      have hi := M.prefixInformation_le_complete μ π hb t
      have hs : Real.sqrt ((infinitePriorInformation μ (M.experiment π t) -
          infinitePriorInformation μ (M.experiment ρ m) + fanoModulus (Fintype.card (S m)) r)/2) ≤
        Real.sqrt ((M.completeInformation μ π - M.prefixInformation μ ρ m +
          fanoModulus (Fintype.card (S m)) r)/2) := by
        apply Real.sqrt_le_sqrt
        dsimp [prefixInformation] at hi ⊢
        linarith
      exact htri.trans (hrev.trans (add_le_add_right hs r)))
  simpa using hl

/-- The quantitative reverse residual, in nats. No uniform deadline is asserted. -/
theorem reverse_residual_le_information_gap {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) (n : ℕ) :
    (⨅ t, priorAverageDeficiency μ (M.experiment ρ t) (M.experiment π n)) ≤
      Real.sqrt ((M.completeInformation μ π - M.completeInformation μ ρ)/2) := by
  have hbρ := M.informationBounded_of_averageDominates μ hb h
  have ht := (((tendsto_const_nhds (x := M.completeInformation μ π)).sub (M.tendsto_prefixInformation μ ρ hbρ)).div_const 2).sqrt
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro t
  apply (ciInf_le (f := fun s => priorAverageDeficiency μ
    (M.experiment ρ s) (M.experiment π n)) ?_ t).trans
    (M.reverse_prefix_le_information_tail μ hb h t n)
  exact ⟨0, by rintro _ ⟨s, rfl⟩; exact priorAverageDeficiency_nonneg μ _ _⟩

/-- Equality of finite information totals on a comparable pair is exactly
reverse prior-average finitary simulation. -/
theorem completeInformation_eq_iff_averageDominates_reverse {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) :
    M.completeInformation μ π = M.completeInformation μ ρ ↔ M.AverageDominates μ ρ π := by
  have hbρ := M.informationBounded_of_averageDominates μ hb h
  constructor
  · intro he n ε hε
    have ht : Tendsto (fun m => Real.sqrt
        ((M.completeInformation μ π - M.prefixInformation μ ρ m)/2)) atTop (𝓝 0) := by
      have ht := (((tendsto_const_nhds (x := M.completeInformation μ π)).sub (M.tendsto_prefixInformation μ ρ hbρ)).div_const 2).sqrt
      simpa only [he, sub_self, zero_div, Real.sqrt_zero] using ht
    have hev := (tendsto_order.mp ht).2 ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp hev
    exact ⟨T, fun t ht => (M.reverse_prefix_le_information_tail μ hb h t n).trans_lt (hT t ht)⟩
  · intro hr
    exact le_antisymm (M.completeInformation_mono_of_averageDominates μ hbρ hr)
      (M.completeInformation_mono_of_averageDominates μ hb h)

/-- Prefix refinement makes each fixed-target average deficiency decrease. -/
theorem averageDeficiency_antitone (π ρ : P) (n : ℕ) :
    Antitone (fun t => priorAverageDeficiency μ (M.experiment π t) (M.experiment ρ n)) := by
  intro s t hst
  have htri := priorAverageDeficiency_triangle μ (M.experiment π t) (M.experiment π s)
    (M.experiment ρ n) (M.valid π t) (M.valid π s) (M.valid ρ n)
    (M.measurable π t) (M.measurable π s) (M.measurable ρ n)
  rw [priorAverageDeficiency_eq_zero_of_blackwell μ _ _ (M.refines π s t hst), zero_add] at htri
  exact htri

/-- The eventual-tolerance order agrees with zero fixed-prefix residuals. -/
theorem averageDominates_iff_zero_residual (π ρ : P) :
    M.AverageDominates μ π ρ ↔
      ∀ n, (⨅ t, priorAverageDeficiency μ (M.experiment π t) (M.experiment ρ n)) = 0 := by
  have hbb n : BddBelow (range (fun t => priorAverageDeficiency μ
      (M.experiment π t) (M.experiment ρ n))) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact priorAverageDeficiency_nonneg μ _ _⟩
  constructor
  · intro h n
    apply le_antisymm _ (le_ciInf (fun _ => priorAverageDeficiency_nonneg μ _ _))
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨T, hT⟩ := h n ε hε
    rw [zero_add]
    exact (ciInf_le (hbb n) T).trans (hT T le_rfl).le
  · intro h n ε hε
    have hlt : (⨅ t, priorAverageDeficiency μ (M.experiment π t) (M.experiment ρ n)) < ε := by
      rw [h n]; exact hε
    obtain ⟨T, hT⟩ := exists_lt_of_ciInf_lt hlt
    exact ⟨T, fun t ht => (M.averageDeficiency_antitone μ π ρ n ht).trans_lt hT⟩

/-- Strict information loss is exactly a positive reverse residual somewhere. -/
theorem completeInformation_lt_iff_positive_reverse_residual {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) :
    M.completeInformation μ ρ < M.completeInformation μ π ↔
      ∃ n, 0 < ⨅ t, priorAverageDeficiency μ (M.experiment ρ t) (M.experiment π n) := by
  have hn n : 0 ≤ ⨅ t, priorAverageDeficiency μ (M.experiment ρ t) (M.experiment π n) :=
    le_ciInf (fun _ => priorAverageDeficiency_nonneg μ _ _)
  have hle := M.completeInformation_mono_of_averageDominates μ hb h
  constructor
  · intro hlt
    have hnot : ¬ M.AverageDominates μ ρ π := by
      intro hr
      have he := (M.completeInformation_eq_iff_averageDominates_reverse μ hb h).mpr hr
      rw [he] at hlt
      exact (lt_irrefl _) hlt
    rw [M.averageDominates_iff_zero_residual μ ρ π] at hnot
    obtain ⟨n, hne⟩ := not_forall.mp hnot
    exact ⟨n, lt_of_le_of_ne (hn n) (fun he => hne he.symm)⟩
  · rintro ⟨n, hpos⟩
    apply lt_of_le_of_ne hle
    intro he
    have hr := (M.completeInformation_eq_iff_averageDominates_reverse μ hb h).mp he.symm
    have hz := (M.averageDominates_iff_zero_residual μ ρ π).mp hr n
    rw [hz] at hpos
    exact (lt_irrefl _) hpos

/-- The exact capped finite-prefix bound from the written theorem. -/
theorem reverse_prefix_le_min_information_tail {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) (m n : ℕ) :
    priorAverageDeficiency μ (M.experiment ρ m) (M.experiment π n) ≤
      min 1 (Real.sqrt ((M.completeInformation μ π - M.prefixInformation μ ρ m)/2)) :=
  le_min (priorAverageDeficiency_le_one μ _ _ (M.valid ρ m) (M.valid π n)
    (M.measurable ρ m) (M.measurable π n)) (M.reverse_prefix_le_information_tail μ hb h m n)

/-- The exact capped reverse-residual bound from the written theorem. -/
theorem reverse_residual_le_min_information_gap {π ρ : P}
    (hb : M.InformationBounded μ π) (h : M.AverageDominates μ π ρ) (n : ℕ) :
    (⨅ t, priorAverageDeficiency μ (M.experiment ρ t) (M.experiment π n)) ≤
      min 1 (Real.sqrt ((M.completeInformation μ π - M.completeInformation μ ρ)/2)) := by
  apply le_min _ (M.reverse_residual_le_information_gap μ hb h n)
  apply (ciInf_le (f := fun t => priorAverageDeficiency μ
    (M.experiment ρ t) (M.experiment π n)) ?_ 0).trans
    (priorAverageDeficiency_le_one μ _ _ (M.valid ρ 0) (M.valid π n)
      (M.measurable ρ 0) (M.measurable π n))
  exact ⟨0, by rintro _ ⟨t, rfl⟩; exact priorAverageDeficiency_nonneg μ _ _⟩

/-- Average reverse recovery lifts to uniform reverse recovery on comparable pairs. -/
def AverageReverseLifts : Prop :=
  ∀ π ρ, M.UniformDominates π ρ → M.AverageDominates μ ρ π → M.UniformDominates ρ π

/-- The exact finite-valued strictness criterion, for any feasible policy family. -/
theorem completeInformation_strictlyFinitaryMonotone_iff [Nonempty Θ]
    (hb : ∀ π, M.InformationBounded μ π) :
    IsStrictlyFinitaryMonotone M.indexed indexedFiniteDeficiency (M.completeInformation μ) ↔
      M.AverageReverseLifts μ := by
  constructor
  · intro hJ π ρ hu ha
    by_contra hn
    have hlt := hJ.strict π ρ hu hn
    have he := (M.completeInformation_eq_iff_averageDominates_reverse μ (hb π)
      (M.averageDominates_of_uniform μ hu)).mpr ha
    rw [he] at hlt
    exact (lt_irrefl _) hlt
  · intro hU
    refine ⟨fun π ρ hu => M.completeInformation_mono_of_averageDominates μ (hb π)
      (M.averageDominates_of_uniform μ hu), ?_⟩
    intro π ρ hu hn
    have ha := M.averageDominates_of_uniform μ hu
    apply lt_of_le_of_ne (M.completeInformation_mono_of_averageDominates μ (hb π) ha)
    intro he
    have har := (M.completeInformation_eq_iff_averageDominates_reverse μ (hb π) ha).mp he.symm
    exact hn (hU π ρ hu har)

end MeasurableFiniteProcess
end
end IdExp
