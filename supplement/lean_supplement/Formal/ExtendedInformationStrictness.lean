import Formal.FinitaryInformationEquality

/-!
# The exact strictness criterion, including infinite information totals

The score is the actual extended-real supremum of finite-prefix mutual
information. Two separate obstructions are characterized: failure to lift
average reverse simulation to uniform reverse simulation on comparable pairs,
and a strict pair whose two totals are both infinite.
-/
namespace IdExp
open MeasureTheory Set Finset Filter Topology
open scoped ENNReal
noncomputable section
namespace MeasurableFiniteProcess
variable {Θ P : Type*} [MeasurableSpace Θ]
  {S : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
  (M : MeasurableFiniteProcess Θ P S) (μ : Measure Θ) [IsProbabilityMeasure μ]

/-- Actual complete mutual information, with infinite totals retained. -/
def totalInformation (π : P) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal (M.prefixInformation μ π n)

theorem informationBounded_iff_totalInformation_ne_top (π : P) :
    M.InformationBounded μ π ↔ M.totalInformation μ π ≠ ⊤ := by
  constructor
  · intro hb
    have hu : M.totalInformation μ π ≤ ENNReal.ofReal (M.completeInformation μ π) := by
      apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (M.prefixInformation_le_complete μ π hb n)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  · intro hn
    refine ⟨(M.totalInformation μ π).toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hn).mp (le_iSup
      (fun n => ENNReal.ofReal (M.prefixInformation μ π n)) n)

theorem totalInformation_toReal (π : P) :
    (M.totalInformation μ π).toReal = M.completeInformation μ π := by
  unfold totalInformation completeInformation
  rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (M.prefixInformation_nonneg μ π _)]

theorem totalInformation_eq_ofReal_complete (π : P) (hb : M.InformationBounded μ π) :
    M.totalInformation μ π = ENNReal.ofReal (M.completeInformation μ π) := by
  rw [← M.totalInformation_toReal μ π]
  exact (ENNReal.ofReal_toReal ((M.informationBounded_iff_totalInformation_ne_top μ π).mp hb)).symm

/-- Weak monotonicity holds even for infinite complete information. -/
theorem totalInformation_mono_of_averageDominates {π ρ : P}
    (h : M.AverageDominates μ π ρ) : M.totalInformation μ ρ ≤ M.totalInformation μ π := by
  by_cases hn : M.totalInformation μ π = ⊤
  · simp [hn]
  have hb := (M.informationBounded_iff_totalInformation_ne_top μ π).mpr hn
  have hbρ := M.informationBounded_of_averageDominates μ hb h
  rw [M.totalInformation_eq_ofReal_complete μ π hb, M.totalInformation_eq_ofReal_complete μ ρ hbρ]
  exact ENNReal.ofReal_le_ofReal (M.completeInformation_mono_of_averageDominates μ hb h)

/-- The finite-information equality theorem with the actual extended score. -/
theorem totalInformation_eq_iff_averageDominates_reverse {π ρ : P}
    (hb : M.totalInformation μ π ≠ ⊤) (h : M.AverageDominates μ π ρ) :
    M.totalInformation μ π = M.totalInformation μ ρ ↔ M.AverageDominates μ ρ π := by
  constructor
  · intro he
    have he' := congrArg ENNReal.toReal he
    rw [M.totalInformation_toReal, M.totalInformation_toReal] at he'
    exact (M.completeInformation_eq_iff_averageDominates_reverse μ
      ((M.informationBounded_iff_totalInformation_ne_top μ π).mpr hb) h).mp he'
  · intro hr
    exact le_antisymm (M.totalInformation_mono_of_averageDominates μ hr)
      (M.totalInformation_mono_of_averageDominates μ h)

/-- Strictness for the extended score; both weak and strict comparisons. -/
def TotalInformationStrictlyMonotone : Prop :=
  (∀ π ρ, M.UniformDominates π ρ → M.totalInformation μ ρ ≤ M.totalInformation μ π) ∧
  (∀ π ρ, M.UniformDominates π ρ → ¬ M.UniformDominates ρ π →
    M.totalInformation μ ρ < M.totalInformation μ π)

/-- Infinite saturation is forbidden only on strictly ordered pairs. -/
def NoInfiniteStrictPair : Prop :=
  ∀ π ρ, M.UniformDominates π ρ → ¬ M.UniformDominates ρ π →
    ¬ (M.totalInformation μ π = ⊤ ∧ M.totalInformation μ ρ = ⊤)

/-- **Exact iff:** strict uniform comparison preservation is equivalent to
average-to-uniform reverse lifting and absence of infinite strict-pair ties. -/
theorem totalInformation_strictlyMonotone_iff [Nonempty Θ] :
    M.TotalInformationStrictlyMonotone μ ↔
      M.AverageReverseLifts μ ∧ M.NoInfiniteStrictPair μ := by
  constructor
  · intro hJ
    constructor
    · intro π ρ hu ha
      by_contra hn
      have hlt := hJ.2 π ρ hu hn
      have hle := M.totalInformation_mono_of_averageDominates μ ha
      exact (not_lt_of_ge hle) hlt
    · intro π ρ hu hn he
      have hlt := hJ.2 π ρ hu hn
      rw [he.1, he.2] at hlt
      exact (lt_irrefl _) hlt
  · rintro ⟨hU, hS⟩
    refine ⟨fun π ρ hu => M.totalInformation_mono_of_averageDominates μ
      (M.averageDominates_of_uniform μ hu), ?_⟩
    intro π ρ hu hn
    have ha := M.averageDominates_of_uniform μ hu
    apply lt_of_le_of_ne (M.totalInformation_mono_of_averageDominates μ ha)
    intro he
    by_cases htop : M.totalInformation μ π = ⊤
    · exact hS π ρ hu hn ⟨htop, he.trans htop⟩
    have hr := (M.totalInformation_eq_iff_averageDominates_reverse μ htop ha).mp he.symm
    exact hn (hU π ρ hu hr)

end MeasurableFiniteProcess
end
end IdExp
