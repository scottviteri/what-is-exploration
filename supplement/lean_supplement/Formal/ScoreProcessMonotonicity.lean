import Formal.NativeProcess
import Formal.CausalProcess
import Formal.DeficiencyTriangle
import Formal.DecisionEnvelope
import Formal.CausalUniversality

/-!
# Scores that respect the finitary process order

Do intrinsic objectives respect *Blackwell improvement*, or the *finite-prefix
process order*?  For a score on prefix experiments the two are connected by
one property, **deficiency continuity**: `J` is deficiency-continuous at a
target `F` with modulus `ω` when simulating `F` from any source `E` to
directed error `r` bounds the score shortfall `J F - J E` by `ω r`.  Exact
Blackwell monotonicity is the case `r = 0`.

The abstract theorem shows that a deficiency-continuous score is eventually
dominated, prefix by prefix, along any finitarily dominating process, so its
process supremum is monotone in the finitary preorder.  Nothing about priors,
finiteness of the world class, decoder attainment, or rates is used.

Three score families are deficiency-continuous with modulus one on the actual
causal prefix chain: negative directed deficiency to a fixed valid target,
negative fixed-depth native audits, and optimized unit-range decision values
for a fixed finitely supported prior and task.  Information gain with finite
signals needs a signal-size-dependent modulus (a coupling/Fano bound).  That
modulus is recorded as a hypothesis in the abstract theorem and is *not*
proved in this module.
-/

namespace IdExp

open Finset Set

/-! ## Abstract layer -/

section Abstract

variable {P X : Type*}

/-- A modulus that vanishes at zero from the right. -/
def VanishingModulus (ω : ℝ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ η, 0 < η ∧ ∀ r, 0 ≤ r → r < η → ω r ≤ ε

theorem vanishingModulus_id : VanishingModulus id :=
  fun ε hε => ⟨ε, hε, fun _ _ hr => hr.le⟩

theorem vanishingModulus_of_le {ω ω' : ℝ → ℝ} (hω' : VanishingModulus ω')
    (hle : ∀ r, 0 ≤ r → ω r ≤ ω' r) : VanishingModulus ω := by
  intro ε hε
  obtain ⟨η, hη, h⟩ := hω' ε hε
  exact ⟨η, hη, fun r hr0 hr => (hle r hr0).trans (h r hr0 hr)⟩

/-- `J` is deficiency-continuous at target `F` with modulus `ω`: simulating
`F` from any source `E` to directed error `δ E F` bounds the shortfall of
the target's score by `ω (δ E F)`. -/
def DeficiencyContinuousAt (δ : X → X → ℝ) (J : X → ℝ) (ω : ℝ → ℝ) (F : X) : Prop :=
  ∀ E, J F ≤ J E + ω (δ E F)

/-- Deficiency continuity with a modulus vanishing at zero contains exact
Blackwell monotonicity: zero deficiency gives a score comparison. -/
theorem le_of_deficiencyContinuousAt_of_eq_zero {δ : X → X → ℝ} {J : X → ℝ}
    {ω : ℝ → ℝ} (hω0 : ω 0 = 0) {E F : X}
    (hcont : DeficiencyContinuousAt δ J ω F) (hEF : δ E F = 0) :
    J F ≤ J E := by
  have h := hcont E
  rw [hEF, hω0, add_zero] at h
  exact h

/-- **Eventual score dominance at one fixed rival prefix.**  If `π`
finitarily dominates `σ` and `J` is deficiency-continuous at the rival prefix
`K σ n`, then all sufficiently late prefixes of `π` score at least as well as
that rival prefix, up to any positive tolerance. -/
theorem finitaryDominates_score_eventually_le
    (K : P → ℕ → X) (δ : X → X → ℝ) (hδ : ∀ x y, 0 ≤ δ x y)
    (J : X → ℝ) (ω : ℝ → ℝ) (hω : VanishingModulus ω)
    {π σ : P} (hdom : FinitaryDominates K δ π σ) (n : ℕ)
    (hcont : DeficiencyContinuousAt δ J ω (K σ n)) :
    ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → J (K σ n) ≤ J (K π t) + ε := by
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := hω ε hε
  obtain ⟨T, hT⟩ := hdom n η hη
  refine ⟨T, fun t ht => ?_⟩
  have h1 := hcont (K π t)
  have h2 := hηε _ (hδ _ _) (hT t ht)
  linarith

/-- The process score of a prefix chain: the supremum of its prefix scores.
For a score that cannot decrease along prefixes this is the terminal score. -/
noncomputable def processScoreSup (K : P → ℕ → X) (J : X → ℝ) (π : P) : ℝ :=
  sSup (Set.range fun t => J (K π t))

theorem le_processScoreSup (K : P → ℕ → X) (J : X → ℝ) (π : P)
    (hbdd : BddAbove (Set.range fun t => J (K π t))) (t : ℕ) :
    J (K π t) ≤ processScoreSup K J π :=
  le_csSup hbdd ⟨t, rfl⟩

/-- Every fixed rival prefix score is at most the dominating process score. -/
theorem score_le_processScoreSup_of_finitaryDominates
    (K : P → ℕ → X) (δ : X → X → ℝ) (hδ : ∀ x y, 0 ≤ δ x y)
    (J : X → ℝ) (ω : ℝ → ℝ) (hω : VanishingModulus ω)
    {π σ : P} (hdom : FinitaryDominates K δ π σ)
    (hbdd : BddAbove (Set.range fun t => J (K π t)))
    (n : ℕ) (hcont : DeficiencyContinuousAt δ J ω (K σ n)) :
    J (K σ n) ≤ processScoreSup K J π := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T, hT⟩ :=
    finitaryDominates_score_eventually_le K δ hδ J ω hω hdom n hcont ε hε
  have h1 := hT T le_rfl
  have h2 := le_processScoreSup K J π hbdd T
  linarith

/-- **Process scores are monotone in the finitary order.**  A deficiency-
continuous score's process supremum cannot prefer a finitarily dominated
process. -/
theorem processScoreSup_mono_of_finitaryDominates
    (K : P → ℕ → X) (δ : X → X → ℝ) (hδ : ∀ x y, 0 ≤ δ x y)
    (J : X → ℝ) (ω : ℝ → ℝ) (hω : VanishingModulus ω)
    {π σ : P} (hdom : FinitaryDominates K δ π σ)
    (hbdd : BddAbove (Set.range fun t => J (K π t)))
    (hcont : ∀ n, DeficiencyContinuousAt δ J ω (K σ n)) :
    processScoreSup K J σ ≤ processScoreSup K J π := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact score_le_processScoreSup_of_finitaryDominates K δ hδ J ω hω hdom hbdd n (hcont n)

/-- Mutually dominant processes have equal process scores. -/
theorem processScoreSup_eq_of_mutual_finitaryDominates
    (K : P → ℕ → X) (δ : X → X → ℝ) (hδ : ∀ x y, 0 ≤ δ x y)
    (J : X → ℝ) (ω : ℝ → ℝ) (hω : VanishingModulus ω)
    {π σ : P} (hπσ : FinitaryDominates K δ π σ) (hσπ : FinitaryDominates K δ σ π)
    (hbddπ : BddAbove (Set.range fun t => J (K π t)))
    (hbddσ : BddAbove (Set.range fun t => J (K σ t)))
    (hcont : ∀ ρ n, DeficiencyContinuousAt δ J ω (K ρ n)) :
    processScoreSup K J σ = processScoreSup K J π :=
  le_antisymm
    (processScoreSup_mono_of_finitaryDominates K δ hδ J ω hω hπσ hbddπ (hcont σ))
    (processScoreSup_mono_of_finitaryDominates K δ hδ J ω hω hσπ hbddσ (hcont π))

/-- A finitarily greatest process has the largest process score among all
processes, for every deficiency-continuous bounded score. -/
theorem processScoreSup_le_of_finitarilyGreatest
    (K : P → ℕ → X) (δ : X → X → ℝ) (hδ : ∀ x y, 0 ≤ δ x y)
    (J : X → ℝ) (ω : ℝ → ℝ) (hω : VanishingModulus ω)
    {π : P} (hgreat : FinitarilyGreatest K δ π)
    (hbdd : BddAbove (Set.range fun t => J (K π t)))
    (hcont : ∀ ρ n, DeficiencyContinuousAt δ J ω (K ρ n)) (σ : P) :
    processScoreSup K J σ ≤ processScoreSup K J π :=
  processScoreSup_mono_of_finitaryDominates K δ hδ J ω hω (hgreat σ) hbdd (hcont σ)

end Abstract

/-! ## The actual causal prefix chain -/

section Causal

set_option linter.unusedSectionVars false

universe u

variable {A O Θ : Type u} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- Valid prefix experiments packaged with their horizon, so that one carrier
indexes experiments on horizon-dependent trace alphabets. -/
def ValidCausalPrefix (A O Θ : Type u) [Fintype A] [Fintype O] :=
  Σ t : ℕ, {E : FiniteExperiment Θ (CausalFiniteTrace A O t) // IsFiniteExperiment E}

/-- Directed deficiency between packaged prefix experiments. -/
noncomputable def validCausalPrefixDeficiency (x y : ValidCausalPrefix A O Θ) : ℝ :=
  finiteDeficiency x.2.1 y.2.1

/-- The packaged prefix chain of a valid causal policy on a valid class. -/
noncomputable def validCausalPrefixChain (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) (t : ℕ) :
    ValidCausalPrefix A O Θ :=
  ⟨t, ⟨causalFiniteExperiment π.1 Qs t, causalFiniteExperiment_valid π.1 π.2 Qs hQ t⟩⟩

theorem validCausalPrefixDeficiency_nonneg (x y : ValidCausalPrefix A O Θ) :
    0 ≤ validCausalPrefixDeficiency x y := by
  haveI := nonempty_of_isFiniteExperiment y.2.1 y.2.2
  exact finiteDeficiency_nonneg_of_valid x.2.1 y.2.1 x.2.2 y.2.2

/-- Causal finitary dominance is literally the abstract finitary dominance of
the packaged chains. -/
theorem causalFinitaryDominates_iff_packaged (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π ρ : ValidCausalPolicy A O) :
    CausalFinitaryDominates Qs π ρ ↔
      FinitaryDominates (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency π ρ :=
  Iff.rfl

/-! ### Negative deficiency to a fixed target -/

/-- Negative directed deficiency to a fixed valid target is deficiency-
continuous with modulus one, by the deficiency triangle inequality. -/
theorem negDeficiency_deficiencyContinuousAt {Z : Type*} [Fintype Z]
    (T : FiniteExperiment Θ Z) (hT : IsFiniteExperiment T)
    (F : ValidCausalPrefix A O Θ) :
    DeficiencyContinuousAt validCausalPrefixDeficiency
      (fun x : ValidCausalPrefix A O Θ => -finiteDeficiency x.2.1 T) id F := by
  intro E
  have h := finiteDeficiency_triangle E.2.1 F.2.1 T E.2.2 F.2.2 hT
  simp only [id_eq, validCausalPrefixDeficiency]
  linarith

/-- Along a finitarily dominating policy, the deficiency to any fixed valid
target eventually falls below the rival's deficiency plus any tolerance. -/
theorem causalFinitaryDominates_deficiency_eventually_le {Z : Type*} [Fintype Z]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (T : FiniteExperiment Θ Z) (hT : IsFiniteExperiment T)
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) (n : ℕ) :
    ∀ ε, 0 < ε → ∃ T', ∀ t, T' ≤ t →
      finiteDeficiency (causalFiniteExperiment π.1 Qs t) T ≤
        finiteDeficiency (causalFiniteExperiment ρ.1 Qs n) T + ε := by
  intro ε hε
  obtain ⟨T', hT'⟩ := finitaryDominates_score_eventually_le
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg
    (fun x : ValidCausalPrefix A O Θ => -finiteDeficiency x.2.1 T) id vanishingModulus_id
    ((causalFinitaryDominates_iff_packaged Qs hQ π ρ).1 hdom) n
    (negDeficiency_deficiencyContinuousAt T hT _) ε hε
  refine ⟨T', fun t ht => ?_⟩
  have h := hT' t ht
  change -finiteDeficiency (causalFiniteExperiment ρ.1 Qs n) T ≤
    -finiteDeficiency (causalFiniteExperiment π.1 Qs t) T + ε at h
  linarith

/-! ### Negative fixed-depth native audits -/

/-- The fixed-depth native audit is one-Lipschitz in its source: auditing a
source is at most auditing a simulator of it plus the simulation error. -/
theorem causalNativeDeficiency_le_add_deficiency
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (m : ℕ)
    (E F : ValidCausalPrefix A O Θ) :
    causalNativeDeficiency E.2.1 Qs m ≤
      finiteDeficiency E.2.1 F.2.1 + causalNativeDeficiency F.2.1 Qs m := by
  classical
  unfold causalNativeDeficiency
  apply Finset.sup'_le
  intro τ _
  have htri := finiteDeficiency_triangle E.2.1 F.2.1
    (causalPlanObservationExperiment m τ Qs) E.2.2 F.2.2
    (causalPlanObservationExperiment_valid m τ Qs hQ)
  have hle : finiteDeficiency F.2.1 (causalPlanObservationExperiment m τ Qs) ≤
      (Finset.univ : Finset (CausalPlan A O m)).sup' Finset.univ_nonempty
        (fun τ => finiteDeficiency F.2.1 (causalPlanObservationExperiment m τ Qs)) :=
    Finset.le_sup' (fun τ => finiteDeficiency F.2.1 (causalPlanObservationExperiment m τ Qs))
      (Finset.mem_univ τ)
  linarith

/-- The negative fixed-depth native audit is deficiency-continuous with
modulus one. -/
theorem negNativeAudit_deficiencyContinuousAt
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (m : ℕ)
    (F : ValidCausalPrefix A O Θ) :
    DeficiencyContinuousAt validCausalPrefixDeficiency
      (fun x : ValidCausalPrefix A O Θ => -causalNativeDeficiency x.2.1 Qs m) id F := by
  intro E
  have h := causalNativeDeficiency_le_add_deficiency Qs hQ m E F
  simp only [id_eq, validCausalPrefixDeficiency]
  linarith

/-- **Fixed-depth native audits respect the finitary order eventually.**
Along a finitarily dominating policy, the depth-`m` native audit eventually
falls below the rival's depth-`m` audit plus any tolerance, for every `m`. -/
theorem causalFinitaryDominates_nativeAudit_eventually_le
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) (m n : ℕ) :
    ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
      causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs m ≤
        causalNativeDeficiency (causalFiniteExperiment ρ.1 Qs n) Qs m + ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := finitaryDominates_score_eventually_le
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg
    (fun x : ValidCausalPrefix A O Θ => -causalNativeDeficiency x.2.1 Qs m) id
    vanishingModulus_id
    ((causalFinitaryDominates_iff_packaged Qs hQ π ρ).1 hdom) n
    (negNativeAudit_deficiencyContinuousAt Qs hQ m _) ε hε
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  change -causalNativeDeficiency (causalFiniteExperiment ρ.1 Qs n) Qs m ≤
    -causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs m + ε at h
  linarith

/-! ### Optimized decision values for a fixed finitely supported task -/

/-- The optimized value of a fixed finitely supported decision problem is
deficiency-continuous with modulus one, by quantitative decision readiness. -/
theorem decisionProblemValue_deficiencyContinuousAt
    (Pr : FiniteSupportDecisionProblem Θ) (F : ValidCausalPrefix A O Θ) :
    DeficiencyContinuousAt validCausalPrefixDeficiency
      (fun x : ValidCausalPrefix A O Θ => finiteDecisionProblemValue x.2.1 Pr) id F := by
  intro E
  haveI := nonempty_of_isFiniteExperiment F.2.1 F.2.2
  have h := finiteDecisionProblemValue_sub_le_deficiency E.2.1 F.2.1 E.2.2 F.2.2 Pr
  simp only [id_eq, validCausalPrefixDeficiency]
  linarith

/-- **Decision values respect the finitary order eventually.**  Along a
finitarily dominating policy, every fixed finitely supported decision
problem's optimized value eventually exceeds the rival prefix's value minus
any tolerance.  The task may be chosen after the policies; the cutoff may
depend on it. -/
theorem causalFinitaryDominates_decisionValue_eventually_ge
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (Pr : FiniteSupportDecisionProblem Θ)
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) (n : ℕ) :
    ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
      finiteDecisionProblemValue (causalFiniteExperiment ρ.1 Qs n) Pr ≤
        finiteDecisionProblemValue (causalFiniteExperiment π.1 Qs t) Pr + ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := finitaryDominates_score_eventually_le
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg
    (fun x : ValidCausalPrefix A O Θ => finiteDecisionProblemValue x.2.1 Pr) id
    vanishingModulus_id
    ((causalFinitaryDominates_iff_packaged Qs hQ π ρ).1 hdom) n
    (decisionProblemValue_deficiencyContinuousAt Pr _) ε hε
  exact ⟨T, fun t ht => hT t ht⟩

/-! ### Process-level statements -/

/-- The terminal (supremal) decision value of a policy's prefix chain. -/
noncomputable def causalTerminalDecisionValue (Qs : Θ → CausalResponse A O)
    (Pr : FiniteSupportDecisionProblem Θ) (π : ValidCausalPolicy A O) : ℝ :=
  sSup (Set.range fun t => finiteDecisionProblemValue (causalFiniteExperiment π.1 Qs t) Pr)

/-- **Terminal decision values are monotone in the finitary process order.**
No prior on the world class, finiteness, or attainment is assumed; the
task's prior is finitely supported. -/
theorem causalTerminalDecisionValue_mono_of_finitaryDominates
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (Pr : FiniteSupportDecisionProblem Θ)
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) :
    causalTerminalDecisionValue Qs Pr ρ ≤ causalTerminalDecisionValue Qs Pr π := by
  have hbdd : BddAbove (Set.range fun t =>
      finiteDecisionProblemValue (causalFiniteExperiment π.1 Qs t) Pr) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (finiteDecisionProblemValue_mem_unitInterval _
      (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) Pr).2
  have h := processScoreSup_mono_of_finitaryDominates
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg
    (fun x : ValidCausalPrefix A O Θ => finiteDecisionProblemValue x.2.1 Pr) id
    vanishingModulus_id
    ((causalFinitaryDominates_iff_packaged Qs hQ π ρ).1 hdom) hbdd
    (fun n => decisionProblemValue_deficiencyContinuousAt Pr _)
  exact h

/-- The terminal negative native audit at a fixed depth. -/
noncomputable def causalTerminalNegNativeAudit (Qs : Θ → CausalResponse A O) (m : ℕ)
    (π : ValidCausalPolicy A O) : ℝ :=
  sSup (Set.range fun t => -causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs m)

/-- **Terminal negative native audits are monotone in the finitary order.**
Thus the prior-free score `-Γ_{≤m}` respects the finite-prefix comparison at
the process level, for every fixed target depth `m`. -/
theorem causalTerminalNegNativeAudit_mono_of_finitaryDominates
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (m : ℕ)
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) :
    causalTerminalNegNativeAudit Qs m ρ ≤ causalTerminalNegNativeAudit Qs m π := by
  have hbdd : BddAbove (Set.range fun t =>
      -causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs m) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h0 : 0 ≤ causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs m := by
      classical
      unfold causalNativeDeficiency
      obtain ⟨τ, -⟩ := (Finset.univ_nonempty : (Finset.univ : Finset (CausalPlan A O m)).Nonempty)
      exact le_trans (finiteDeficiency_nonneg_of_valid _ _
        (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
        (causalPlanObservationExperiment_valid m τ Qs hQ))
        (Finset.le_sup' (fun τ => finiteDeficiency (causalFiniteExperiment π.1 Qs t)
          (causalPlanObservationExperiment m τ Qs)) (Finset.mem_univ τ))
    linarith
  have h := processScoreSup_mono_of_finitaryDominates
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg
    (fun x : ValidCausalPrefix A O Θ => -causalNativeDeficiency x.2.1 Qs m) id
    vanishingModulus_id
    ((causalFinitaryDominates_iff_packaged Qs hQ π ρ).1 hdom) hbdd
    (fun n => negNativeAudit_deficiencyContinuousAt Qs hQ m _)
  exact h

end Causal

end IdExp
