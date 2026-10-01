import Formal.CausalProfile

/-!
# Deterministic deficiency: the Dirac dichotomy and the deterministic causal bridge

**Relevance:** direct current-paper support for the deterministic-class
trace-separation theorem (open question Q4, `Formal/OPEN_PROBLEMS.md`).

A *Dirac* finite experiment reveals a deterministic signal `e θ` in world `θ`.
Between two Dirac experiments the directed deficiency is a two-valued
combinatorial quantity:

* it is `0` exactly when the source signal separates every pair the target
  separates (`e θ = e θ' → f θ = f θ'`); and
* otherwise it is at least `1/2`: a shared source signal must decode to two
  different target signals, and a probability row cannot put more than total
  mass one on both.

The second half of the module applies this to the causal ontology.  A
deterministic response kernel and a deterministic policy produce, at every
horizon, exactly one length-`n` trace per world, so the acquired experiment is
Dirac at that trace, and every deterministic native test is Dirac at its
observation word.  Consequently the depth-`n` native deficiency of the
acquired depth-`t` experiment is zero exactly when worlds with equal
length-`t` traces have equal depth-`n` plan experiments, and native
sufficiency of the deterministic policy on a finite class of deterministic
worlds is equivalent to the length-`t` trace map separating, for some finite
`t`, every pair of worlds that is not controlled-trace equivalent.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

/-! ## Dirac finite experiments -/

section Dirac

variable {Θ X Y : Type*} [Fintype X] [Fintype Y]

/-- The Dirac finite experiment revealing the deterministic signal `e θ`. -/
noncomputable def diracExp (e : Θ → X) : FiniteExperiment Θ X := by
  classical
  exact fun θ x => if x = e θ then 1 else 0

theorem diracExp_self (e : Θ → X) (θ : Θ) : diracExp e θ (e θ) = 1 := by
  simp [diracExp]

theorem diracExp_of_ne (e : Θ → X) (θ : Θ) {x : X} (hx : x ≠ e θ) :
    diracExp e θ x = 0 := by
  simp [diracExp, hx]

theorem diracExp_apply [DecidableEq X] (e : Θ → X) (θ : Θ) (x : X) :
    diracExp e θ x = if x = e θ then 1 else 0 := by
  by_cases hx : x = e θ
  · rw [if_pos hx, hx, diracExp_self]
  · rw [if_neg hx, diracExp_of_ne e θ hx]

/-- Under any decidable equality, the Dirac row is `Pi.single (e θ) 1`. -/
theorem diracExp_eq_pi_single [DecidableEq X] (e : Θ → X) (θ : Θ) :
    diracExp e θ = Pi.single (e θ) 1 := by
  funext x
  rw [diracExp_apply, Pi.single_apply]

theorem diracExp_nonneg (e : Θ → X) (θ : Θ) (x : X) : 0 ≤ diracExp e θ x := by
  by_cases hx : x = e θ
  · rw [hx, diracExp_self]; norm_num
  · rw [diracExp_of_ne e θ hx]

theorem sum_diracExp (e : Θ → X) (θ : Θ) : ∑ x, diracExp e θ x = 1 := by
  classical
  simp [diracExp_apply]

/-- Dirac experiments are genuine finite experiments. -/
theorem diracExp_valid (e : Θ → X) : IsFiniteExperiment (diracExp e) :=
  fun θ => ⟨diracExp_nonneg e θ, sum_diracExp e θ⟩

/-- Two Dirac rows coincide exactly when their signals coincide. -/
theorem diracExp_row_eq_iff (e : Θ → X) (θ θ' : Θ) :
    diracExp e θ = diracExp e θ' ↔ e θ = e θ' := by
  constructor
  · intro h
    have h1 := congrFun h (e θ)
    rw [diracExp_self] at h1
    by_contra hne
    have hne' : e θ ≠ e θ' := hne
    rw [diracExp_of_ne e θ' hne'] at h1
    exact one_ne_zero h1
  · intro h
    funext x
    by_cases hx : x = e θ
    · rw [hx, diracExp_self, h, diracExp_self]
    · rw [diracExp_of_ne e θ hx, diracExp_of_ne e θ' (h ▸ hx)]

/-- Decoding a Dirac source through `G` reads off the row `G (e θ)`. -/
theorem finiteDecisionLaw_diracExp (e : Θ → X) (G : X → Y → ℝ) (θ : Θ) :
    finiteDecisionLaw (diracExp e) G θ = G (e θ) := by
  classical
  funext y
  unfold finiteDecisionLaw
  simp [diracExp_apply]

/-- Every entry of a stochastic row is at most one. -/
theorem stochasticRules_le_one {G : X → Y → ℝ} (hG : G ∈ stochasticRules X Y)
    (x : X) (y : Y) : G x y ≤ 1 := by
  have hrow := hG x (Set.mem_univ x)
  calc
    G x y ≤ ∑ y', G x y' :=
      Finset.single_le_sum (fun y' _ => hrow.1 y') (Finset.mem_univ y)
    _ = 1 := hrow.2

/-- Two distinct entries of a stochastic row have total mass at most one. -/
theorem stochasticRules_add_le_one {G : X → Y → ℝ}
    (hG : G ∈ stochasticRules X Y) (x : X) {y y' : Y} (hne : y ≠ y') :
    G x y + G x y' ≤ 1 := by
  classical
  have hrow := hG x (Set.mem_univ x)
  calc
    G x y + G x y' = ∑ z ∈ ({y, y'} : Finset Y), G x z :=
      (Finset.sum_pair hne).symm
    _ ≤ ∑ z, G x z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ => hrow.1 z)
    _ = 1 := hrow.2

/-- **Decoder error between Dirac experiments.**  Decoding the Dirac source
`e` into the Dirac target `f` through a stochastic `G` errs, in world `θ`, by
exactly the mass `G` fails to put on the correct target signal. -/
theorem decodeErr_diracExp (e : Θ → X) (f : Θ → Y) {G : X → Y → ℝ}
    (hG : G ∈ stochasticRules X Y) (θ : Θ) :
    decodeErr (diracExp e) (diracExp f) G θ = 1 - G (e θ) (f θ) := by
  classical
  have hrow := hG (e θ) (Set.mem_univ (e θ))
  have hle := stochasticRules_le_one hG (e θ) (f θ)
  have hpoint : ∀ y,
      |(∑ x, diracExp e θ x * G x y) - diracExp f θ y| =
        G (e θ) y + (if y = f θ then 1 - 2 * G (e θ) y else 0) := by
    intro y
    have hsum : (∑ x, diracExp e θ x * G x y) = G (e θ) y := by
      have := congrFun (finiteDecisionLaw_diracExp e G θ) y
      simpa [finiteDecisionLaw] using this
    rw [hsum, diracExp_apply]
    by_cases hy : y = f θ
    · rw [if_pos hy, if_pos hy, hy]
      rw [abs_of_nonpos (by linarith)]
      ring
    · rw [if_neg hy, if_neg hy, sub_zero, add_zero]
      exact abs_of_nonneg (hrow.1 y)
  unfold decodeErr
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (f θ), hrow.2]
  simp
  ring


/-! ## The Dirac deficiency dichotomy -/

/-- `e` *separates for* `f` when equal source signals force equal target
signals: the source distinguishes every pair the target distinguishes. -/
def SeparatesFor (e : Θ → X) (f : Θ → Y) : Prop :=
  ∀ θ θ', e θ = e θ' → f θ = f θ'

/-- Some pair of worlds *merges* under `e` while `f` still tells them apart. -/
def MergesSomePair (e : Θ → X) (f : Θ → Y) : Prop :=
  ∃ θ θ', e θ = e θ' ∧ f θ ≠ f θ'

theorem not_separatesFor_iff (e : Θ → X) (f : Θ → Y) :
    ¬ SeparatesFor e f ↔ MergesSomePair e f := by
  unfold SeparatesFor MergesSomePair
  constructor
  · intro h
    push Not at h
    exact h
  · rintro ⟨θ, θ', he, hf⟩ h
    exact hf (h θ θ' he)

/-- The deterministic preimage decoder: send a source signal to the target
signal of some world producing it (an arbitrary world when none does). -/
noncomputable def diracPreimageDecoder [Nonempty Θ] (e : Θ → X) (f : Θ → Y) :
    X → Y → ℝ := by
  classical
  exact fun x y =>
    if y = f (if hx : ∃ θ, e θ = x then Classical.choose hx
              else Classical.arbitrary Θ) then 1 else 0

theorem diracPreimageDecoder_mem_stochasticRules [Nonempty Θ]
    (e : Θ → X) (f : Θ → Y) :
    diracPreimageDecoder e f ∈ stochasticRules X Y := by
  classical
  intro x _
  constructor
  · intro y
    unfold diracPreimageDecoder
    split_ifs <;> norm_num
  · simp [diracPreimageDecoder]

/-- When `e` separates for `f`, the preimage decoder is exact at every world. -/
theorem diracPreimageDecoder_apply_of_separates [Nonempty Θ]
    {e : Θ → X} {f : Θ → Y} (hsep : SeparatesFor e f) (θ : Θ) :
    diracPreimageDecoder e f (e θ) (f θ) = 1 := by
  classical
  have hx : ∃ θ', e θ' = e θ := ⟨θ, rfl⟩
  have hf : f (Classical.choose hx) = f θ :=
    hsep _ _ (Classical.choose_spec hx)
  unfold diracPreimageDecoder
  rw [dif_pos hx, hf, if_pos rfl]

/-- Separation gives zero deficiency: the preimage decoder is exact. -/
theorem finiteDeficiency_diracExp_eq_zero_of_separates [Nonempty Θ]
    {e : Θ → X} {f : Θ → Y} (hsep : SeparatesFor e f) :
    finiteDeficiency (diracExp e) (diracExp f) = 0 := by
  have : Nonempty Y := ⟨f (Classical.arbitrary Θ)⟩
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder (diracExp e) (diracExp f)
      (diracPreimageDecoder e f) (diracPreimageDecoder_mem_stochasticRules e f)
    intro θ
    rw [decodeErr_diracExp e f (diracPreimageDecoder_mem_stochasticRules e f) θ,
      diracPreimageDecoder_apply_of_separates hsep θ]
    norm_num
  · exact finiteDeficiency_nonneg_of_valid _ _ (diracExp_valid e) (diracExp_valid f)

/-- A merged pair forces every decoder to err by at least one half at one
of the two worlds: the shared source row must split its mass between two
different target signals. -/
theorem half_le_decodeErr_of_merge {e : Θ → X} {f : Θ → Y}
    {G : X → Y → ℝ} (hG : G ∈ stochasticRules X Y)
    {θ θ' : Θ} (he : e θ = e θ') (hf : f θ ≠ f θ') :
    1 / 2 ≤ max (decodeErr (diracExp e) (diracExp f) G θ)
      (decodeErr (diracExp e) (diracExp f) G θ') := by
  rw [decodeErr_diracExp e f hG θ, decodeErr_diracExp e f hG θ', ← he]
  have hsum := stochasticRules_add_le_one hG (e θ) hf
  rcases le_total (G (e θ) (f θ)) (G (e θ) (f θ')) with h | h
  · rw [max_eq_left (by linarith)]
    linarith
  · rw [max_eq_right (by linarith)]
    linarith

/-- **Merging lower bound.**  If some pair merges under the source while the
target separates it, the directed deficiency is at least one half. -/
theorem half_le_finiteDeficiency_diracExp_of_merge [Nonempty Θ]
    {e : Θ → X} {f : Θ → Y} (hmerge : MergesSomePair e f) :
    1 / 2 ≤ finiteDeficiency (diracExp e) (diracExp f) := by
  have : Nonempty Y := ⟨f (Classical.arbitrary Θ)⟩
  obtain ⟨θ, θ', he, hf⟩ := hmerge
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
    (diracExp_valid e) (diracExp_valid f))
  rintro c ⟨G, hG, herr⟩
  exact (half_le_decodeErr_of_merge hG he hf).trans
    (max_le (herr θ) (herr θ'))

/-- **The Dirac deficiency dichotomy, zero form.**  Between Dirac
experiments the directed deficiency vanishes exactly when the source signal
separates every pair of worlds the target signal separates. -/
theorem finiteDeficiency_diracExp_eq_zero_iff [Nonempty Θ]
    (e : Θ → X) (f : Θ → Y) :
    finiteDeficiency (diracExp e) (diracExp f) = 0 ↔ SeparatesFor e f := by
  constructor
  · intro h
    by_contra hsep
    have hmerge := (not_separatesFor_iff e f).1 hsep
    have := half_le_finiteDeficiency_diracExp_of_merge hmerge
    rw [h] at this
    norm_num at this
  · exact finiteDeficiency_diracExp_eq_zero_of_separates

/-- **The Dirac deficiency dichotomy.**  Between Dirac experiments the
directed deficiency is either exactly zero or at least one half. -/
theorem finiteDeficiency_dirac_dichotomy [Nonempty Θ]
    (e : Θ → X) (f : Θ → Y) :
    finiteDeficiency (diracExp e) (diracExp f) = 0 ∨
      1 / 2 ≤ finiteDeficiency (diracExp e) (diracExp f) := by
  by_cases hsep : SeparatesFor e f
  · exact Or.inl (finiteDeficiency_diracExp_eq_zero_of_separates hsep)
  · exact Or.inr (half_le_finiteDeficiency_diracExp_of_merge
      ((not_separatesFor_iff e f).1 hsep))

/-- Small deficiency between Dirac experiments already forces zero. -/
theorem finiteDeficiency_diracExp_eq_zero_of_lt_half [Nonempty Θ]
    {e : Θ → X} {f : Θ → Y}
    (h : finiteDeficiency (diracExp e) (diracExp f) < 1 / 2) :
    finiteDeficiency (diracExp e) (diracExp f) = 0 := by
  rcases finiteDeficiency_dirac_dichotomy e f with h0 | hhalf
  · exact h0
  · exact absurd h (not_lt.2 hhalf)


/-! ### Literal `Pi.single` forms -/

/-- As a whole experiment, the Dirac experiment is `θ ↦ Pi.single (e θ) 1`. -/
theorem diracExp_eq_pi_single_fun [DecidableEq X] (e : Θ → X) :
    diracExp e = fun θ => Pi.single (e θ) 1 :=
  funext fun θ => diracExp_eq_pi_single e θ

/-- The zero-deficiency criterion stated directly for `Pi.single` rows. -/
theorem finiteDeficiency_pi_single_eq_zero_iff [Nonempty Θ] [DecidableEq X] [DecidableEq Y]
    (e : Θ → X) (f : Θ → Y) :
    finiteDeficiency (fun θ => (Pi.single (e θ) 1 : X → ℝ))
        (fun θ => (Pi.single (f θ) 1 : Y → ℝ)) = 0 ↔
      ∀ θ θ', e θ = e θ' → f θ = f θ' := by
  rw [← diracExp_eq_pi_single_fun e, ← diracExp_eq_pi_single_fun f]
  exact finiteDeficiency_diracExp_eq_zero_iff e f

/-- The merging lower bound stated directly for `Pi.single` rows. -/
theorem half_le_finiteDeficiency_pi_single_of_merge [Nonempty Θ] [DecidableEq X] [DecidableEq Y]
    {e : Θ → X} {f : Θ → Y} (hmerge : ∃ θ θ', e θ = e θ' ∧ f θ ≠ f θ') :
    1 / 2 ≤ finiteDeficiency (fun θ => (Pi.single (e θ) 1 : X → ℝ))
      (fun θ => (Pi.single (f θ) 1 : Y → ℝ)) := by
  rw [← diracExp_eq_pi_single_fun e, ← diracExp_eq_pi_single_fun f]
  exact half_le_finiteDeficiency_diracExp_of_merge hmerge

end Dirac

/-! ## The exact Dirac deficiency: `1 - 1/k` for a `k`-way merge -/

section ExactValue

variable {Θ X Y : Type*} [Fintype Θ] [Nonempty Θ] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

/-- The target signals of the worlds whose source signal is `x`. -/
def mergeTargets (e : Θ → X) (f : Θ → Y) (x : X) : Finset Y :=
  (Finset.univ.filter fun θ => e θ = x).image f

theorem mem_mergeTargets (e : Θ → X) (f : Θ → Y) (x : X) (y : Y) :
    y ∈ mergeTargets e f x ↔ ∃ θ, e θ = x ∧ f θ = y := by
  simp [mergeTargets]

theorem mem_mergeTargets_self (e : Θ → X) (f : Θ → Y) (θ : Θ) :
    f θ ∈ mergeTargets e f (e θ) :=
  (mem_mergeTargets e f (e θ) (f θ)).2 ⟨θ, rfl, rfl⟩

/-- The number of distinct target signals merged under source signal `x`. -/
def mergeCount (e : Θ → X) (f : Θ → Y) (x : X) : ℕ :=
  (mergeTargets e f x).card

theorem mergeCount_pos (e : Θ → X) (f : Θ → Y) (θ : Θ) :
    0 < mergeCount e f (e θ) :=
  Finset.card_pos.2 ⟨f θ, mem_mergeTargets_self e f θ⟩

/-- The paper's exact value: the worst world's `1 - 1/k`, where `k` is the
number of target signals merged at that world's source signal. -/
noncomputable def diracDeficiencyValue (e : Θ → X) (f : Θ → Y) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun θ => 1 - 1 / (mergeCount e f (e θ) : ℝ))

theorem le_diracDeficiencyValue (e : Θ → X) (f : Θ → Y) (θ : Θ) :
    1 - 1 / (mergeCount e f (e θ) : ℝ) ≤ diracDeficiencyValue e f :=
  Finset.le_sup' (fun θ => 1 - 1 / (mergeCount e f (e θ) : ℝ)) (Finset.mem_univ θ)

/-- The uniform merge decoder: on a source signal produced by some world,
spread mass uniformly over the merged target signals; elsewhere, decode to
an arbitrary fixed target. -/
noncomputable def uniformMergeDecoder (e : Θ → X) (f : Θ → Y) : X → Y → ℝ := by
  classical
  exact fun x y =>
    if (mergeTargets e f x).Nonempty then
      (if y ∈ mergeTargets e f x then 1 / (mergeCount e f x : ℝ) else 0)
    else if y = f (Classical.arbitrary Θ) then 1 else 0

theorem uniformMergeDecoder_mem_stochasticRules (e : Θ → X) (f : Θ → Y) :
    uniformMergeDecoder e f ∈ stochasticRules X Y := by
  classical
  intro x _
  constructor
  · intro y
    unfold uniformMergeDecoder
    split_ifs <;> positivity
  · unfold uniformMergeDecoder
    by_cases hne : (mergeTargets e f x).Nonempty
    · simp only [if_pos hne]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      have hk : (mergeCount e f x : ℝ) ≠ 0 := by
        unfold mergeCount
        exact_mod_cast (Finset.card_ne_zero.2 hne)
      unfold mergeCount
      unfold mergeCount at hk
      field_simp
    · simp only [if_neg hne]
      simp

theorem uniformMergeDecoder_apply_self (e : Θ → X) (f : Θ → Y) (θ : Θ) :
    uniformMergeDecoder e f (e θ) (f θ) = 1 / (mergeCount e f (e θ) : ℝ) := by
  classical
  have hne : (mergeTargets e f (e θ)).Nonempty := ⟨f θ, mem_mergeTargets_self e f θ⟩
  unfold uniformMergeDecoder
  rw [if_pos hne, if_pos (mem_mergeTargets_self e f θ)]

/-- Upper bound: the uniform merge decoder attains the exact value. -/
theorem finiteDeficiency_diracExp_le_diracDeficiencyValue (e : Θ → X) (f : Θ → Y) :
    finiteDeficiency (diracExp e) (diracExp f) ≤ diracDeficiencyValue e f := by
  apply finiteDeficiency_le_of_decoder (diracExp e) (diracExp f)
    (uniformMergeDecoder e f) (uniformMergeDecoder_mem_stochasticRules e f)
  intro θ
  rw [decodeErr_diracExp e f (uniformMergeDecoder_mem_stochasticRules e f) θ,
    uniformMergeDecoder_apply_self]
  exact le_diracDeficiencyValue e f θ

/-- Lower bound: any stochastic row puts mass at most `1/k` on some one of
`k` merged targets, so some merged world sees error at least `1 - 1/k`. -/
theorem diracDeficiencyValue_le_of_decoder (e : Θ → X) (f : Θ → Y)
    {G : X → Y → ℝ} (hG : G ∈ stochasticRules X Y) {c : ℝ}
    (herr : ∀ θ, decodeErr (diracExp e) (diracExp f) G θ ≤ c) :
    diracDeficiencyValue e f ≤ c := by
  classical
  apply Finset.sup'_le
  intro θ _
  have hne : (mergeTargets e f (e θ)).Nonempty := ⟨f θ, mem_mergeTargets_self e f θ⟩
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (mergeTargets e f (e θ)) (G (e θ)) hne
  obtain ⟨θ', hθ'e, hθ'f⟩ := (mem_mergeTargets e f (e θ) y).1 hy
  have hrow := hG (e θ) (Set.mem_univ (e θ))
  have hkpos : (0 : ℝ) < (mergeCount e f (e θ) : ℝ) := by
    exact_mod_cast mergeCount_pos e f θ
  have hsum : (mergeCount e f (e θ) : ℝ) * G (e θ) y ≤ 1 := by
    calc
      (mergeCount e f (e θ) : ℝ) * G (e θ) y =
          ∑ _z ∈ mergeTargets e f (e θ), G (e θ) y := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rfl
      _ ≤ ∑ z ∈ mergeTargets e f (e θ), G (e θ) z :=
        Finset.sum_le_sum fun z hz => hmin z hz
      _ ≤ ∑ z, G (e θ) z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun z _ _ => hrow.1 z)
      _ = 1 := hrow.2
  have hGy : G (e θ) y ≤ 1 / (mergeCount e f (e θ) : ℝ) := by
    rw [le_div_iff₀ hkpos]
    linarith
  have herr' := herr θ'
  rw [decodeErr_diracExp e f hG θ', hθ'e, hθ'f] at herr'
  linarith

/-- **Exact Dirac deficiency.**  Between Dirac experiments on a finite class,
the directed deficiency is exactly `max_θ (1 - 1/k(θ))`, where `k(θ)` is the
number of distinct target signals among the worlds sharing world `θ`'s
source signal. -/
theorem finiteDeficiency_diracExp_eq_diracDeficiencyValue (e : Θ → X) (f : Θ → Y) :
    finiteDeficiency (diracExp e) (diracExp f) = diracDeficiencyValue e f := by
  have : Nonempty Y := ⟨f (Classical.arbitrary Θ)⟩
  apply le_antisymm (finiteDeficiency_diracExp_le_diracDeficiencyValue e f)
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
    (diracExp_valid e) (diracExp_valid f))
  rintro c ⟨G, hG, herr⟩
  exact diracDeficiencyValue_le_of_decoder e f hG herr

/-- Between Dirac experiments on a finite class the deficiency is strictly
below one: each world's own target signal always receives mass `1/k > 0`. -/
theorem finiteDeficiency_diracExp_lt_one (e : Θ → X) (f : Θ → Y) :
    finiteDeficiency (diracExp e) (diracExp f) < 1 := by
  rw [finiteDeficiency_diracExp_eq_diracDeficiencyValue]
  unfold diracDeficiencyValue
  rw [Finset.sup'_lt_iff]
  intro θ _
  have hkpos : (0 : ℝ) < (mergeCount e f (e θ) : ℝ) := by
    exact_mod_cast mergeCount_pos e f θ
  have : 0 < 1 / (mergeCount e f (e θ) : ℝ) := by positivity
  linarith

/-- A `k`-way merge at some source signal, with `k ≥ 2`, forces deficiency at
least `1 - 1/k`; this sharpens the one-half bound. -/
theorem sub_one_div_le_finiteDeficiency_diracExp (e : Θ → X) (f : Θ → Y) (θ : Θ) :
    1 - 1 / (mergeCount e f (e θ) : ℝ) ≤ finiteDeficiency (diracExp e) (diracExp f) := by
  rw [finiteDeficiency_diracExp_eq_diracDeficiencyValue]
  exact le_diracDeficiencyValue e f θ

end ExactValue

/-! ## Deterministic causal kernels and policies -/

section Causal

variable {A O Θ : Type*} [Fintype A] [Fintype O]


/-- The bundled valid deterministic policy. -/
noncomputable def validDetPolicy (p : CausalHistory A O → A) : ValidCausalPolicy A O :=
  ⟨detPolicy p, isCausalPolicy_detPolicy p⟩

/-! ## The unique trace of a deterministic policy in a deterministic world -/

/-- The length-`n` action--observation history produced by policy `p` in
world `g`, in chronological order. -/
def detTraceList (p : CausalHistory A O → A) (g : CausalHistory A O → A → O) :
    ℕ → CausalHistory A O
  | 0 => []
  | n + 1 =>
      detTraceList p g n ++
        [(p (detTraceList p g n), g (detTraceList p g n) (p (detTraceList p g n)))]

@[simp]
theorem detTraceList_zero (p : CausalHistory A O → A) (g : CausalHistory A O → A → O) :
    detTraceList p g 0 = [] := rfl

theorem detTraceList_succ (p : CausalHistory A O → A) (g : CausalHistory A O → A → O)
    (n : ℕ) :
    detTraceList p g (n + 1) =
      detTraceList p g n ++
        [(p (detTraceList p g n), g (detTraceList p g n) (p (detTraceList p g n)))] := rfl

@[simp]
theorem detTraceList_length (p : CausalHistory A O → A) (g : CausalHistory A O → A → O)
    (n : ℕ) : (detTraceList p g n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [detTraceList_succ, ih]

/-- Every deterministic trace is a prefix of every later one. -/
theorem detTraceList_take (p : CausalHistory A O → A) (g : CausalHistory A O → A → O)
    {s t : ℕ} (hst : s ≤ t) :
    (detTraceList p g t).take s = detTraceList p g s := by
  induction t with
  | zero =>
      have hs : s = 0 := Nat.le_zero.mp hst
      subst hs
      rfl
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with h | h
      · have hs : s ≤ t := Nat.lt_succ_iff.mp h
        rw [detTraceList_succ,
          List.take_append_of_le_length (by rw [detTraceList_length]; exact hs), ih hs]
      · have hs : s = t + 1 := le_antisymm hst h
        subst hs
        exact List.take_of_length_le (by rw [detTraceList_length])

/-- Equal traces at a later time force equal traces at every earlier time. -/
theorem detTraceList_eq_of_le (p : CausalHistory A O → A)
    {g g' : CausalHistory A O → A → O} {s t : ℕ} (hst : s ≤ t)
    (h : detTraceList p g t = detTraceList p g' t) :
    detTraceList p g s = detTraceList p g' s := by
  rw [← detTraceList_take p g hst, ← detTraceList_take p g' hst, h]

/-- Under a deterministic policy and a deterministic world, exactly one
history of each length has positive probability, and it has probability one. -/
theorem causalTraceProb_det [DecidableEq A] [DecidableEq O]
    (p : CausalHistory A O → A) (g : CausalHistory A O → A → O)
    (h : CausalHistory A O) :
    causalTraceProb (detPolicy p) (detResponse g) h =
      if h = detTraceList p g h.length then 1 else 0 := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [causalTraceProb, causalTraceProbFrom]
  | append_singleton l ao ih =>
      rw [causalTraceProb_append_singleton, ih]
      rw [List.length_append, List.length_singleton, detTraceList_succ]
      by_cases hl : l = detTraceList p g l.length
      · rw [if_pos hl]
        by_cases hao : ao = (p l, g l (p l))
        · subst hao
          rw [if_pos (by rw [← hl]), detPolicy_self, detResponse_self]
          norm_num
        · have hne : l ++ [ao] ≠
              detTraceList p g l.length ++
                [(p (detTraceList p g l.length),
                  g (detTraceList p g l.length) (p (detTraceList p g l.length)))] := by
            intro heq
            rw [← hl] at heq
            exact hao (List.singleton_inj.1 (List.append_cancel_left heq))
          rw [if_neg hne]
          by_cases ha : ao.1 = p l
          · have ho : ao.2 ≠ g l ao.1 := by
              intro ho
              apply hao
              exact Prod.ext ha (by rw [ho, ha])
            rw [detResponse_of_ne g l ao.1 ho]
            ring
          · rw [detPolicy_of_ne p l ha]
            ring
      · rw [if_neg hl, if_neg]
        · ring
        · intro heq
          exact hl (List.append_inj_left' heq rfl)

/-- The length-`n` trace as a finite signal, so that it can index a Dirac
finite experiment. -/
noncomputable def detTraceFin (p : CausalHistory A O → A) (g : CausalHistory A O → A → O)
    (n : ℕ) : CausalFiniteTrace A O n :=
  fun k => (detTraceList p g n).get (Fin.cast (detTraceList_length p g n).symm k)

theorem ofFn_detTraceFin (p : CausalHistory A O → A) (g : CausalHistory A O → A → O)
    (n : ℕ) : List.ofFn (detTraceFin p g n) = detTraceList p g n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [detTraceFin]

theorem detTraceFin_eq_iff (p : CausalHistory A O → A)
    (g g' : CausalHistory A O → A → O) (n : ℕ) :
    detTraceFin p g n = detTraceFin p g' n ↔ detTraceList p g n = detTraceList p g' n := by
  rw [← List.ofFn_inj, ofFn_detTraceFin, ofFn_detTraceFin]

/-- **Deterministic acquisition is Dirac.**  A deterministic policy on a
family of deterministic worlds acquires, at horizon `n`, the Dirac experiment
at the length-`n` trace map. -/
theorem causalFiniteExperiment_det (p : CausalHistory A O → A)
    (g : Θ → CausalHistory A O → A → O) (n : ℕ) :
    causalFiniteExperiment (detPolicy p) (fun θ => detResponse (g θ)) n =
      diracExp (fun θ => detTraceFin p (g θ) n) := by
  classical
  funext θ w
  unfold causalFiniteExperiment
  rw [causalTraceProb_det, List.length_ofFn]
  by_cases hw : w = detTraceFin p (g θ) n
  · rw [hw, diracExp_self, if_pos (ofFn_detTraceFin p (g θ) n)]
  · rw [diracExp_of_ne _ _ hw, if_neg]
    intro h
    apply hw
    rw [← ofFn_detTraceFin p (g θ) n] at h
    exact List.ofFn_injective h


/-! ## Deterministic native tests are Dirac -/

/-- The action map of the deterministic policy realizing a depth-`n` plan. -/
noncomputable def planAction [Nonempty A] (n : ℕ) (τ : CausalPlan A O n)
    (h : CausalHistory A O) : A :=
  if hh : h.length < n then τ (causalDecisionPointOfHistory n h hh)
  else Classical.choice inferInstance

/-- `causalPolicyOfPlan` is literally the deterministic policy of `planAction`. -/
theorem causalPolicyOfPlan_eq_detPolicy [Nonempty A] (n : ℕ) (τ : CausalPlan A O n) :
    causalPolicyOfPlan n τ = detPolicy (planAction n τ) := by
  classical
  funext h a
  by_cases hh : h.length < n
  · by_cases ha : a = τ (causalDecisionPointOfHistory n h hh)
    · have ha' : a = planAction n τ h := by simp [planAction, hh, ha]
      rw [ha', detPolicy_self]
      simp [causalPolicyOfPlan, planAction, hh]
    · have ha' : a ≠ planAction n τ h := by simp [planAction, hh, ha]
      rw [detPolicy_of_ne _ _ ha']
      simp [causalPolicyOfPlan, hh, ha]
  · by_cases ha : a = Classical.choice (inferInstance : Nonempty A)
    · have ha' : a = planAction n τ h := by simp [planAction, hh, ha]
      rw [ha', detPolicy_self]
      simp [causalPolicyOfPlan, planAction, hh]
    · have ha' : a ≠ planAction n τ h := by simp [planAction, hh, ha]
      rw [detPolicy_of_ne _ _ ha']
      simp [causalPolicyOfPlan, hh, ha]

/-- The observation word produced by the deterministic plan `τ` in the
deterministic world `g`. -/
noncomputable def detPlanObs [Nonempty A] (n : ℕ) (τ : CausalPlan A O n)
    (g : CausalHistory A O → A → O) : CausalObservationTrace O n :=
  causalTraceObservations (detTraceFin (planAction n τ) g n)

/-- **Deterministic native tests are Dirac.**  On a family of deterministic
worlds, the observation experiment of a deterministic plan is the Dirac
experiment at its observation-word map. -/
theorem causalPlanObservationExperiment_det [Nonempty A] (n : ℕ) (τ : CausalPlan A O n)
    (g : Θ → CausalHistory A O → A → O) :
    causalPlanObservationExperiment n τ (fun θ => detResponse (g θ)) =
      diracExp (fun θ => detPlanObs n τ (g θ)) := by
  classical
  funext θ o
  unfold causalPlanObservationExperiment
  rw [causalPolicyOfPlan_eq_detPolicy, causalFiniteExperiment_det,
    congrFun (finiteDecisionLaw_diracExp _ _ θ) o]
  by_cases ho : o = detPlanObs n τ (g θ)
  · rw [ho, diracExp_self]
    simp [causalForgetActionsRule, detPlanObs]
  · rw [diracExp_of_ne (fun θ => detPlanObs n τ (g θ)) θ ho]
    have ho' : causalTraceObservations (detTraceFin (planAction n τ) (g θ) n) ≠ o :=
      fun h => ho h.symm
    simp [causalForgetActionsRule, ho']

/-! ## Native deficiency of a deterministic acquisition -/

variable [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- The depth-`n` native deficiency vanishes exactly when every depth-`n`
deterministic test is simulated exactly. -/
theorem causalNativeDeficiency_eq_zero_iff_forall {X : Type*} [Fintype X]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    causalNativeDeficiency E Qs n = 0 ↔
      ∀ τ : CausalPlan A O n,
        finiteDeficiency E (causalPlanObservationExperiment n τ Qs) = 0 := by
  constructor
  · intro h τ
    apply le_antisymm
    · rw [← h]
      exact finiteDeficiency_causalPlan_le_native E Qs n τ
    · exact finiteDeficiency_nonneg_of_valid _ _ hE
        (causalPlanObservationExperiment_valid n τ Qs hQ)
  · intro h
    obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency E Qs n
    rw [hτ, h τ]

/-- **Deterministic native deficiency criterion.**  For a deterministic
policy on a family of deterministic worlds, the depth-`n` native deficiency
of the acquired depth-`t` experiment vanishes exactly when worlds with equal
length-`t` traces have equal depth-`n` plan experiments. -/
theorem det_causalNativeDeficiency_eq_zero_iff (p : CausalHistory A O → A)
    (g : Θ → CausalHistory A O → A → O) (t n : ℕ) :
    causalNativeDeficiency
        (causalFiniteExperiment (detPolicy p) (fun θ => detResponse (g θ)) t)
        (fun θ => detResponse (g θ)) n = 0 ↔
      ∀ θ θ', detTraceList p (g θ) t = detTraceList p (g θ') t →
        ∀ τ : CausalPlan A O n,
          causalPlanObservationExperiment n τ (fun θ => detResponse (g θ)) θ =
            causalPlanObservationExperiment n τ (fun θ => detResponse (g θ)) θ' := by
  rw [causalNativeDeficiency_eq_zero_iff_forall _
    (causalFiniteExperiment_valid _ (isCausalPolicy_detPolicy p) _
      (fun θ => isCausalResponse_detResponse (g θ)) t)
    _ (fun θ => isCausalResponse_detResponse (g θ)) n]
  simp_rw [causalPlanObservationExperiment_det, causalFiniteExperiment_det,
    finiteDeficiency_diracExp_eq_zero_iff, diracExp_row_eq_iff]
  unfold SeparatesFor
  simp_rw [detTraceFin_eq_iff]
  exact ⟨fun h θ θ' he τ => h τ θ θ' he, fun h τ θ θ' he => h θ θ' he τ⟩

/-- **Deterministic native dichotomy.**  The depth-`n` native deficiency of
a deterministic acquisition is either zero or at least one half. -/
theorem det_causalNativeDeficiency_dichotomy (p : CausalHistory A O → A)
    (g : Θ → CausalHistory A O → A → O) (t n : ℕ) :
    causalNativeDeficiency
        (causalFiniteExperiment (detPolicy p) (fun θ => detResponse (g θ)) t)
        (fun θ => detResponse (g θ)) n = 0 ∨
      1 / 2 ≤ causalNativeDeficiency
        (causalFiniteExperiment (detPolicy p) (fun θ => detResponse (g θ)) t)
        (fun θ => detResponse (g θ)) n := by
  by_cases h : causalNativeDeficiency
      (causalFiniteExperiment (detPolicy p) (fun θ => detResponse (g θ)) t)
      (fun θ => detResponse (g θ)) n = 0
  · exact Or.inl h
  · right
    rw [causalNativeDeficiency_eq_zero_iff_forall _
      (causalFiniteExperiment_valid _ (isCausalPolicy_detPolicy p) _
        (fun θ => isCausalResponse_detResponse (g θ)) t)
      _ (fun θ => isCausalResponse_detResponse (g θ)) n] at h
    push Not at h
    obtain ⟨τ, hτ⟩ := h
    refine le_trans ?_ (finiteDeficiency_causalPlan_le_native _ _ n τ)
    rw [causalPlanObservationExperiment_det, causalFiniteExperiment_det] at hτ ⊢
    rcases finiteDeficiency_dirac_dichotomy
      (fun θ => detTraceFin p (g θ) t) (fun θ => detPlanObs n τ (g θ)) with h0 | hh
    · exact absurd h0 hτ
    · exact hh

end Causal

/-! ## Controlled-trace equivalence through deterministic plans -/

section BehEq

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A]

/-- Controlled-trace equivalent worlds give the same row of every policy
experiment. -/
theorem causalFiniteExperiment_row_eq_of_behEq (π : CausalPolicy A O)
    {Qs : Θ → CausalResponse A O} {θ θ' : Θ}
    (h : CausalBehEq (Qs θ) (Qs θ')) (n : ℕ) :
    causalFiniteExperiment π Qs n θ = causalFiniteExperiment π Qs n θ' := by
  funext w
  exact causalTraceProb_eq_of_causalBehEq π h (List.ofFn w)

/-- Controlled-trace equivalent worlds give the same row of every
deterministic-plan observation experiment. -/
theorem causalPlanObservationExperiment_row_eq_of_behEq
    {Qs : Θ → CausalResponse A O} {θ θ' : Θ}
    (h : CausalBehEq (Qs θ) (Qs θ')) (n : ℕ) (τ : CausalPlan A O n) :
    causalPlanObservationExperiment n τ Qs θ =
      causalPlanObservationExperiment n τ Qs θ' := by
  funext o
  unfold causalPlanObservationExperiment finiteDecisionLaw
  rw [causalFiniteExperiment_row_eq_of_behEq (causalPolicyOfPlan n τ) h n]

/-- The open-loop plan replaying the action word of a trace agrees with that
trace. -/
theorem causalPlanAgreesTrace_targetAction {n : ℕ} (w : CausalFiniteTrace A O n) :
    CausalPlanAgreesTrace (causalTraceTargetAction w) w :=
  fun k => causalTraceTargetAction_decisionPoint w k

/-- Worlds whose deterministic-plan observation experiments agree at every
depth are controlled-trace equivalent: replaying the action word of any
history as an open-loop plan recovers that history's controlled likelihood.
No determinism of the kernels is needed. -/
theorem causalBehEq_of_forall_plan_experiment_eq
    {Qs : Θ → CausalResponse A O} {θ θ' : Θ}
    (h : ∀ n (τ : CausalPlan A O n),
      causalPlanObservationExperiment n τ Qs θ =
        causalPlanObservationExperiment n τ Qs θ') :
    CausalBehEq (Qs θ) (Qs θ') := by
  intro hist
  let w : CausalFiniteTrace A O hist.length := hist.get
  have hw : List.ofFn w = hist := List.ofFn_get hist
  let τ : CausalPlan A O hist.length := causalTraceTargetAction w
  have hfull :
      causalFiniteExperiment (causalPolicyOfPlan hist.length τ) Qs hist.length θ =
        causalFiniteExperiment (causalPolicyOfPlan hist.length τ) Qs hist.length θ' := by
    rw [← causalPlanObservationExperiment_attach hist.length τ Qs]
    unfold finiteDecisionLaw
    rw [h hist.length τ]
  have hw' := congrFun hfull w
  unfold causalFiniteExperiment at hw'
  rw [causalTraceProb_factor, causalTraceProb_factor,
    causalPolicyProb_plan_eq_indicator] at hw'
  have hone : causalPlanTraceIndicator τ w = 1 := by
    unfold causalPlanTraceIndicator
    exact if_pos (causalPlanAgreesTrace_targetAction w)
  rw [hone, one_mul, one_mul, hw] at hw'
  exact hw'

/-- **Plan experiments determine the controlled-trace class.**  Two worlds
are controlled-trace equivalent exactly when every deterministic plan at
every depth induces the same observation experiment row in both. -/
theorem causalBehEq_iff_forall_plan_experiment_eq
    (Qs : Θ → CausalResponse A O) (θ θ' : Θ) :
    CausalBehEq (Qs θ) (Qs θ') ↔
      ∀ n (τ : CausalPlan A O n),
        causalPlanObservationExperiment n τ Qs θ =
          causalPlanObservationExperiment n τ Qs θ' :=
  ⟨fun h n τ => causalPlanObservationExperiment_row_eq_of_behEq h n τ,
    causalBehEq_of_forall_plan_experiment_eq⟩

end BehEq

/-! ## The deterministic trace-separation theorem -/

section Main

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- The deterministic acquisition at depth `t` on the world family `g`. -/
noncomputable abbrev detAcquired (p : CausalHistory A O → A)
    (g : Θ → CausalHistory A O → A → O) (t : ℕ) :=
  causalFiniteExperiment (detPolicy p) (fun θ => detResponse (g θ)) t

/-- **All-depth zero native deficiency is trace separation.**  For a
deterministic policy on deterministic worlds, the acquired depth-`t`
experiment has zero native deficiency at every depth exactly when worlds
with equal length-`t` traces are controlled-trace equivalent. -/
theorem det_forall_nativeDeficiency_eq_zero_iff_traces_separate
    (p : CausalHistory A O → A) (g : Θ → CausalHistory A O → A → O) (t : ℕ) :
    (∀ n, causalNativeDeficiency (detAcquired p g t) (fun θ => detResponse (g θ)) n = 0) ↔
      ∀ θ θ', detTraceList p (g θ) t = detTraceList p (g θ') t →
        CausalBehEq (detResponse (g θ)) (detResponse (g θ')) := by
  simp_rw [det_causalNativeDeficiency_eq_zero_iff,
    causalBehEq_iff_forall_plan_experiment_eq (fun θ => detResponse (g θ))]
  exact ⟨fun h θ θ' he n τ => h n θ θ' he τ, fun h n θ θ' he τ => h θ θ' he n τ⟩

/-- Zero native deficiency at every depth from one finite time already gives
native sufficiency, for any valid policy and any valid world family: later
prefixes only decrease deficiency to each fixed test. -/
theorem causalNativelySufficient_of_exists_nativeDeficiency_eq_zero
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O)
    (h : ∃ t, ∀ n, causalNativeDeficiency (causalFiniteExperiment π.1 Qs t) Qs n = 0) :
    CausalNativelySufficient Qs π := by
  obtain ⟨t₀, ht₀⟩ := h
  intro n ε hε
  refine ⟨t₀, fun t ht τ => ?_⟩
  have hanti := causalPolicyTestDeficiency_antitone π Qs hQ ⟨n, τ⟩ ht
  unfold causalPolicyTestDeficiency causalNativeTestExperiment at hanti
  refine lt_of_le_of_lt (hanti.trans ?_) hε
  rw [← ht₀ n]
  exact finiteDeficiency_causalPlan_le_native _ _ n τ

/-- **Deterministic trace-separation theorem, sufficiency form.**  On a
finite class of deterministic worlds, a deterministic policy is natively
sufficient exactly when, for some finite time `t`, its length-`t` trace map
separates every pair of worlds that is not controlled-trace equivalent. -/
theorem det_causalNativelySufficient_iff_traces_separate [Fintype Θ]
    (p : CausalHistory A O → A) (g : Θ → CausalHistory A O → A → O) :
    CausalNativelySufficient (fun θ => detResponse (g θ)) (validDetPolicy p) ↔
      ∃ t, ∀ θ θ', detTraceList p (g θ) t = detTraceList p (g θ') t →
        CausalBehEq (detResponse (g θ)) (detResponse (g θ')) := by
  constructor
  · intro hnat
    classical
    have hpair : ∀ q : Θ × Θ, ∃ T : ℕ,
        ¬ CausalBehEq (detResponse (g q.1)) (detResponse (g q.2)) →
          ∀ t, T ≤ t → detTraceList p (g q.1) t ≠ detTraceList p (g q.2) t := by
      intro q
      by_cases hbeh : CausalBehEq (detResponse (g q.1)) (detResponse (g q.2))
      · exact ⟨0, fun h => absurd hbeh h⟩
      · rw [causalBehEq_iff_forall_plan_experiment_eq (fun θ => detResponse (g θ))] at hbeh
        push Not at hbeh
        obtain ⟨n, τ, hτ⟩ := hbeh
        obtain ⟨T, hT⟩ := hnat n (1 / 2) (by norm_num)
        refine ⟨T, fun _ t ht heq => ?_⟩
        have hlt := hT t ht τ
        change finiteDeficiency
          (causalFiniteExperiment (detPolicy p) (fun θ => detResponse (g θ)) t)
          (causalPlanObservationExperiment n τ (fun θ => detResponse (g θ))) < 1 / 2 at hlt
        rw [causalPlanObservationExperiment_det, causalFiniteExperiment_det] at hlt
        rw [causalPlanObservationExperiment_det] at hτ
        have h0 := finiteDeficiency_diracExp_eq_zero_of_lt_half hlt
        rw [finiteDeficiency_diracExp_eq_zero_iff] at h0
        apply hτ
        rw [diracExp_row_eq_iff]
        exact h0 _ _ ((detTraceFin_eq_iff p _ _ t).2 heq)
    choose T hT using hpair
    refine ⟨Finset.univ.sup T, fun θ θ' heq => ?_⟩
    by_contra hbeh
    exact hT (θ, θ') hbeh _ (Finset.le_sup (Finset.mem_univ (θ, θ'))) heq
  · rintro ⟨t₀, ht₀⟩
    apply causalNativelySufficient_of_exists_nativeDeficiency_eq_zero _
      (fun θ => isCausalResponse_detResponse (g θ))
    refine ⟨t₀, ?_⟩
    exact (det_forall_nativeDeficiency_eq_zero_iff_traces_separate p g t₀).2 ht₀

/-- **Deterministic trace-separation theorem, attained-zero form.**  On a
finite class of deterministic worlds, a deterministic policy is natively
sufficient exactly when the zero native profile is attained at some finite
time: approaching zero in the limit and attaining it at a finite horizon
coincide. -/
theorem det_causalNativelySufficient_iff_exists_nativeDeficiency_eq_zero [Fintype Θ]
    (p : CausalHistory A O → A) (g : Θ → CausalHistory A O → A → O) :
    CausalNativelySufficient (fun θ => detResponse (g θ)) (validDetPolicy p) ↔
      ∃ t, ∀ n, causalNativeDeficiency (detAcquired p g t)
        (fun θ => detResponse (g θ)) n = 0 := by
  rw [det_causalNativelySufficient_iff_traces_separate]
  simp_rw [det_forall_nativeDeficiency_eq_zero_iff_traces_separate]

/-- On a finite deterministic class the native deficiency of a deterministic
acquisition is strictly below one, so together with the dichotomy it lies in
`{0} ∪ [1/2, 1)`. -/
theorem det_causalNativeDeficiency_lt_one [Fintype Θ]
    (p : CausalHistory A O → A) (g : Θ → CausalHistory A O → A → O) (t n : ℕ) :
    causalNativeDeficiency (detAcquired p g t) (fun θ => detResponse (g θ)) n < 1 := by
  classical
  obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency
    (detAcquired p g t) (fun θ => detResponse (g θ)) n
  rw [hτ, causalPlanObservationExperiment_det]
  unfold detAcquired
  rw [causalFiniteExperiment_det]
  exact finiteDeficiency_diracExp_lt_one _ _

/-- The profile of a deterministic policy on a finite deterministic class is
the zero profile exactly when its trace map separates the class at some finite
time. -/
theorem det_causalPolicyProfile_eq_zeroProfile_iff [Fintype Θ]
    (p : CausalHistory A O → A) (g : Θ → CausalHistory A O → A → O)
    (e : ℕ ≃ CausalNativeTest A O) :
    causalPolicyProfile (fun θ => detResponse (g θ))
        (fun θ => isCausalResponse_detResponse (g θ)) e (validDetPolicy p) = zeroProfile ↔
      ∃ t, ∀ θ θ', detTraceList p (g θ) t = detTraceList p (g θ') t →
        CausalBehEq (detResponse (g θ)) (detResponse (g θ')) := by
  rw [causalPolicyProfile_eq_zeroProfile_iff_nativelySufficient,
    det_causalNativelySufficient_iff_traces_separate]

end Main

end IdExp
