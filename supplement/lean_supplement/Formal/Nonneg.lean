/-
Nonnegativity and range lemmas for the objects of `Formal.Basic`.

These are the "stochasticity consequences" that `STATEMENTS.md` (choice C5)
notes are not baked into the definitions: under `POMDP.Valid` and `IsPolicy`,
forward weights, trace likelihoods, policy weights and trace probabilities are
nonnegative, posteriors lie in `[0, 1]`, and entropies are nonnegative.  They
are the plumbing behind the first proved statement, `infoInf_le_ent`.
-/
import Formal.Basic

-- `Basic`'s definitions captured `[Fintype A]`/`[Fintype O]` unevenly from its
-- `variable` block; the linter's per-theorem `omit` churn is not worth it here.
set_option linter.unusedSectionVars false

namespace IdExp

open Finset

variable {A O : Type*} [Fintype A] [Fintype O]

theorem stepLik_nonneg (M : POMDP A O) (hM : M.Valid) {f : M.S → ℝ}
    (hf : ∀ s, 0 ≤ f s) (ao : A × O) (s' : M.S) : 0 ≤ stepLik M f ao s' := by
  unfold stepLik
  exact mul_nonneg
    (Finset.sum_nonneg fun s _ => mul_nonneg (hf s) (hM.2.2.1 ao.1 s s'))
    (hM.2.2.2.2.1 s' ao.2)

theorem foldl_stepLik_nonneg (M : POMDP A O) (hM : M.Valid) :
    ∀ (steps : List (A × O)) (f : M.S → ℝ), (∀ s, 0 ≤ f s) →
      ∀ s, 0 ≤ steps.foldl (stepLik M) f s
  | [], _, hf => hf
  | ao :: rest, f, hf =>
      foldl_stepLik_nonneg M hM rest (stepLik M f ao)
        (fun s' => stepLik_nonneg M hM hf ao s')

theorem fwd_nonneg (M : POMDP A O) (hM : M.Valid) (o₀ : O)
    (steps : List (A × O)) (s : M.S) : 0 ≤ fwd M o₀ steps s :=
  foldl_stepLik_nonneg M hM steps _
    (fun s => mul_nonneg (hM.1 s) (hM.2.2.2.2.1 s o₀)) s

theorem traceLik_nonneg (M : POMDP A O) (hM : M.Valid) (h : Hist A O) :
    0 ≤ traceLik M h :=
  Finset.sum_nonneg fun s _ => fwd_nonneg M hM h.1 h.2 s

theorem polWeightAux_nonneg (π : Policy A O) (hπ : IsPolicy π) (o₀ : O) :
    ∀ (rest pre : List (A × O)), 0 ≤ polWeightAux π o₀ pre rest
  | [], _ => by
      unfold polWeightAux
      exact zero_le_one
  | ao :: rest, pre => by
      unfold polWeightAux
      exact mul_nonneg ((hπ (o₀, pre)).1 ao.1)
        (polWeightAux_nonneg π hπ o₀ rest (pre ++ [ao]))

/-- Appending one step multiplies the policy weight by the policy's probability of
the appended action at the extended history. -/
theorem polWeightAux_append (π : Policy A O) (o₀ : O) :
    ∀ (rest pre : List (A × O)) (ao : A × O),
      polWeightAux π o₀ pre (rest ++ [ao]) =
        polWeightAux π o₀ pre rest * π (o₀, pre ++ rest) ao.1
  | [], pre, ao => by
      simp [polWeightAux]
  | bo :: rest, pre, ao => by
      simp only [List.cons_append, polWeightAux]
      rw [polWeightAux_append π o₀ rest (pre ++ [bo]) ao, List.append_assoc,
        List.singleton_append, mul_assoc]

theorem polWeight_append (π : Policy A O) (h : Hist A O) (ao : A × O) :
    polWeight π (h.1, h.2 ++ [ao]) = polWeight π h * π h ao.1 := by
  unfold polWeight
  rw [polWeightAux_append]
  simp

theorem polWeight_nonneg (π : Policy A O) (hπ : IsPolicy π) (h : Hist A O) :
    0 ≤ polWeight π h :=
  polWeightAux_nonneg π hπ h.1 h.2 []

theorem traceProb_nonneg (π : Policy A O) (hπ : IsPolicy π) (M : POMDP A O)
    (hM : M.Valid) (h : Hist A O) : 0 ≤ traceProb π M h :=
  mul_nonneg (polWeight_nonneg π hπ h) (traceLik_nonneg M hM h)

/-! ### Consistency of the trace likelihoods

Summing the trace likelihood over the next observation returns the trace
likelihood of the shorter history: the finite-dimensional laws form a
projective family, which is what the Ionescu–Tulcea construction of
`pathLaw_exists` will need (`STATEMENTS.md` C2). -/

theorem fwd_append_single (M : POMDP A O) (o₀ : O) (steps : List (A × O))
    (ao : A × O) : fwd M o₀ (steps ++ [ao]) = stepLik M (fwd M o₀ steps) ao := by
  unfold fwd
  rw [List.foldl_append]
  rfl

theorem sum_traceLik_append (M : POMDP A O) (hM : M.Valid) (o₀ : O)
    (steps : List (A × O)) (a : A) :
    ∑ o' : O, traceLik M (o₀, steps ++ [(a, o')]) = traceLik M (o₀, steps) := by
  simp only [traceLik, fwd_append_single, stepLik]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [hM.2.2.2.2.2, mul_one]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [hM.2.2.2.1, mul_one]

/-- The conditional next-observation law after history `h` and action `a`:
the likelihood ratio, or the uniform law on histories of zero trace
likelihood (a null event under every policy; STATEMENTS.md C5). -/
noncomputable def nextObs (M : POMDP A O) (h : Hist A O) (a : A) (o' : O) : ℝ :=
  if traceLik M h = 0 then (1 : ℝ) / Fintype.card O
  else traceLik M (h.1, h.2 ++ [(a, o')]) / traceLik M h

theorem nextObs_nonneg (M : POMDP A O) (hM : M.Valid) (h : Hist A O) (a : A) (o' : O) :
    0 ≤ nextObs M h a o' := by
  unfold nextObs
  split_ifs
  · positivity
  · exact div_nonneg (traceLik_nonneg M hM _) (traceLik_nonneg M hM _)

/-- `nextObs` is a probability vector on `O` (this is where projectivity is used). -/
theorem sum_nextObs [Nonempty O] (M : POMDP A O) (hM : M.Valid) (h : Hist A O) (a : A) :
    ∑ o' : O, nextObs M h a o' = 1 := by
  unfold nextObs
  by_cases h0 : traceLik M h = 0
  · simp only [h0, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card O : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [h0, if_false]
    rw [← Finset.sum_div]
    have := sum_traceLik_append M hM h.1 h.2 a
    rw [this]
    exact div_self h0

theorem isDist_nextObs [Nonempty O] (M : POMDP A O) (hM : M.Valid) (h : Hist A O) (a : A) :
    IsDist (nextObs M h a) :=
  ⟨nextObs_nonneg M hM h a, sum_nextObs M hM h a⟩

/-- One-step telescoping of the finite-horizon trace probability: extending a
history multiplies its probability by the policy's action probability and the
conditional next-observation law.  (On zero-likelihood histories both sides
vanish, since `traceLik (h ++ [ao]) = 0` whenever `traceLik h = 0`.) -/
theorem traceLik_append_eq_zero (M : POMDP A O) (hM : M.Valid) (h : Hist A O)
    (ao : A × O) (h0 : traceLik M h = 0) : traceLik M (h.1, h.2 ++ [ao]) = 0 := by
  have hsum := sum_traceLik_append M hM h.1 h.2 ao.1
  rw [h0] at hsum
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun o' _ => traceLik_nonneg M hM (h.1, h.2 ++ [(ao.1, o')]))).1 hsum ao.2
    (Finset.mem_univ _)

theorem traceProb_append (π : Policy A O) (M : POMDP A O) (hM : M.Valid)
    (h : Hist A O) (a : A) (o' : O) :
    traceProb π M (h.1, h.2 ++ [(a, o')]) = traceProb π M h * π h a * nextObs M h a o' := by
  unfold traceProb
  rw [polWeight_append]
  by_cases h0 : traceLik M h = 0
  · rw [traceLik_append_eq_zero M hM h (a, o') h0, h0]
    ring
  · unfold nextObs
    rw [if_neg h0]
    field_simp

variable {Θ : Type*} [Fintype Θ]

theorem posterior_nonneg (α : Θ → ℝ) (hα : IsDist α) (Ms : Θ → POMDP A O)
    (hV : ∀ θ, (Ms θ).Valid) (h : Hist A O) (θ : Θ) :
    0 ≤ posterior α Ms h θ := by
  unfold posterior
  exact div_nonneg (mul_nonneg (hα.1 θ) (traceLik_nonneg _ (hV θ) h))
    (Finset.sum_nonneg fun θ' _ =>
      mul_nonneg (hα.1 θ') (traceLik_nonneg _ (hV θ') h))

theorem posterior_le_one (α : Θ → ℝ) (hα : IsDist α) (Ms : Θ → POMDP A O)
    (hV : ∀ θ, (Ms θ).Valid) (h : Hist A O) (θ : Θ) :
    posterior α Ms h θ ≤ 1 := by
  unfold posterior
  apply div_le_one_of_le₀
  · exact Finset.single_le_sum
      (fun θ' _ => mul_nonneg (hα.1 θ') (traceLik_nonneg _ (hV θ') h))
      (Finset.mem_univ θ)
  · exact Finset.sum_nonneg fun θ' _ =>
      mul_nonneg (hα.1 θ') (traceLik_nonneg _ (hV θ') h)

/-- Shannon entropy of a vector with coordinates in `[0, 1]` is nonnegative. -/
theorem ent_nonneg_of_mem_Icc {C : Type*} [Fintype C] {p : C → ℝ}
    (h0 : ∀ c, 0 ≤ p c) (h1 : ∀ c, p c ≤ 1) : 0 ≤ ent p :=
  Finset.sum_nonneg fun c _ => Real.negMulLog_nonneg (h0 c) (h1 c)

theorem ent_posterior_nonneg (α : Θ → ℝ) (hα : IsDist α) (Ms : Θ → POMDP A O)
    (hV : ∀ θ, (Ms θ).Valid) (h : Hist A O) : 0 ≤ ent (posterior α Ms h) :=
  ent_nonneg_of_mem_Icc (posterior_nonneg α hα Ms hV h)
    (posterior_le_one α hα Ms hV h)

end IdExp
