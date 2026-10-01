import Formal.FiniteProbability

/-!
# The episodic coverage bound: the finite rejection-decoder core

**Paper context** (episodic-coverage deliverable, Aug 2026).  In an episodic
interface the experiment `E_N` hands the analyst the transcript of `N` i.i.d.
episodes collected by a behavior policy `π`.  For a fixed depth-`n` native test
`σ` the rejection decoder scans the transcript for the first episode whose
first `n` actions are `σ`-consistent (the *match* event, of `π`-probability
`p = p_σ`), outputs that episode's first `n` observations, and outputs a
fallback `o₀ ∈ O = 𝒪ⁿ` if no episode matches.  The per-episode splicing
identity says that conditional on a match the emitted observation string has
exactly the test law `T = T^σ(Q)` (uniform `π`, or the Bernoulli-thinned
decoder in general).  Hence the decoder's output law is the mixture
`(1 − (1−p)^N) · T + (1−p)^N · δ_{o₀}`, which is within total variation
`(1−p)^N` of `T`, uniformly over worlds `Q` — giving
`Γ_{≤n}(E_N) ≤ (1−p)^N` with `p = |A|^{−n}` for uniform `π`.

**What is formalized here** (everything below is proved, no axioms beyond
Mathlib's):

* the finite product model: an episode is summarized as a pair
  `(match?, outcome) : Bool × O`, a transcript is `x : Fin N → Bool × O`
  carrying the i.i.d. product weight `∏ i, epLaw p T R (x i)`, where the
  per-episode law `epLaw` matches with probability `p` and emits `T` on a
  match and an arbitrary law `R` otherwise (`R` is the marginal outcome law
  on non-matching episodes; the decoder never uses it);
* the rejection decoder `firstMatch` (first matching episode's outcome, else
  the fallback `o₀`) as an explicit function of the transcript;
* the **mixture identity** `outputLaw_eq_mixture`: the decoder's output law
  is exactly `(1 − (1−p)^N) · T + (1−p)^N · δ_{o₀}` — proved from the finite
  construction by induction on `N`, not taken as a definition;
* the **rejection-decoder inequality** `tvDist_outputLaw_le`:
  `TV(outputLaw, T) ≤ (1−p)^N` (with `TV = ½ Σ |·|` on finite laws);
* the limit `tendsto_tvDist_outputLaw`: for `0 < p ≤ 1` the decoding error
  tends to `0` as `N → ∞`;
* sanity: `isDist_outputLaw` — the output law is a probability vector.

**Formalization boundary:** `CausalSplicing.lean` now proves the actual
single-episode causal match identity and its exact conditional native law
under uniform behavior. Here that episode enters through `p` (match
probability) and `T` (conditional outcome law). The remaining paper-level
wrapper assembles independent reset episodes into a complete causal
multi-episode transcript and composes the summary decoder with this result.
Adaptive schedules are separate. The bound `(1−p)^N` is independent of
`T` and `R`, hence uniform over the world class.
-/

set_option linter.unusedSectionVars false

namespace IdExp
namespace CoverageBound

open Finset Filter
open scoped Topology

variable {O : Type*} [Fintype O] [DecidableEq O]

/-! ## The finite i.i.d. episode model -/

/-- Per-episode summary law on `Bool × O`: with probability `p` the episode
*matches* the test's action string and its outcome has the test law `T`; with
probability `1 − p` it does not match and its outcome has some other law `R`
(never used by the decoder). -/
def epLaw (p : ℝ) (T R : O → ℝ) : Bool × O → ℝ :=
  fun a => if a.1 then p * T a.2 else (1 - p) * R a.2

@[simp] theorem epLaw_true (p : ℝ) (T R : O → ℝ) (o : O) :
    epLaw p T R (true, o) = p * T o := rfl

@[simp] theorem epLaw_false (p : ℝ) (T R : O → ℝ) (o : O) :
    epLaw p T R (false, o) = (1 - p) * R o := rfl

theorem sum_epLaw (p : ℝ) {T R : O → ℝ} (hT : ∑ o, T o = 1) (hR : ∑ o, R o = 1) :
    ∑ a : Bool × O, epLaw p T R a = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [epLaw_true, epLaw_false]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hT, hR]
  ring

/-- The i.i.d. transcript weight of `N` episodes. -/
def transcriptLaw (p : ℝ) (T R : O → ℝ) (N : ℕ) (x : Fin N → Bool × O) : ℝ :=
  ∏ i, epLaw p T R (x i)

theorem transcriptLaw_cons (p : ℝ) (T R : O → ℝ) (N : ℕ) (a : Bool × O)
    (xs : Fin N → Bool × O) :
    transcriptLaw p T R (N + 1) (Fin.cons a xs)
      = epLaw p T R a * transcriptLaw p T R N xs := by
  unfold transcriptLaw
  rw [Fin.prod_univ_succ]
  simp

/-- Splitting a sum over `(N+1)`-transcripts into first episode and rest. -/
theorem sum_pi_succ {E : Type*} [Fintype E] {N : ℕ} (f : (Fin (N + 1) → E) → ℝ) :
    ∑ x : Fin (N + 1) → E, f x = ∑ a : E, ∑ xs : Fin N → E, f (Fin.cons a xs) :=
  calc ∑ x : Fin (N + 1) → E, f x
      = ∑ q : E × (Fin N → E), f (Fin.cons q.1 q.2) :=
        (Fintype.sum_equiv (Fin.consEquiv fun _ => E)
          (fun q => f (Fin.cons q.1 q.2)) f fun _ => rfl).symm
    _ = ∑ a : E, ∑ xs : Fin N → E, f (Fin.cons a xs) :=
        Fintype.sum_prod_type fun q => f (Fin.cons q.1 q.2)

theorem sum_transcriptLaw (p : ℝ) {T R : O → ℝ} (hT : ∑ o, T o = 1)
    (hR : ∑ o, R o = 1) : ∀ N : ℕ, ∑ x : Fin N → Bool × O, transcriptLaw p T R N x = 1
  | 0 => by simp [transcriptLaw]
  | N + 1 => by
    rw [sum_pi_succ (transcriptLaw p T R (N + 1))]
    simp_rw [transcriptLaw_cons, ← Finset.mul_sum,
      sum_transcriptLaw p hT hR N, mul_one]
    exact sum_epLaw p hT hR

/-! ## The rejection decoder -/

/-- The rejection decoder: the outcome of the first matching episode among the
`N` episodes of the transcript, or the fallback `o0` if none matches. -/
def firstMatch (o0 : O) : (N : ℕ) → (Fin N → Bool × O) → O
  | 0, _ => o0
  | N + 1, x => if (x 0).1 then (x 0).2 else firstMatch o0 N (Fin.tail x)

@[simp] theorem firstMatch_zero (o0 : O) (x : Fin 0 → Bool × O) :
    firstMatch o0 0 x = o0 := rfl

theorem firstMatch_cons (o0 : O) (N : ℕ) (a : Bool × O) (xs : Fin N → Bool × O) :
    firstMatch o0 (N + 1) (Fin.cons a xs)
      = if a.1 then a.2 else firstMatch o0 N xs := by
  simp [firstMatch, Fin.tail_cons]

/-- The law of the rejection decoder's output: push the i.i.d. transcript law
forward through `firstMatch`. -/
def outputLaw (p : ℝ) (T R : O → ℝ) (o0 : O) (N : ℕ) (o : O) : ℝ :=
  ∑ x : Fin N → Bool × O,
    transcriptLaw p T R N x * (if firstMatch o0 N x = o then 1 else 0)

/-! ## The mixture identity -/

/-- One-step recursion: conditioning on the first episode. -/
theorem outputLaw_succ (p : ℝ) {T R : O → ℝ} (hT : ∑ o, T o = 1)
    (hR : ∑ o, R o = 1) (o0 : O) (N : ℕ) (o : O) :
    outputLaw p T R o0 (N + 1) o
      = p * T o + (1 - p) * outputLaw p T R o0 N o := by
  have hmass := sum_transcriptLaw p hT hR N
  have htrue : ∀ o' : O, (∑ xs : Fin N → Bool × O,
      p * T o' * transcriptLaw p T R N xs * (if o' = o then 1 else 0))
        = p * T o' * (if o' = o then 1 else 0) := by
    intro o'
    rw [← Finset.sum_mul, ← Finset.mul_sum, hmass, mul_one]
  have hfalse : ∀ o' : O, (∑ xs : Fin N → Bool × O,
      (1 - p) * R o' * transcriptLaw p T R N xs *
        (if firstMatch o0 N xs = o then 1 else 0))
        = (1 - p) * R o' * outputLaw p T R o0 N o := by
    intro o'
    rw [show outputLaw p T R o0 N o = ∑ xs : Fin N → Bool × O,
        transcriptLaw p T R N xs * (if firstMatch o0 N xs = o then 1 else 0)
      from rfl]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun xs _ => by ring
  calc outputLaw p T R o0 (N + 1) o
      = ∑ a : Bool × O, ∑ xs : Fin N → Bool × O,
          epLaw p T R a * transcriptLaw p T R N xs *
            (if (if a.1 then a.2 else firstMatch o0 N xs) = o then 1 else 0) := by
        unfold outputLaw
        rw [sum_pi_succ]
        simp_rw [transcriptLaw_cons, firstMatch_cons]
    _ = (∑ o' : O, ∑ xs : Fin N → Bool × O,
          p * T o' * transcriptLaw p T R N xs * (if o' = o then 1 else 0))
        + ∑ o' : O, ∑ xs : Fin N → Bool × O,
            (1 - p) * R o' * transcriptLaw p T R N xs *
              (if firstMatch o0 N xs = o then 1 else 0) := by
        rw [Fintype.sum_prod_type, Fintype.sum_bool]
        simp
    _ = (∑ o' : O, p * T o' * (if o' = o then 1 else 0))
        + ∑ o' : O, (1 - p) * R o' * outputLaw p T R o0 N o := by
        simp_rw [htrue, hfalse]
    _ = p * T o + (1 - p) * outputLaw p T R o0 N o := by
        have h1 : (∑ o' : O, p * T o' * (if o' = o then 1 else 0)) = p * T o := by
          simp [mul_ite]
        have h2 : (∑ o' : O, (1 - p) * R o' * outputLaw p T R o0 N o)
            = (1 - p) * outputLaw p T R o0 N o := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hR, mul_one]
        rw [h1, h2]

/-- **The mixture identity.**  The rejection decoder's output law is exactly
the mixture `(1 − (1−p)^N) · T + (1−p)^N · δ_{o₀}` — proved from the explicit
finite i.i.d. construction, not assumed. -/
theorem outputLaw_eq_mixture (p : ℝ) {T R : O → ℝ} (hT : ∑ o, T o = 1)
    (hR : ∑ o, R o = 1) (o0 : O) :
    ∀ (N : ℕ) (o : O), outputLaw p T R o0 N o
      = (1 - (1 - p) ^ N) * T o + (1 - p) ^ N * (if o = o0 then 1 else 0)
  | 0, o => by
    unfold outputLaw
    rcases eq_or_ne o o0 with h | h
    · simp [transcriptLaw, h]
    · simp [transcriptLaw, h, Ne.symm h]
  | N + 1, o => by
    rw [outputLaw_succ p hT hR o0 N o, outputLaw_eq_mixture p hT hR o0 N o]
    ring

/-! ## Total variation and the coverage bound -/

/-- Total variation distance between finite (signed) laws: `½ Σ |μ − ν|`. -/
noncomputable def tvDist (μ ν : O → ℝ) : ℝ := (1 / 2) * ∑ o, |μ o - ν o|

theorem tvDist_nonneg (μ ν : O → ℝ) : 0 ≤ tvDist μ ν :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- TV between a `(1−q, q)`-mixture and its first component is at most `q`. -/
theorem tvDist_mixture_le {T D : O → ℝ} (hT : IsDist T) (hD : IsDist D)
    {q : ℝ} (hq : 0 ≤ q) :
    tvDist (fun o => (1 - q) * T o + q * D o) T ≤ q := by
  unfold tvDist
  have h1 : ∀ o : O, |(1 - q) * T o + q * D o - T o| = q * |D o - T o| := by
    intro o
    have h : (1 - q) * T o + q * D o - T o = q * (D o - T o) := by ring
    rw [h, abs_mul, abs_of_nonneg hq]
  simp_rw [h1]
  rw [← Finset.mul_sum]
  have h2 : ∑ o, |D o - T o| ≤ 2 := by
    have hb : ∀ o : O, |D o - T o| ≤ D o + T o := fun o =>
      abs_le.mpr ⟨by linarith [hD.1 o, hT.1 o], by linarith [hD.1 o, hT.1 o]⟩
    calc ∑ o, |D o - T o| ≤ ∑ o, (D o + T o) := Finset.sum_le_sum fun o _ => hb o
      _ = 2 := by rw [Finset.sum_add_distrib, hD.2, hT.2]; norm_num
  have h3 : q * ∑ o, |D o - T o| ≤ q * 2 := mul_le_mul_of_nonneg_left h2 hq
  linarith

/-- The point mass at the fallback is a probability vector. -/
theorem isDist_dirac (o0 : O) : IsDist (fun o : O => if o = o0 then (1 : ℝ) else 0) := by
  constructor
  · intro o; dsimp only; split <;> norm_num
  · simp

/-- **The rejection-decoder inequality (episodic coverage bound, finite
core).**  With per-episode match probability `p ≤ 1` and `N` i.i.d. episodes,
the rejection decoder's output law is within total variation `(1 − p)^N` of
the test law `T`.  The bound does not depend on `T`, `R`, or `o₀`, so at paper
level it is uniform over the world class: `Γ_{≤n}(E_N) ≤ (1−p)^N`. -/
theorem tvDist_outputLaw_le (p : ℝ) {T R : O → ℝ} (hT : IsDist T)
    (hR : IsDist R) (hp : p ≤ 1) (o0 : O) (N : ℕ) :
    tvDist (outputLaw p T R o0 N) T ≤ (1 - p) ^ N := by
  have hq : (0 : ℝ) ≤ (1 - p) ^ N := pow_nonneg (by linarith) N
  have hfun : outputLaw p T R o0 N = fun o =>
      (1 - (1 - p) ^ N) * T o + (1 - p) ^ N * (if o = o0 then 1 else 0) :=
    funext fun o => outputLaw_eq_mixture p hT.2 hR.2 o0 N o
  rw [hfun]
  exact tvDist_mixture_le hT (isDist_dirac o0) hq

/-- Sanity: the decoder's output law is itself a probability vector. -/
theorem isDist_outputLaw (p : ℝ) {T R : O → ℝ} (hT : IsDist T) (hR : IsDist R)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (o0 : O) (N : ℕ) :
    IsDist (outputLaw p T R o0 N) := by
  have hq0 : (0 : ℝ) ≤ (1 - p) ^ N := pow_nonneg (by linarith) N
  have hq1 : (1 - p) ^ N ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  constructor
  · intro o
    rw [outputLaw_eq_mixture p hT.2 hR.2 o0 N o]
    have hite : (0 : ℝ) ≤ (if o = o0 then (1 : ℝ) else 0) := by split <;> norm_num
    have g1 : (0 : ℝ) ≤ (1 - (1 - p) ^ N) * T o :=
      mul_nonneg (by linarith) (hT.1 o)
    have g2 : (0 : ℝ) ≤ (1 - p) ^ N * (if o = o0 then (1 : ℝ) else 0) :=
      mul_nonneg hq0 hite
    linarith
  · simp_rw [outputLaw_eq_mixture p hT.2 hR.2 o0 N]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hT.2,
      (isDist_dirac o0).2]
    ring

/-! ## The limit -/

/-- The coverage bound is geometric: `(1 − p)^N → 0` for `0 < p ≤ 1`. -/
theorem tendsto_coverage_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Tendsto (fun N : ℕ => (1 - p) ^ N) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- **Corollary.**  For any fixed positive match probability, the rejection
decoder's error vanishes as the number of episodes grows. -/
theorem tendsto_tvDist_outputLaw (p : ℝ) {T R : O → ℝ} (hT : IsDist T)
    (hR : IsDist R) (hp0 : 0 < p) (hp1 : p ≤ 1) (o0 : O) :
    Tendsto (fun N : ℕ => tvDist (outputLaw p T R o0 N) T) atTop (𝓝 0) :=
  squeeze_zero (fun _ => tvDist_nonneg _ _)
    (fun N => tvDist_outputLaw_le p hT hR hp1 o0 N)
    (tendsto_coverage_bound hp0 hp1)

end CoverageBound
end IdExp
