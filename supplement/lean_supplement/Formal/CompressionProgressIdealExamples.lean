import Formal.KolmogorovInterpreterConstructions
import Formal.KolmogorovPrefixChain
import Formal.CompressionProgressCompleteFinite

/-!
# Finite and divergent complete ideal-compression examples

The actual interpreter constructions come from KolmogorovInterpreterConstructions.
The explicit base-machine chain inequality is discharged by the separate prefix
concatenation construction; it is never an axiom or a description-length oracle.
-/
namespace IdExp.CompressionProgressIdealExamples
open KolmogorovHistoryCompressor KolmogorovInterpreterConstructions
open CompressionProgressSwap CompressionProgressIdeal
open scoped ENNReal
noncomputable section

variable (V : Machine) (c M : ℕ) (hM : 2 ≤ M)
variable (hchain : ∀ m D : Bits, V.complexity [] D ≤
  V.complexity [] m + V.complexity m D + c)
variable (hgap : c + 2 ≤ M)

@[simp] theorem encodeHistory_length (h : List (Bool × Fin 2)) :
    (encodeHistory h).length = 2 * h.length := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [encodeHistory, ih]; omega

theorem encodeHistory_ne_nil (h : List (Bool × Fin 2)) (hh : h ≠ []) :
    encodeHistory h ≠ [] := by
  intro he
  have := congrArg List.length he
  simp only [encodeHistory_length, List.length_nil] at this
  have : h.length = 0 := by omega
  exact hh (List.length_eq_zero_iff.mp this)

abbrev learner (finite : Bool) (initial : Bits) : HistoryCompressor :=
  specification (machine finite V M hM) initial

theorem finite_cost_empty (h : History) (hh : h ≠ []) :
    twoPartCost (machine true V M hM) [] h = M + V.complexity [] (encodeHistory h) + 1 := by
  unfold twoPartCost
  rw [finite_empty, finite_background V M hM _ (encodeHistory_ne_nil h hh)]
  omega

include hchain hgap

theorem finite_cost_gap (h : History) (hh : h ≠ []) (m : Bits) (hm : m ≠ []) :
    twoPartCost (machine true V M hM) [] h + 1 ≤
      twoPartCost (machine true V M hM) m h := by
  rw [finite_cost_empty V M hM h hh]
  unfold twoPartCost
  rw [finite_background V M hM m hm]
  by_cases he : encodeHistory h = m
  · rw [← he, finite_self V M hM _ (encodeHistory_ne_nil h hh)]
  · rw [finite_other V M hM _ _ (encodeHistory_ne_nil h hh) he]
    have := hchain m (encodeHistory h)
    omega

theorem finite_update (initial old : Bits) (h : History) (hh : h ≠ []) :
    (learner V M hM true initial).update old h = [] := by
  let S := learner V M hM true initial
  have hb := S.update_minimizes old [] h
  by_contra he
  have hg := finite_cost_gap V c M hM hchain hgap h hh (S.update old h) he
  change twoPartCost (machine true V M hM) (S.update old h) h ≤
    twoPartCost (machine true V M hM) [] h at hb
  omega

theorem finite_gain_empty (initial : Bits) (h : History) (hh : h ≠ []) :
    (learner V M hM true initial).gain [] h = 0 := by
  unfold IdealHistoryCompressor.Specification.gain
  rw [finite_update V c M hM hchain hgap initial [] h hh]
  simp

theorem finite_gain_positive (initial old : Bits) (ho : old ≠ [])
    (h : History) (hh : h ≠ []) :
    1 ≤ (learner V M hM true initial).gain old h := by
  have hg := finite_cost_gap V c M hM hchain hgap h hh old ho
  unfold IdealHistoryCompressor.Specification.gain
  rw [finite_update V c M hM hchain hgap initial old h hh]
  change 1 ≤ (twoPartCost (machine true V M hM) old h : ℝ) -
    (twoPartCost (machine true V M hM) [] h : ℝ)
  exact_mod_cast (show (1 : ℤ) ≤ (twoPartCost (machine true V M hM) old h : ℤ) -
    (twoPartCost (machine true V M hM) [] h : ℤ) by omega)

theorem finite_runFrom_empty (initial : Bits) (archive rest : History) :
    (learner V M hM true initial).runFrom [] archive rest = ([],0) := by
  induction rest generalizing archive with
  | nil => rfl
  | cons x rest ih =>
    simp only [IdealHistoryCompressor.Specification.runFrom]
    rw [finite_update V c M hM hchain hgap initial [] _ (by simp)]
    rw [ih, finite_gain_empty V c M hM hchain hgap initial _ (by simp)]
    simp
    rfl

theorem finite_score_cons (initial : Bits) (x : Bool × Fin 2) (rest : History) :
    (learner V M hM true initial).score (x :: rest) =
      (learner V M hM true initial).gain initial [x] := by
  change ((learner V M hM true initial).runFrom initial [] (x :: rest)).2 = _
  simp only [IdealHistoryCompressor.Specification.runFrom, List.nil_append]
  rw [finite_update V c M hM hchain hgap initial initial [x] (by simp)]
  rw [finite_runFrom_empty V c M hM hchain hgap]
  simp

omit hchain hgap in
theorem divergent_cost_self (h : History) (hh : h ≠ []) :
    twoPartCost (machine false V M hM) (encodeHistory h) h =
      M + V.complexity [] (encodeHistory h) + 1 := by
  unfold twoPartCost
  rw [divergent_background, divergent_self V M hM _ (encodeHistory_ne_nil h hh)]

theorem divergent_cost_gap (h : History) (hh : h ≠ []) (m : Bits)
    (hm : m ≠ encodeHistory h) :
    twoPartCost (machine false V M hM) (encodeHistory h) h + 1 ≤
      twoPartCost (machine false V M hM) m h := by
  rw [divergent_cost_self V M hM h hh]
  unfold twoPartCost
  rw [divergent_background, divergent_other V M hM m _ (Ne.symm hm)]
  have := hchain m (encodeHistory h)
  omega

theorem divergent_update (initial old : Bits) (h : History) (hh : h ≠ []) :
    (learner V M hM false initial).update old h = encodeHistory h := by
  let S := learner V M hM false initial
  have hb := S.update_minimizes old (encodeHistory h) h
  by_contra he
  have hg := divergent_cost_gap V c M hM hchain hgap h hh (S.update old h) he
  change twoPartCost (machine false V M hM) (S.update old h) h ≤
    twoPartCost (machine false V M hM) (encodeHistory h) h at hb
  omega

theorem divergent_gain_positive (initial old : Bits) (h : History) (hh : h ≠ [])
    (ho : old ≠ encodeHistory h) :
    1 ≤ (learner V M hM false initial).gain old h := by
  have hg := divergent_cost_gap V c M hM hchain hgap h hh old ho
  unfold IdealHistoryCompressor.Specification.gain
  rw [divergent_update V c M hM hchain hgap initial old h hh]
  change 1 ≤ (twoPartCost (machine false V M hM) old h : ℝ) -
    (twoPartCost (machine false V M hM) (encodeHistory h) h : ℝ)
  exact_mod_cast (show (1 : ℤ) ≤ (twoPartCost (machine false V M hM) old h : ℤ) -
    (twoPartCost (machine false V M hM) (encodeHistory h) h : ℤ) by omega)


def firstBound (initial : Bits) : ℝ :=
  ∑ x : Bool × Fin 2, (learner V M hM true initial).gain initial [x]

omit hchain hgap in
theorem firstBound_nonneg (initial : Bits) : 0 ≤ firstBound V M hM initial :=
  Finset.sum_nonneg fun _ _ => IdealHistoryCompressor.Specification.gain_nonneg _ _ _

theorem finite_score_bound (initial : Bits) (h : History) :
    (learner V M hM true initial).score h ≤ firstBound V M hM initial := by
  cases h with
  | nil => simpa [IdealHistoryCompressor.Specification.score,
      IdealHistoryCompressor.Specification.runFrom] using firstBound_nonneg V M hM initial
  | cons x rest =>
    rw [finite_score_cons V c M hM hchain hgap]
    unfold firstBound
    exact Finset.single_le_sum (f := fun y : Bool × Fin 2 =>
      (learner V M hM true initial).gain initial [y]) (fun y _ =>
      (learner V M hM true initial).gain_nonneg initial [y]) (Finset.mem_univ x)

omit hchain hgap in
theorem averageExperiment_isDist (e : Bool) (π : Policy) (n : ℕ) :
    IsDist (averageExperiment e π n) := by
  have h0 := causalFiniteExperiment_valid π.1 π.2 (response e) (response_valid e) n 0
  have h1 := causalFiniteExperiment_valid π.1 π.2 (response e) (response_valid e) n 1
  constructor
  · intro w
    exact div_nonneg (add_nonneg (h0.1 w) (h1.1 w)) (by norm_num)
  · change (∑ w, (causalFiniteExperiment π.1 (response e) n 0 w +
      causalFiniteExperiment π.1 (response e) n 1 w) / 2) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, h0.2, h1.2]
    norm_num

omit hchain hgap in
theorem prefix_of_score_le (S : HistoryCompressor) (e : Bool) (π : Policy) (n : ℕ) (B : ℝ)
    (hB : ∀ h : History, S.score h ≤ B) : prefixObjective S e π n ≤ B := by
  have hdist := averageExperiment_isDist e π n
  unfold prefixObjective objective
  calc
    _ ≤ ∑ w, averageExperiment e π n w * B := Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hB _) (hdist.1 w)
    _ = B := by rw [← Finset.sum_mul, hdist.2, one_mul]

theorem finite_prefix_bound (initial : Bits) (e : Bool) (π : Policy) (n : ℕ) :
    prefixObjective (learner V M hM true initial) e π n ≤ firstBound V M hM initial :=
  prefix_of_score_le _ e π n _ (finite_score_bound V c M hM hchain hgap initial)

theorem finite_complete_bound (initial : Bits) (e : Bool) (π : Policy) :
    completeObjective (learner V M hM true initial) e π ≤
      ENNReal.ofReal (firstBound V M hM initial) := by
  apply iSup_le
  intro n
  exact ENNReal.ofReal_le_ofReal (finite_prefix_bound V c M hM hchain hgap initial e π n)

theorem finite_prefix_positive (initial : Bits) (hi : initial ≠ [])
    (e : Bool) (π : Policy) (n : ℕ) :
    1 ≤ prefixObjective (learner V M hM true initial) e π (n+1) := by
  have hdist := averageExperiment_isDist e π (n+1)
  unfold prefixObjective objective
  calc
    1 = ∑ w, averageExperiment e π (n+1) w * 1 := by simp [hdist.2]
    _ ≤ _ := Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (by
      rw [List.ofFn_succ, finite_score_cons V c M hM hchain hgap]
      exact finite_gain_positive V c M hM hchain hgap initial initial hi _ (by simp))
      (hdist.1 w)

theorem finite_complete_positive (initial : Bits) (hi : initial ≠ [])
    (e : Bool) (π : Policy) :
    1 ≤ completeObjective (learner V M hM true initial) e π := by
  apply le_trans (b := ENNReal.ofReal
    (prefixObjective (learner V M hM true initial) e π 1))
  · simpa using ENNReal.ofReal_le_ofReal
      (finite_prefix_positive V c M hM hchain hgap initial hi e π 0)
  · exact le_iSup (fun n => ENNReal.ofReal
      (prefixObjective (learner V M hM true initial) e π n)) 1

theorem finite_complete_dominated_maximizer (initial : Bits) (hi : initial ≠ []) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      0 < completeObjective (learner V M hM true initial) e π ∧
      completeObjective (learner V M hM true initial) e π < ⊤ ∧
      (∀ ρ : Policy, completeObjective (learner V M hM true initial) e ρ ≤
        completeObjective (learner V M hM true initial) e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1/2) := by
  obtain ⟨e,π,hr,hfin,hmax,hgreat,hdom,hnondom,haudit⟩ :=
    CompressionProgressCompleteFinite.exists_complete_dominated_maximizer_of_prefix_bound
      (learner V M hM true initial) (firstBound V M hM initial)
      (fun π n => finite_prefix_bound V c M hM hchain hgap initial false π n)
  exact ⟨e,π,hr,lt_of_lt_of_le (by norm_num)
    (finite_complete_positive V c M hM hchain hgap initial hi e π),
    hfin,hmax,hgreat,hdom,hnondom,haudit⟩

theorem divergent_runFrom_lower (initial : Bits) (archive rest : History) :
    (rest.length : ℝ) ≤
      ((learner V M hM false initial).runFrom (encodeHistory archive) archive rest).2 := by
  induction rest generalizing archive with
  | nil => simp [IdealHistoryCompressor.Specification.runFrom]
  | cons x rest ih =>
    have hne : encodeHistory archive ≠ encodeHistory (archive ++ [x]) := by
      intro he
      have he := congrArg List.length he
      simp only [encodeHistory_length, List.length_append, List.length_cons,
        List.length_nil] at he
      omega
    have hg := divergent_gain_positive V c M hM hchain hgap initial
      (encodeHistory archive) (archive ++ [x]) (by simp) hne
    simp only [IdealHistoryCompressor.Specification.runFrom]
    rw [divergent_update V c M hM hchain hgap initial _ _ (by simp)]
    have ht := ih (archive ++ [x])
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem divergent_score_lower (initial : Bits) (x : Bool × Fin 2) (rest : History) :
    (rest.length : ℝ) ≤ (learner V M hM false initial).score (x :: rest) := by
  change (rest.length : ℝ) ≤
    ((learner V M hM false initial).runFrom initial [] (x :: rest)).2
  simp only [IdealHistoryCompressor.Specification.runFrom, List.nil_append]
  rw [divergent_update V c M hM hchain hgap initial initial [x] (by simp)]
  have ht := divergent_runFrom_lower V c M hM hchain hgap initial [x] rest
  have hg := (learner V M hM false initial).gain_nonneg initial [x]
  change _ ≤ _ + _
  linarith

theorem divergent_prefix_lower (initial : Bits) (e : Bool) (π : Policy) (n : ℕ) :
    (n : ℝ) ≤ prefixObjective (learner V M hM false initial) e π (n+1) := by
  have hdist := averageExperiment_isDist e π (n+1)
  unfold prefixObjective objective
  calc
    (n : ℝ) = ∑ w, averageExperiment e π (n+1) w * (n : ℝ) := by
      rw [← Finset.sum_mul, hdist.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (by
      rw [List.ofFn_succ]
      simpa using divergent_score_lower V c M hM hchain hgap initial (w 0)
        (List.ofFn (fun i : Fin n => w i.succ))) (hdist.1 w)

theorem divergent_complete_top (initial : Bits) (e : Bool) (π : Policy) :
    completeObjective (learner V M hM false initial) e π = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  obtain ⟨n,hn⟩ := exists_nat_ge (r : ℝ)
  have hl := divergent_prefix_lower V c M hM hchain hgap initial e π n
  have hb : (r : ℝ≥0∞) ≤ ENNReal.ofReal
      (prefixObjective (learner V M hM false initial) e π (n+1)) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (le_trans hn hl)
  exact hb.trans (le_iSup (fun k => ENNReal.ofReal
    (prefixObjective (learner V M hM false initial) e π k)) (n+1))


omit hchain hgap in
/-- An actual optimal prefix interpreter has positive finite complete-return
maxima that miss the revealing experiment. Only existence of the supplied
base optimal prefix interpreter is a premise; the chain bound is discharged. -/
theorem exists_finite_positive_optimal_prefix (V : Machine)
    (hf : V.PrefixFree) (ho : V.Optimal) :
    ∃ U : Machine, U.PrefixFree ∧ U.Optimal ∧
      (∀ (initial : Bits) (e : Bool) (π : Policy),
        completeObjective (specification U initial) e π < ⊤) ∧
      (∀ initial : Bits, initial ≠ [] → ∃ (e : Bool) (π : Policy),
        π.1 [] e = 0 ∧
        0 < completeObjective (specification U initial) e π ∧
        completeObjective (specification U initial) e π < ⊤ ∧
        (∀ ρ : Policy, completeObjective (specification U initial) e ρ ≤
          completeObjective (specification U initial) e π) ∧
        CausalFinitarilyGreatest (response e) (policy e) ∧
        CausalFinitaryDominates (response e) (policy e) π ∧
        ¬ CausalFinitaryDominates (response e) π (policy e) ∧
        (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
          (causalFiniteExperiment (policy e).1 (response e) 1) = 1/2)) := by
  obtain ⟨c,hc⟩ := KolmogorovPrefixChain.exists_chain_constant V hf ho
  have hm : 2 ≤ c+2 := by omega
  refine ⟨machine true V (c+2) hm, prefixFree true V (c+2) hm hf,
    optimal true V (c+2) hm ho, ?_, ?_⟩
  · intro initial e π
    exact lt_of_le_of_lt (finite_complete_bound V c (c+2) hm hc (by omega) initial e π)
      ENNReal.ofReal_lt_top
  · intro initial hi
    exact finite_complete_dominated_maximizer V c (c+2) hm hc (by omega) initial hi

omit hchain hgap in
/-- Additive optimality and exact full-archive oracle fitting do not guarantee
finite undiscounted progress. This concrete interpreter gives infinite complete
expected return for every initialization and every randomized history policy. -/
theorem exists_divergent_optimal_prefix (V : Machine)
    (hf : V.PrefixFree) (ho : V.Optimal) :
    ∃ U : Machine, U.PrefixFree ∧ U.Optimal ∧
      ∀ (initial : Bits) (e : Bool) (π : Policy),
        completeObjective (specification U initial) e π = ⊤ := by
  obtain ⟨c,hc⟩ := KolmogorovPrefixChain.exists_chain_constant V hf ho
  have hm : 2 ≤ c+2 := by omega
  refine ⟨machine false V (c+2) hm, prefixFree false V (c+2) hm hf,
    optimal false V (c+2) hm ho, ?_⟩
  intro initial e π
  exact divergent_complete_top V c (c+2) hm hc (by omega) initial e π

end
end IdExp.CompressionProgressIdealExamples
