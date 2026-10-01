import Formal.CausalContinuity
import Formal.NativeDistance

/-!
# The native metric on the actual behavioral quotient

Finite-depth distances and their uniformly convergent weighted sum are
continuous on the compact raw space. Their zero relation is behavioral
equivalence. The induced metric is built on the existing `CausalWorld`
quotient itself; its compactness follows from the continuous surjection
from valid raw response kernels. No compactness of a policy class or
terminal Le Cam topology is substituted for this geometry.
-/

namespace IdExp

open Set TopologicalSpace

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [DecidableEq A] [DecidableEq O]

theorem continuous_nativeDepthDist (n : ℕ) :
    Continuous (fun p : ValidCausalWorld A O × ValidCausalWorld A O =>
      nativeDepthDist n p.1 p.2) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun τ _ => continuous_validCausalPlanObservationTV n τ)

/-- The summable geometric bound is uniform over the entire raw space. -/
theorem continuous_nativeDist :
    Continuous (fun p : ValidCausalWorld A O × ValidCausalWorld A O =>
      nativeDist p.1 p.2) := by
  apply continuous_tsum
    (fun n => continuous_const.mul (continuous_nativeDepthDist (n + 1)))
    nativeWeight_summable
  intro n p
  change ‖nativeWeight n * nativeDepthDist (n + 1) p.1 p.2‖ ≤ nativeWeight n
  rw [Real.norm_of_nonneg (mul_nonneg (nativeWeight_pos n).le
    (nativeDepthDist_nonneg (n + 1) p.1 p.2))]
  exact mul_le_of_le_one_right (nativeWeight_pos n).le
    (nativeDepthDist_le_one (n + 1) p.1 p.2)

/-- Distance depends on behaviors, not on chosen unreachable-history rows. -/
theorem nativeDist_congr {Q R Q' R' : ValidCausalWorld A O}
    (h : CausalBehEq Q.val R.val) (h' : CausalBehEq Q'.val R'.val) :
    nativeDist Q Q' = nativeDist R R' := by
  simp only [nativeDist, nativeDepthDist,
    nativeObservationLaw_eq_of_behEq h, nativeObservationLaw_eq_of_behEq h']

/-- Evaluate on chosen representatives. The congruence theorem makes this
independent of the choice, and the mk lemma identifies the induced distance. -/
noncomputable def nativeWorldDist (q r : CausalWorld A O) : ℝ :=
  nativeDist (Quotient.out q) (Quotient.out r)

@[simp] theorem nativeWorldDist_mk (Q R : ValidCausalWorld A O) :
    nativeWorldDist (Quotient.mk _ Q) (Quotient.mk _ R) = nativeDist Q R := by
  apply nativeDist_congr
  · exact Quotient.exact (Quotient.out_eq (Quotient.mk _ Q))
  · exact Quotient.exact (Quotient.out_eq (Quotient.mk _ R))

/-- Metric data before identifying its topology with the quotient topology. -/
@[instance_reducible]
noncomputable def nativeWorldMetric : MetricSpace (CausalWorld A O) where
  dist := nativeWorldDist
  dist_self q := nativeDist_self (Quotient.out q)
  dist_comm q r := nativeDist_comm (Quotient.out q) (Quotient.out r)
  dist_triangle q r s := nativeDist_triangle (Quotient.out q) (Quotient.out r) (Quotient.out s)
  eq_of_dist_eq_zero := by
    intro q r h
    have hrel : (validCausalBehEqSetoid A O).r (Quotient.out q) (Quotient.out r) :=
      (nativeDist_eq_zero_iff (Quotient.out q) (Quotient.out r)).1 h
    calc
      q = Quotient.mk _ (Quotient.out q) := (Quotient.out_eq q).symm
      _ = Quotient.mk _ (Quotient.out r) := Quotient.sound hrel
      _ = r := Quotient.out_eq r

/-- Compact-to-Hausdorff quotient uniqueness identifies the topology induced
by the native metric with the canonical quotient of the raw product topology.
This step avoids silently replacing either of those topologies. -/
theorem nativeWorldMetric_topology :
    (inferInstance : TopologicalSpace (CausalWorld A O)) =
      (nativeWorldMetric (A := A) (O := O)).toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace (CausalWorld A O) :=
    (nativeWorldMetric (A := A) (O := O)).toUniformSpace.toTopologicalSpace
  letI : MetricSpace (CausalWorld A O) := nativeWorldMetric
  have hcont : Continuous (Quotient.mk (validCausalBehEqSetoid A O)) := by
    apply continuous_iff_continuousAt.2
    intro Q
    apply tendsto_iff_dist_tendsto_zero.2
    have ht := ((continuous_nativeDist (A := A) (O := O)).comp
      (continuous_id.prodMk
        (continuous_const : Continuous (fun _ : ValidCausalWorld A O => Q)))).tendsto Q
    change Filter.Tendsto
      (fun R : ValidCausalWorld A O => nativeWorldDist (Quotient.mk _ R) (Quotient.mk _ Q))
      (nhds Q) (nhds 0)
    simpa only [Function.comp_def, id_eq, nativeDist_self, nativeWorldDist_mk] using ht
  exact (Topology.IsQuotientMap.of_surjective_continuous
    Quotient.mk_surjective hcont).eq_coinduced.symm

/-- The paper's quotient has precisely the displayed native metric, whose
topology agrees definitionally with its pre-existing quotient topology. -/
noncomputable instance causalWorld_nativeMetricSpace : MetricSpace (CausalWorld A O) :=
  nativeWorldMetric.replaceTopology nativeWorldMetric_topology

@[simp] theorem causalWorld_dist_mk (Q R : ValidCausalWorld A O) :
    dist (Quotient.mk _ Q : CausalWorld A O) (Quotient.mk _ R) = nativeDist Q R :=
  nativeWorldDist_mk Q R

/-- The canonical quotient projection is continuous from the raw product
topology to the actual native metric topology. -/
theorem continuous_causalWorld_mk :
    Continuous (Quotient.mk (validCausalBehEqSetoid A O)) := by
  apply continuous_iff_continuousAt.2
  intro Q
  apply tendsto_iff_dist_tendsto_zero.2
  have ht := ((continuous_nativeDist (A := A) (O := O)).comp
    (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : ValidCausalWorld A O => Q)))).tendsto Q
  simpa only [Function.comp_def, id_eq, nativeDist_self, causalWorld_dist_mk] using ht

/-- The actual quotient is compact as a continuous image of the compact
valid-raw-kernel space. -/
instance causalWorld_compactSpace : CompactSpace (CausalWorld A O) := by
  have hsurj : Function.Surjective (Quotient.mk (validCausalBehEqSetoid A O)) :=
    Quotient.mk_surjective
  rw [← isCompact_univ_iff]
  rw [← Set.image_univ_of_surjective hsurj]
  exact isCompact_univ.image continuous_causalWorld_mk

/-! ## Native tests and finite-depth pseudometrics on behavioral worlds -/

/-- The native observation law descends to the actual behavioral quotient.
This is a quotient lift, so no discontinuous choice of representative is part
of the law's definition or continuity argument. -/
noncomputable def nativeWorldObservationLaw (n : ℕ) (τ : CausalPlan A O n) :
    CausalWorld A O → CausalObservationTrace O n → ℝ :=
  Quotient.lift (nativeObservationLaw n τ)
    (fun _ _ h => nativeObservationLaw_eq_of_behEq h n τ)

@[simp] theorem nativeWorldObservationLaw_mk (n : ℕ) (τ : CausalPlan A O n)
    (Q : ValidCausalWorld A O) :
    nativeWorldObservationLaw n τ (Quotient.mk _ Q) = nativeObservationLaw n τ Q := rfl

/-- Every descended native law is still an actual probability distribution. -/
theorem nativeWorldObservationLaw_valid (n : ℕ) (τ : CausalPlan A O n)
    (q : CausalWorld A O) : IsDist (nativeWorldObservationLaw n τ q) := by
  induction q using Quotient.inductionOn with
  | h Q => exact nativeObservationLaw_valid n τ Q

/-- Native observation experiments are continuous on the canonical quotient
topology, which is also the installed native-metric topology. -/
theorem continuous_nativeWorldObservationLaw (n : ℕ) (τ : CausalPlan A O n) :
    Continuous (nativeWorldObservationLaw n τ) := by
  have hquot : Topology.IsQuotientMap (Quotient.mk (validCausalBehEqSetoid A O)) :=
    Topology.IsQuotientMap.of_surjective_continuous Quotient.mk_surjective
      continuous_causalWorld_mk
  apply hquot.continuous_iff.2
  exact continuous_validCausalPlanObservationExperiment n τ

/-- The paper's finite-depth pseudometric directly on behavioral worlds:
the maximum TV distance between their descended native observation laws. -/
noncomputable def nativeWorldDepthDist (n : ℕ) (q r : CausalWorld A O) : ℝ :=
  (Finset.univ : Finset (CausalPlan A O n)).sup' Finset.univ_nonempty
    (fun τ => finiteTV (nativeWorldObservationLaw n τ q) (nativeWorldObservationLaw n τ r))

@[simp] theorem nativeWorldDepthDist_mk (n : ℕ) (Q R : ValidCausalWorld A O) :
    nativeWorldDepthDist n (Quotient.mk _ Q) (Quotient.mk _ R) = nativeDepthDist n Q R := rfl

/-- The finite-depth distance is jointly continuous on the quotient, not
merely on raw response coordinates. -/
theorem continuous_nativeWorldDepthDist (n : ℕ) :
    Continuous (fun p : CausalWorld A O × CausalWorld A O =>
      nativeWorldDepthDist n p.1 p.2) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro τ _
  exact continuous_finiteTV.comp
    (((continuous_nativeWorldObservationLaw n τ).comp continuous_fst).prodMk
      ((continuous_nativeWorldObservationLaw n τ).comp continuous_snd))

@[simp] theorem nativeWorldDepthDist_self (n : ℕ) (q : CausalWorld A O) :
    nativeWorldDepthDist n q q = 0 := by
  induction q using Quotient.inductionOn with
  | h Q => exact nativeDepthDist_self n Q

theorem nativeWorldDepthDist_comm (n : ℕ) (q r : CausalWorld A O) :
    nativeWorldDepthDist n q r = nativeWorldDepthDist n r q := by
  induction q using Quotient.inductionOn with
  | h Q =>
    induction r using Quotient.inductionOn with
    | h R => exact nativeDepthDist_comm n Q R

theorem nativeWorldDepthDist_triangle (n : ℕ) (q r s : CausalWorld A O) :
    nativeWorldDepthDist n q s ≤ nativeWorldDepthDist n q r + nativeWorldDepthDist n r s := by
  induction q using Quotient.inductionOn with
  | h Q =>
    induction r using Quotient.inductionOn with
    | h R =>
      induction s using Quotient.inductionOn with
      | h S => exact nativeDepthDist_triangle n Q R S

/-- The finite-depth continuous pseudometric statement with the paper's
behavioral worlds as its domain, rather than raw kernel representatives. -/
theorem nativeWorldDepthDist_continuous_pseudometric (n : ℕ) :
    Continuous (fun p : CausalWorld A O × CausalWorld A O =>
      nativeWorldDepthDist n p.1 p.2) ∧
    (∀ q : CausalWorld A O, nativeWorldDepthDist n q q = 0) ∧
    (∀ q r : CausalWorld A O, nativeWorldDepthDist n q r = nativeWorldDepthDist n r q) ∧
    (∀ q r s : CausalWorld A O,
      nativeWorldDepthDist n q s ≤ nativeWorldDepthDist n q r + nativeWorldDepthDist n r s) :=
  ⟨continuous_nativeWorldDepthDist n, nativeWorldDepthDist_self n,
    nativeWorldDepthDist_comm n, nativeWorldDepthDist_triangle n⟩

/-- The installed metric is exactly the weighted sum of the descended
finite-depth pseudometrics, as displayed in the paper. -/
theorem causalWorld_dist_eq_tsum_nativeWorldDepthDist (q r : CausalWorld A O) :
    dist q r = ∑' n, nativeWeight n * nativeWorldDepthDist (n + 1) q r := by
  induction q using Quotient.inductionOn with
  | h Q =>
    induction r using Quotient.inductionOn with
    | h R =>
      simp only [causalWorld_dist_mk, nativeWorldDepthDist_mk, nativeDist]

/-- Explicitly record the continuous pseudometric axioms at each depth.
No incompatible pseudometric topology is installed on raw kernels. -/
theorem nativeDepthDist_continuous_pseudometric (n : ℕ) :
    Continuous (fun p : ValidCausalWorld A O × ValidCausalWorld A O =>
      nativeDepthDist n p.1 p.2) ∧
    (∀ Q : ValidCausalWorld A O, nativeDepthDist n Q Q = 0) ∧
    (∀ Q R : ValidCausalWorld A O, nativeDepthDist n Q R = nativeDepthDist n R Q) ∧
    (∀ Q R S : ValidCausalWorld A O,
      nativeDepthDist n Q S ≤ nativeDepthDist n Q R + nativeDepthDist n R S) :=
  ⟨continuous_nativeDepthDist n, nativeDepthDist_self n,
    nativeDepthDist_comm n, nativeDepthDist_triangle n⟩

end IdExp
