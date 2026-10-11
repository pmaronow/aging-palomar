module

public import SphericalAging.SphereEulerSourceApproximation

public section

/-! Actual Euler states and queries factor through their literal initial
seed and observed gradient history. No measurability of undisclosed
disorder, or conditional Gaussian law, is required by this factorization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SphericalAging.SphereEulerObservedHistory
open FiniteModel HardSphereDynamics SphereEulerSourceApproximation
open SphereEulerModelApproximation SphereEulerMeshRate SphereEulerPredictable
open SphereEulerQueryData
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] abbrev History (N k : ℕ) := Seed N×(Fin k→State N)

@[expose] def actualHistory (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) : History N k :=
  ((q.1.2,q.2),fun j => SphereEulerSourceApproximation.gradient β T M j.val q)

@[expose] def historyGradients (k : ℕ) (z : History N k) (j : ℕ) : State N :=
  if hj : j<k then z.2 ⟨j,hj⟩ else 0

@[expose] def historyState (β T : ℝ≥0) (M k : ℕ) (z : History N k) : State N :=
  stateFromData β (mesh T M) z.1.1
    (fun j => increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j z.1.2)
    (historyGradients k z) k

theorem stateFromData_congr_prefix (β h : ℝ) (x : State N) (increments gradients other : ℕ→State N)
    (k : ℕ) (heq : ∀j,j<k → gradients j=other j) :
    stateFromData β h x increments gradients k=stateFromData β h x increments other k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change stepFromGradient β h (stateFromData β h x increments gradients k) (increments k) (gradients k)=
      stepFromGradient β h (stateFromData β h x increments other k) (increments k) (other k)
    rw [ih (fun j hj => heq j (Nat.lt_trans hj (Nat.lt_succ_self k))),heq k (Nat.lt_succ_self k)]

theorem historyState_measurable (β T : ℝ≥0) (M k : ℕ) : Measurable (historyState (N:=N) β T M k) := by
  apply stateFromData_measurable β (mesh T M)
    (fun z : History N k => z.1.1)
    (fun j z => increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j z.1.2)
    (fun j z => historyGradients k z j) k
  · exact measurable_fst.comp measurable_fst
  · intro j _
    exact (seed_increment_measurable T M j).comp measurable_fst
  · intro j hj
    simp only [historyGradients,dif_pos hj]
    exact (measurable_pi_apply (⟨j,hj⟩ : Fin k)).comp
      (measurable_snd : Measurable (fun z : History N k => z.2))

theorem actual_node_eq_historyState (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) :
    node (NullAugmentation.driver (VectorBrownian.driver N)) β (mesh T M) q.1.1 q.1.2 k q.2=
      historyState β T M k (actualHistory β T M k q) := by
  unfold node historyState
  rw [state_eq_stateFromData]
  apply stateFromData_congr_prefix
  intro j hj
  simp only [historyGradients,dif_pos hj,actualHistory]
  rfl

theorem actual_node_measurable_history (β T : ℝ≥0) (M k : ℕ) :
    Measurable[MeasurableSpace.comap (actualHistory (N:=N) (p:=p) β T M k) inferInstance]
      (fun q : Sample N p => node (NullAugmentation.driver (VectorBrownian.driver N))
        β (mesh T M) q.1.1 q.1.2 k q.2) := by
  have he : (fun q : Sample N p => node (NullAugmentation.driver (VectorBrownian.driver N))
      β (mesh T M) q.1.1 q.1.2 k q.2)=historyState β T M k ∘ actualHistory β T M k :=
    funext (actual_node_eq_historyState β T M k)
  rw [he]
  exact (historyState_measurable β T M k).comp (Measurable.of_comap_le le_rfl)

theorem actual_query_measurable_history (β T : ℝ≥0) (M k : ℕ) :
    Measurable[MeasurableSpace.comap (actualHistory (N:=N) (p:=p) β T M k) inferInstance]
      (SphereEulerSourceApproximation.query β T M k) :=
  SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp
    (actual_node_measurable_history β T M k)

theorem actual_output_measurable_history (β T : ℝ≥0) (M : ℕ) :
    Measurable[MeasurableSpace.comap (actualHistory (N:=N) (p:=p) β T M M) inferInstance]
      (output β T M) := actual_query_measurable_history β T M M

end SphericalAging.SphereEulerObservedHistory
