module

public import SphericalAging.SphereEulerObservedHistory
public import SphericalAging.WienerStoppedPath

public section

/-! The literal Euler algorithm uses only the initial state and the
Brownian path up to its prescribed horizon. All identities are pathwise,
including paths outside the Wiener almost-sure support. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SphericalAging.SphereEulerStoppedSeed
open FiniteModel HardSphereDynamics SphereEulerSourceApproximation
open SphereEulerModelApproximation SphereEulerMeshRate SphereEulerPredictable
open SphereEulerObservedHistory
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def stopSample (T : ℝ≥0) (q : Sample N p) : Sample N p :=
  (q.1,WienerStoppedPath.stopped T q.2)

theorem stopSample_measurable (T : ℝ≥0) : Measurable (stopSample (N:=N) (p:=p) T) :=
  measurable_fst.prodMk ((WienerStoppedPath.stopped_measurable T).comp measurable_snd)

theorem increment_stopped_eq (T : ℝ≥0) {M : ℕ} (hM : M≠0) {j : ℕ} (hj : j<M)
    (omega : VectorBrownian.Space N) :
    increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j (WienerStoppedPath.stopped T omega)=
      increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j omega := by
  have hb : grid (mesh T M) (j+1)≤T := by
    simpa only [grid_mesh T hM] using grid_mono (mesh T M) (Nat.succ_le_of_lt hj)
  have ha : grid (mesh T M) j≤T := (grid_mono (mesh T M) (Nat.le_succ j)).trans hb
  unfold increment
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change WienerStoppedPath.stopped T omega i (grid (mesh T M) (j+1))-
    WienerStoppedPath.stopped T omega i (grid (mesh T M) j)=
      omega i (grid (mesh T M) (j+1))-omega i (grid (mesh T M) j)
  rw [WienerStoppedPath.stopped_apply_of_le _ _ hb,WienerStoppedPath.stopped_apply_of_le _ _ ha]

theorem node_stopped_eq (β T : ℝ≥0) {M : ℕ} (hM : M≠0)
    (J : Disorder N p) (x : State N) (omega : VectorBrownian.Space N) (k : ℕ) : k≤M →
    node (NullAugmentation.driver (VectorBrownian.driver N)) β (mesh T M) J x k (WienerStoppedPath.stopped T omega)=
      node (NullAugmentation.driver (VectorBrownian.driver N)) β (mesh T M) J x k omega := by
  induction k with
  | zero => intro _;rfl
  | succ k ih =>
    intro hk
    change SphereEulerQuerySpan.step β (mesh T M) J
      (node (NullAugmentation.driver (VectorBrownian.driver N)) β (mesh T M) J x k (WienerStoppedPath.stopped T omega))
      (increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) k (WienerStoppedPath.stopped T omega))=
      SphereEulerQuerySpan.step β (mesh T M) J
      (node (NullAugmentation.driver (VectorBrownian.driver N)) β (mesh T M) J x k omega)
      (increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) k omega)
    rw [ih (Nat.le_trans (Nat.le_succ k) hk),increment_stopped_eq T hM (Nat.lt_of_succ_le hk)]

theorem query_stopped_eq (β T : ℝ≥0) {M : ℕ} (hM : M≠0) (k : ℕ) (hk : k≤M) (q : Sample N p) :
    SphereEulerSourceApproximation.query β T M k (stopSample T q)=SphereEulerSourceApproximation.query β T M k q :=
  congrArg SphereEulerCoefficients.clip (node_stopped_eq β T hM q.1.1 q.1.2 q.2 k hk)

theorem output_stopped_eq (β T : ℝ≥0) {M : ℕ} (hM : M≠0) (q : Sample N p) :
    output β T M (stopSample T q)=output β T M q := query_stopped_eq β T hM M le_rfl q

@[expose] def pastHistory (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) : History N k :=
  actualHistory β T M k (stopSample T q)

theorem actual_node_measurable_pastHistory (β T : ℝ≥0) {M : ℕ} (hM : M≠0) (k : ℕ) (hk : k≤M) :
    Measurable[MeasurableSpace.comap (pastHistory (N:=N) (p:=p) β T M k) inferInstance]
      (fun q : Sample N p => node (NullAugmentation.driver (VectorBrownian.driver N))
        β (mesh T M) q.1.1 q.1.2 k q.2) := by
  have he : (fun q : Sample N p => node (NullAugmentation.driver (VectorBrownian.driver N))
      β (mesh T M) q.1.1 q.1.2 k q.2)=historyState β T M k ∘ pastHistory β T M k := by
    funext q
    exact (node_stopped_eq β T hM q.1.1 q.1.2 q.2 k hk).symm.trans
      (actual_node_eq_historyState β T M k (stopSample T q))
  rw [he]
  exact (historyState_measurable β T M k).comp (Measurable.of_comap_le le_rfl)

theorem actual_query_measurable_pastHistory (β T : ℝ≥0) {M : ℕ} (hM : M≠0) (k : ℕ) (hk : k≤M) :
    Measurable[MeasurableSpace.comap (pastHistory (N:=N) (p:=p) β T M k) inferInstance]
      (SphereEulerSourceApproximation.query β T M k) :=
  SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp
    (actual_node_measurable_pastHistory β T hM k hk)

theorem actual_output_measurable_pastHistory (β T : ℝ≥0) {M : ℕ} (hM : M≠0) :
    Measurable[MeasurableSpace.comap (pastHistory (N:=N) (p:=p) β T M M) inferInstance]
      (output β T M) := actual_query_measurable_pastHistory β T hM M le_rfl

end SphericalAging.SphereEulerStoppedSeed
