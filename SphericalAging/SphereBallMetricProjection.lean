module

public import SphericalAging.ConvexMetricProjection
public import SphericalAging.HardSphereDynamics

public section
/-! Actual nonexpansive metric projection onto a Euclidean state ball. -/
noncomputable section
open Set Filter Topology Metric
open scoped NNReal InnerProductSpace
namespace SphericalAging.SphereBallMetricProjection
open HardSphereDynamics
variable {N : ℕ}
@[expose] def project (R : ℝ≥0) : State N → State N :=
  ConvexMetricProjection.project (closedBall 0 (R : ℝ)) isClosed_closedBall (convex_closedBall 0 _)
    ⟨0,by simp only [mem_closedBall,dist_self];exact R.coe_nonneg⟩

theorem project_lipschitz (R : ℝ≥0) : LipschitzWith 1 (project (N := N) R) :=
  ConvexMetricProjection.project_lipschitz _ _ _ _
theorem project_continuous (R : ℝ≥0) : Continuous (project (N := N) R) := (project_lipschitz R).continuous
theorem project_norm_le (R : ℝ≥0) (x : State N) : ‖project R x‖≤R := by
  have hm := ConvexMetricProjection.project_mem (closedBall 0 (R : ℝ)) isClosed_closedBall
    (convex_closedBall 0 _) ⟨0,by simp only [mem_closedBall,dist_self];exact R.coe_nonneg⟩ x
  simpa only [project,mem_closedBall,dist_zero_right] using hm
theorem project_eq_self (R : ℝ≥0) {x : State N} (hx : ‖x‖≤R) : project R x=x :=
  ConvexMetricProjection.project_eq_self _ _ _ _ (by simpa only [mem_closedBall,dist_zero_right] using hx)

@[expose] def doubleRadius (N : ℕ) : ℝ≥0 := ⟨2*Real.sqrt N,by positivity⟩
@[expose] def sphereRadius (N : ℕ) : ℝ≥0 := ⟨Real.sqrt N,Real.sqrt_nonneg _⟩

theorem project_doubleRadius_eq_onSphere (x : State N) (hx : OnSphere x) :
    project (doubleRadius N) x=x := by
  apply project_eq_self
  have hn : ‖x‖=Real.sqrt (N : ℝ) := by
    rw [←(onSphere_iff_norm_sq x).mp hx,Real.sqrt_sq (norm_nonneg _)]
  change ‖x‖≤2*Real.sqrt N
  rw [hn]
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

theorem project_sphereRadius_eq_onSphere (x : State N) (hx : OnSphere x) :
    project (sphereRadius N) x=x := by
  apply project_eq_self
  have hn : ‖x‖=Real.sqrt (N : ℝ) := by
    rw [←(onSphere_iff_norm_sq x).mp hx,Real.sqrt_sq (norm_nonneg _)]
  exact hn.le
end SphericalAging.SphereBallMetricProjection
