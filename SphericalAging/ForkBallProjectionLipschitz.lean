module

public import SphericalAging.ForkBallProjection
public import SphericalAging.SphereBallMetricProjection

public section

/-! The literal radial clipping map used for finite fork algorithms is
exactly the Hilbert metric projection, hence genuinely nonexpansive. -/
noncomputable section
open Set Metric
open scoped NNReal InnerProductSpace
namespace SphericalAging.ForkBallProjectionLipschitz
open ForkBallProjection ConvexMetricProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem clip_inner_le {R : ℝ} (hR : 0≤R) (x z : E) (hz : ‖z‖≤R) :
    ⟪x-clip R x,z-clip R x⟫_ℝ≤0 := by
  by_cases hx : ‖x‖≤R
  · simp only [clip,if_pos hx,sub_self,inner_zero_left,le_refl]
  · have hn : 0<‖x‖ := hR.trans_lt (lt_of_not_ge hx)
    let c := R/‖x‖
    have hc : c≤1 := (div_le_one hn).mpr (lt_of_not_ge hx).le
    have he : x-c • x=(1-c) • x := by rw [sub_smul,one_smul]
    have hinner : ⟪x,z⟫_ℝ≤‖x‖*R :=
      ((le_abs_self _).trans (abs_real_inner_le_norm x z)).trans
        (mul_le_mul_of_nonneg_left hz (norm_nonneg x))
    have hmul : c*‖x‖^2=‖x‖*R := by
      dsimp only [c]
      field_simp
    rw [clip,if_neg hx]
    change ⟪x-c • x,z-c • x⟫_ℝ≤0
    rw [he,real_inner_smul_left,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) (by rw [hmul];linarith)

theorem clip_eq_metricProjection (R : ℝ≥0) (x : E) :
    clip (R:ℝ) x=ConvexMetricProjection.project (closedBall 0 (R:ℝ))
      isClosed_closedBall (convex_closedBall 0 _) ⟨0,by simpa using R.coe_nonneg⟩ x := by
  let q := ConvexMetricProjection.project (closedBall 0 (R:ℝ))
    isClosed_closedBall (convex_closedBall 0 _) ⟨0,by simpa using R.coe_nonneg⟩ x
  let p := clip (R:ℝ) x
  have hq : ‖q‖≤R := by
    simpa only [mem_closedBall,dist_zero_right] using
      ConvexMetricProjection.project_mem (closedBall 0 (R:ℝ)) isClosed_closedBall
        (convex_closedBall 0 _) ⟨0,by simpa using R.coe_nonneg⟩ x
  have hp : ‖p‖≤R := clip_norm_le R.coe_nonneg x
  have h1 : ⟪x-p,q-p⟫_ℝ≤0 := clip_inner_le R.coe_nonneg x q hq
  have h2 : ⟪x-q,p-q⟫_ℝ≤0 :=
    ConvexMetricProjection.project_inner_le (closedBall 0 (R:ℝ)) isClosed_closedBall
      (convex_closedBall 0 _) ⟨0,by simpa using R.coe_nonneg⟩ x p
        (by simpa only [mem_closedBall,dist_zero_right] using hp)
  have h1' : 0≤⟪x-p,p-q⟫_ℝ := by
    rw [show q-p= -(p-q) by abel,inner_neg_right] at h1
    linarith
  have hh : ‖p-q‖^2≤0 := by
    rw [show x-q=(x-p)+(p-q) by abel,inner_add_left,real_inner_self_eq_norm_sq] at h2
    linarith
  have hz : ‖p-q‖=0 := by nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem clip_lipschitz (R : ℝ≥0) : LipschitzWith 1 (clip (E:=E) (R:ℝ)) := by
  rw [show clip (E:=E) (R:ℝ)=ConvexMetricProjection.project (closedBall 0 (R:ℝ))
    isClosed_closedBall (convex_closedBall 0 _) ⟨0,by simpa using R.coe_nonneg⟩ from
      funext (clip_eq_metricProjection R)]
  exact ConvexMetricProjection.project_lipschitz _ _ _ _

theorem clip_sphereRadius_eq {N : ℕ} (x : HardSphereDynamics.State N) :
    clip (Real.sqrt N) x=SphereBallMetricProjection.project (SphereBallMetricProjection.sphereRadius N) x :=
  clip_eq_metricProjection (SphereBallMetricProjection.sphereRadius N) x

end SphericalAging.ForkBallProjectionLipschitz
