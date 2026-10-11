module

public import SphericalAging.RandomLpHessianSource
public import SphericalAging.OperatorTaylorRemainder

public section

/-! Literal vector Jacobian-source Taylor errors have three quadratic
terms, with no higher derivative or forcing premise. -/
noncomputable section
open scoped NNReal ContDiff
namespace SphericalAging.VectorJacobianVariationError
open HardSphereDynamics RandomLpHessianSource
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance

theorem source_error_bound {g : State N→State N} (hg : ContDiff ℝ ∞ g) {M A : ℝ≥0}
    (hM : LipschitzWith M (fderiv ℝ g))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ g))) (x y d ux uy : State N) :
    ‖fderiv ℝ g y uy-fderiv ℝ g x uy-fderiv ℝ (fderiv ℝ g) x d ux‖≤
    (A:ℝ)*‖y-x‖^2*‖uy‖+(M:ℝ)*‖y-x-d‖*‖uy‖+(M:ℝ)*‖d‖*‖uy-ux‖ := by
  let H := fderiv ℝ (fderiv ℝ g) x
  let C := fderiv ℝ g y-fderiv ℝ g x-H (y-x)
  have hH : ‖H‖≤(M:ℝ) := norm_fderiv_le_of_lipschitz ℝ hM
  have hC : ‖C‖≤(A:ℝ)*‖y-x‖^2 := OperatorTaylorRemainder.taylor_remainder_bound
    (hg.fderiv_right (m:=∞) (by simp)) hA x y
  have he : fderiv ℝ g y uy-fderiv ℝ g x uy-H d ux=C uy+H (y-x-d) uy+H d (uy-ux) := by
    dsimp [C];simp only [map_sub,ContinuousLinearMap.sub_apply];abel
  rw [he]
  have hn : ‖C uy+H (y-x-d) uy+H d (uy-ux)‖≤‖C uy‖+‖H (y-x-d) uy‖+‖H d (uy-ux)‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  exact hn.trans (add_le_add (add_le_add ((C.le_opNorm uy).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))) (bilinear_bound H hH (y-x-d) uy))
    (bilinear_bound H hH d (uy-ux)))
end SphericalAging.VectorJacobianVariationError
