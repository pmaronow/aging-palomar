module

public import SphericalAging.LandscapeSphereGeometry
public import SphericalAging.SphereRotationGeometry

public section

/-! The actual intrinsic Hamiltonian Hessian has the required quadratic-form
bound. This provides the landscape part of the spherical Bakry–Émery curvature
estimate; identifying the iterated carré du champ with the Bochner expression
remains separate. -/
noncomputable section
open scoped InnerProductSpace
namespace SphericalAging.SphereCurvatureHessianBound

open FiniteModel LandscapeDerivatives HardSphereDynamics SphereRotationGeometry

theorem sphericalHessian_quadratic_abs_bound {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (J : Disorder N p) (x v : Vector N) (hx : OnSphere x) :
    |⟪v, sphericalHessian J x v⟫_ℝ| ≤
      (p : ℝ)^2 * GaussianLandscape.landscapeNorm N p J * ‖v‖^2 := by
  have hb := sphericalHessian_sphere_bound hN hp J x
    ((onSphere_iff_norm_sq x).mp hx)
  calc
    _ ≤ ‖v‖ * ‖sphericalHessian J x v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖sphericalHessian J x‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((sphericalHessian J x).le_opNorm v) (norm_nonneg v)
    _ ≤ ‖v‖ * (((p : ℝ)^2 * GaussianLandscape.landscapeNorm N p J) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (norm_nonneg v)) (norm_nonneg v)
    _ = _ := by ring

theorem sphericalHessian_quadratic_upper_bound {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (J : Disorder N p) (x v : Vector N) (hx : OnSphere x) :
    ⟪v, sphericalHessian J x v⟫_ℝ ≤
      (p : ℝ)^2 * GaussianLandscape.landscapeNorm N p J * ‖v‖^2 :=
  (le_abs_self _).trans (sphericalHessian_quadratic_abs_bound hN hp J x v hx)

theorem sphericalHessian_drift_lower_bound {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    {β : ℝ} (hβ : 0 ≤ β) (J : Disorder N p) (x v : Vector N) (hx : OnSphere x) :
    -β * ((p : ℝ)^2 * GaussianLandscape.landscapeNorm N p J) * ‖v‖^2 ≤
      -β * ⟪v, sphericalHessian J x v⟫_ℝ := by
  have hh := mul_le_mul_of_nonpos_left
    (sphericalHessian_quadratic_upper_bound hN hp J x v hx) (neg_nonpos.mpr hβ)
  simpa only [mul_assoc] using hh

end SphericalAging.SphereCurvatureHessianBound
