module

public import SphericalAging.SphereFisherCurrent
public import SphericalAging.LandscapeSphereGeometry

public section

/-! The initial uniform density has the actual Hamiltonian tangent score and
the genuine normalized quenched Fisher bound needed for the Fisher clock. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereInitialFisher

open MeasureTheory FiniteModel SphereInitialLaw SphereGibbsEntropy SphereEntropyDissipation
open SphereRotationGeometry SphereFisherCurrent LandscapeDerivatives HardSphereDynamics
open SphericalIntegrationByParts
open scoped InnerProductSpace

theorem relativeLog_uniform_gradient {N p : ℕ} (β : ℝ) (J : Disorder N p) (x : Vector N) :
    gradient (relativeLog β J (fun _ => 1)) x = -β • gradient (Hamiltonian N p J) x := by
  have hH : DifferentiableAt ℝ (Hamiltonian N p J) x := (Hamiltonian_contDiff J).differentiable (by simp) x
  have hd := ((hasFDerivAt_const (0 : ℝ) x).fun_sub (hH.hasFDerivAt.const_mul β)).fun_add
    (hasFDerivAt_const (Real.log (partitionFunction N p β J)) x)
  have he : relativeLog β J (fun _ => 1) =
      (fun y => 0-β*Hamiltonian N p J y+Real.log (partitionFunction N p β J)) := by
    funext y
    simp [relativeLog]
  unfold gradient
  rw [he, hd.fderiv]
  simp only [zero_sub, add_zero, map_neg, map_smul]
  rw [neg_smul]

theorem tangentScore_uniform {N p : ℕ} (β : ℝ) (J : Disorder N p) (x : Vector N) :
    tangentScore β J (fun _ => 1) x = -β • projection x (gradient (Hamiltonian N p J) x) := by
  unfold tangentScore
  rw [relativeLog_uniform_gradient, projection_smul]

theorem fisherInformation_uniform_eq {N p : ℕ} (β : ℝ) (J : Disorder N p) :
    fisherInformation β J (fun _ => 1) =
      β^2*(∫ x : Vector N,‖projection x (gradient (Hamiltonian N p J) x)‖^2 ∂sphereLaw N) := by
  unfold fisherInformation
  simp_rw [tangentScore_uniform, one_mul, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, neg_sq]
  exact integral_const_mul _ _

theorem Hamiltonian_tangent_gradient_sq_bound {N p : ℕ} (hN : 0<N)
    (J : Disorder N p) (x : Vector N) (hx : OnSphere x) :
    ‖projection x (gradient (Hamiltonian N p J) x)‖^2 ≤
      (p : ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*(N : ℝ) := by
  have hsqrt : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hg := (div_le_iff₀ hsqrt).mp (Hamiltonian_gradient_sphere_bound hN J x
    ((onSphere_iff_norm_sq x).mp hx))
  have hn := (projection_norm_le_onSphere (Nat.ne_of_gt hN) x (gradient (Hamiltonian N p J) x) hx).trans hg
  have hbound : 0≤(p : ℝ)*GaussianLandscape.landscapeNorm N p J*Real.sqrt (N : ℝ) := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (GaussianLandscape.landscapeNorm_nonnegative N p J)) hsqrt.le
  have hh := (sq_le_sq₀ (norm_nonneg _) hbound).mpr hn
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at hh
  exact hh

/-- The actual initial Fisher information has the uniform quenched landscape
bound, with no covariance or Fisher estimate supplied as a premise. -/
theorem initial_fisher_normalized_quenched_bound {N p : ℕ} (hN : 0<N)
    (β : ℝ) (J : Disorder N p) :
    fisherInformation β J (fun _ => 1)/(N : ℝ) ≤
      β^2*(p : ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2 := by
  have hgrad : Continuous (fun x : Vector N => projection x (gradient (Hamiltonian N p J) x)) := by
    have hg : Continuous (gradient (Hamiltonian N p J)) := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
        ((Hamiltonian_contDiff J).continuous_fderiv (by simp))
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N : ℝ)).smul continuous_id)
  have hm := integral_mono_ae (continuous_sphere_integrable hN (hgrad.norm.pow 2))
    (integrable_const ((p : ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*(N : ℝ)))
    (show ∀ᵐ x ∂sphereLaw N,‖projection x (gradient (Hamiltonian N p J) x)‖^2 ≤
      (p : ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*(N : ℝ) from by
        filter_upwards [sphereLaw_support hN] with x hx
        exact Hamiltonian_tangent_gradient_sq_bound hN J x ((onSphere_iff_norm_sq x).mpr hx))
  simp only [integral_const, Measure.real, IsProbabilityMeasure.measure_univ,
    ENNReal.toReal_one, one_smul] at hm
  rw [fisherInformation_uniform_eq]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  exact (mul_le_mul_of_nonneg_left hm (sq_nonneg β)).trans_eq (by ring)

end SphericalAging.SphereInitialFisher
