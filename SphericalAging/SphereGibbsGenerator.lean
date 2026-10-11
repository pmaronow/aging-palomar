module

public import SphericalAging.SphereCanonicalGenerator
public import SphericalAging.SphereFDTAlgebra

public section

/-! A genuine equilibrium elliptic-generator foundation: the constructed
normalized Gibbs density has zero forward flux, and the actual sphere SDE
coefficient generator has the exact symmetric negative Dirichlet form.
These facts do not assert existence of a nonstationary transition density. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ContDiff
namespace SphericalAging.SphereGibbsGenerator
open FiniteModel HardSphereDynamics SphereInitialLaw SphereGibbsEntropy
open SphericalIntegrationByParts SphereEntropyDissipation SphereGeneratorIntegrationByParts
open SphereForwardAdjoint SphereCanonicalGenerator SphereRotationGeometry
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- The actual finite normalized Gibbs density has a smooth ambient extension. -/
theorem gibbsDensity_contDiff (β : ℝ) (J : Disorder N p) :
    ContDiff ℝ ∞ (gibbsDensity N p β J) := by
  unfold gibbsDensity
  exact ((contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp))).exp).div_const _

/-- The actual logarithmic ratio of Gibbs density against itself is zero. -/
theorem relativeLog_gibbs_zero (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) :
    relativeLog β J (gibbsDensity N p β J)=(fun _ => 0) := by
  funext x
  have hh := negative_log_gibbsDensity hN hp hβ J x
  unfold relativeLog
  linarith

/-- Every actual Gibbs rotation flux vanishes pointwise. -/
theorem gibbs_rotationFlux_zero (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) (A : Operator N) :
    rotationFlux β J A (gibbsDensity N p β J)=(fun _ => 0) := by
  funext x
  have he := relativeLog_lieDerivative β J A
    ((gibbsDensity_contDiff β J).of_le (by simp)) (gibbsDensity_positive hN hp hβ J) x
  rw [relativeLog_gibbs_zero hN hp hβ J,lieDerivative_const] at he
  exact (div_eq_zero_iff).mp he.symm |>.resolve_right (gibbsDensity_positive hN hp hβ J x).ne'

/-- The constructed Gibbs density solves the actual forward density
operator at equilibrium, derived from its genuine exponential formula. -/
theorem gibbs_forwardDensitySlope_zero {ι : Type*} [Fintype ι]
    (hN : 0<N) (hp : 1≤p) (κ : ℝ) {β : ℝ} (hβ : 0≤β)
    (J : Disorder N p) (A : ι → Operator N) :
    forwardDensitySlope κ β J A (gibbsDensity N p β J)=(fun _ => 0) := by
  funext x
  simp [forwardDensitySlope,gibbs_rotationFlux_zero hN hp hβ J,lieDerivative_const]

/-- Exact actual Gibbs generator integration by parts, with no residual
current because the constructed equilibrium flux is truly zero. -/
theorem gibbs_rotationGenerator_ibp {ι : Type*} [Fintype ι]
    (hN : 0<N) (hp : 1≤p) (κ : ℝ) {β : ℝ} (hβ : 0≤β)
    (J : Disorder N p) (A : ι → Operator N) (hA : ∀ i,star (A i)=-A i)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    (∫ x : Vector N,gibbsDensity N p β J x*f x*rotationGenerator κ β J A g x ∂sphereLaw N)=
      -(∫ x : Vector N,gibbsDensity N p β J x*rotationGamma κ A f g x ∂sphereLaw N) := by
  have he := weighted_generator_current_ibp hN κ β J A hA
    ((gibbsDensity_contDiff β J).of_le (by simp)) (gibbsDensity_positive hN hp hβ J) hf hg
  simpa only [relativeLog_gibbs_zero hN hp hβ J,rotationGamma,lieDerivative_const,
    zero_mul,Finset.sum_const_zero,mul_zero,integral_zero,sub_zero] using he

/-- The actual coefficient generator of the sphere SDE has the exact
Gibbs-weighted tangent Dirichlet form. -/
theorem gibbs_coefficientGenerator_ibp (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ x : Vector N,gibbsDensity N p β J x*f x*SphereGenerator.coefficientGenerator β J g x ∂sphereLaw N)=
      -(∫ x : Vector N,gibbsDensity N p β J x*
        ⟪projection x (gradient f x),projection x (gradient g x)⟫_ℝ ∂sphereLaw N) := by
  have he := gibbs_rotationGenerator_ibp hN hp (1/(2*(N : ℝ))) hβ J
    (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2)
    (fun ij => coordinateRotation_skew ij.1 ij.2) (hf.of_le (by norm_num)) hg
  have hgib : ∀ᵐ x ∂sphereLaw N,OnSphere x := by
    simpa only [OnSphere,real_inner_self_eq_norm_sq] using sphereLaw_support hN
  have hL : (fun x : Vector N => gibbsDensity N p β J x*f x*
      rotationGenerator (1/(2*(N : ℝ))) β J
        (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) g x)=ᵐ[sphereLaw N]
      fun x => gibbsDensity N p β J x*f x*SphereGenerator.coefficientGenerator β J g x := by
    filter_upwards [hgib] with x hx
    rw [canonical_rotationGenerator_eq_coefficientGenerator hN β J hg x hx]
  have hG : (fun x : Vector N => gibbsDensity N p β J x*
      rotationGamma (1/(2*(N : ℝ)))
        (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) f g x)=ᵐ[sphereLaw N]
      fun x => gibbsDensity N p β J x*
        ⟪projection x (gradient f x),projection x (gradient g x)⟫_ℝ := by
    filter_upwards [hgib] with x hx
    rw [canonical_rotationGamma_eq_tangent_inner hN f g x hx]
  rw [integral_congr_ae hL,integral_congr_ae hG] at he
  exact he

/-- Genuine weak stationarity of the constructed Gibbs measure for the
actual SDE generator; this is an equilibrium elliptic foundation. -/
theorem gibbs_coefficientGenerator_mean_zero (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p)
    {g : Vector N → ℝ} (hg : ContDiff ℝ 2 g) :
    (∫ x : Vector N,gibbsDensity N p β J x*SphereGenerator.coefficientGenerator β J g x ∂sphereLaw N)=0 := by
  have he := gibbs_rotationGenerator_ibp hN hp (1/(2*(N : ℝ))) hβ J
    (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2)
    (fun ij => coordinateRotation_skew ij.1 ij.2)
    (f := fun _ : Vector N => 1) contDiff_const hg
  have hz : rotationGamma (1/(2*(N : ℝ)))
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) (fun _ : Vector N => 1) g=(fun _ => 0) := by
    funext x
    simp [rotationGamma,lieDerivative_const]
  simp only [mul_one,hz,mul_zero,integral_zero,neg_zero] at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hx' : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  rw [canonical_rotationGenerator_eq_coefficientGenerator hN β J hg x hx']

/-- The actual generator is symmetric on smooth functions in the genuine
normalized Gibbs pairing. -/
theorem gibbs_coefficientGenerator_symmetric (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ x : Vector N,gibbsDensity N p β J x*f x*SphereGenerator.coefficientGenerator β J g x ∂sphereLaw N)=
      (∫ x : Vector N,gibbsDensity N p β J x*g x*SphereGenerator.coefficientGenerator β J f x ∂sphereLaw N) := by
  rw [gibbs_coefficientGenerator_ibp hN hp hβ J hf hg,
    gibbs_coefficientGenerator_ibp hN hp hβ J hg hf]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun x => by dsimp only; rw [real_inner_comm])

/-- The actual Gibbs generator quadratic form is nonpositive, with its
full tangent energy identified rather than postulated. -/
theorem gibbs_coefficientGenerator_nonpositive (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ x : Vector N,gibbsDensity N p β J x*f x*SphereGenerator.coefficientGenerator β J f x ∂sphereLaw N)≤0 := by
  rw [gibbs_coefficientGenerator_ibp hN hp hβ J hf hf]
  exact neg_nonpos.mpr (integral_nonneg (fun x =>
    mul_nonneg (gibbsDensity_positive hN hp hβ J x).le real_inner_self_nonneg))

end SphericalAging.SphereGibbsGenerator
