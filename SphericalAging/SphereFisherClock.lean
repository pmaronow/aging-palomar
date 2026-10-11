module

public import SphericalAging.SphereGamma2Drift
public import SphericalAging.SphereFisherTimeDerivative
public import SphericalAging.SphereIntegratedFDT
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

public section

/-! The actual smooth positive forward density obeys the genuine spherical
Fisher differential comparison. The curvature lower bound is proved from the
canonical rotations and intrinsic Hamiltonian Hessian in SphereGamma2Drift. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFisherClock

open MeasureTheory Set FiniteModel SphereInitialLaw SphereRotationGeometry
open SphereFisherDissipation SphereFisherTimeDerivative SphereGamma2Drift SphereCasimirGamma2
open SphereGeneratorIntegrationByParts SphereEntropyDissipation SphereCanonicalEntropy
open SphereIntegratedFDT SphericalIntegrationByParts SphereFDTAlgebra
open SphereFiniteFDT SphereLogDensityEquation SphereEntropyBudget SphereMixedDerivatives
open scoped Topology

@[expose] def curvatureRate {N p : ℕ} (β : ℝ) (J : Disorder N p) : ℝ :=
  2*β*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J

@[expose] def fisherClock {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : ℝ → Vector N → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-curvatureRate β J*t)*fisherInformation β J (ρ t)

theorem spherical_fisher_continuous {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ → Vector N → ℝ} (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x) :
    Continuous (fun t => fisherInformation β J (ρ t)) := by
  unfold fisherInformation
  exact continuous_sphere_parameter_integral hN
    (hρ.continuous.mul ((joint_tangentScore_continuous β J hρ hpos).norm.pow 2))

theorem rotationGamma2_continuous {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) :
    Continuous (rotationGamma2 κ β J A f) := by
  have hG : ContDiff ℝ 2 (rotationGamma κ A f f) := rotationGamma_contDiff_order κ A hf hf
  unfold rotationGamma2
  exact continuous_const.mul ((rotationGenerator_continuous κ β J A hG).sub
    (continuous_const.mul (rotationGamma_continuous κ A (hf.of_le (by norm_num))
      (rotationGenerator_contDiff_one κ β J A hf))))

/-- True spherical Fisher slope I'≤2βp²‖J‖I, with its exact source rate. -/
theorem spherical_fisher_deriv_le {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (t : ℝ) (hPDE : ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x) :
    deriv (fun s => fisherInformation β J (ρ s)) t ≤
      curvatureRate β J*fisherInformation β J (ρ t) := by
  let C : ℝ := β*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J
  have hsp : ContDiff ℝ 3 (ρ t) := by
    simpa only [Function.comp_def, Function.uncurry, id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 3 (fun x : Vector N => (t,x)))
  have hψ : ContDiff ℝ 3 (relativeLog β J (ρ t)) :=
    ((hsp.log (fun x => (hpos t x).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  have hG : Continuous (rotationGamma (1/(2*(N : ℝ))) (rotations N)
      (relativeLog β J (ρ t)) (relativeLog β J (ρ t))) :=
    rotationGamma_continuous _ _ (hψ.of_le (by norm_num)) (hψ.of_le (by norm_num))
  have hG₂ := rotationGamma2_continuous (1/(2*(N : ℝ))) β J (rotations N) hψ
  have hi₁ := continuous_sphere_integrable hN (hsp.continuous.mul hG)
  have hi₂ := continuous_sphere_integrable hN (hsp.continuous.mul hG₂)
  have hpoint : ∀ᵐ x ∂sphereLaw N,
      -C*(ρ t x*rotationGamma (1/(2*(N : ℝ))) (rotations N)
        (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x) ≤
      ρ t x*rotationGamma2 (1/(2*(N : ℝ))) β J (rotations N) (relativeLog β J (ρ t)) x := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hs : HardSphereDynamics.OnSphere x := by
      simpa only [HardSphereDynamics.OnSphere, real_inner_self_eq_norm_sq] using hx
    have hh := mul_le_mul_of_nonneg_left
      (canonical_rotationGamma2_curvature_lower_bound hN hp hβ J hψ x hs) (hpos t x).le
    dsimp only [C]
    convert hh using 1
    ring
  have hmono := integral_mono_ae (hi₁.const_mul (-C)) hi₂ hpoint
  rw [integral_const_mul] at hmono
  change -C*(∫ x : Vector N,ρ t x*rotationGamma (1/(2*(N : ℝ))) (rotations N)
      (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x ∂sphereLaw N) ≤
    (∫ x : Vector N,ρ t x*rotationGamma2 (1/(2*(N : ℝ))) β J (rotations N)
      (relativeLog β J (ρ t)) x ∂sphereLaw N) at hmono
  have hmetric : (∫ x : Vector N,ρ t x*rotationGamma (1/(2*(N : ℝ))) (rotations N)
      (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x ∂sphereLaw N) =
      fisherInformation β J (ρ t) := by
    unfold fisherInformation tangentScore
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    have hs : HardSphereDynamics.OnSphere x := by
      simpa only [HardSphereDynamics.OnSphere, real_inner_self_eq_norm_sq] using hx
    rw [SphereCanonicalGenerator.canonical_rotationGamma_eq_tangent_inner hN _ _ x hs,
      real_inner_self_eq_norm_sq]
  rw [hmetric] at hmono
  have hd := spherical_fisher_hasDerivAt_gamma2 hN β J hρ hpos t hPDE
  rw [hd.deriv]
  dsimp only [C] at hmono
  unfold curvatureRate
  nlinarith only [hmono]

theorem fisherClock_hasDerivAt {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ → Vector N → ℝ} (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (t : ℝ) (hPDE : ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x) :
    HasDerivAt (fisherClock β J ρ)
      (Real.exp (-curvatureRate β J*t) *
        (deriv (fun s => fisherInformation β J (ρ s)) t - curvatureRate β J*fisherInformation β J (ρ t))) t := by
  have hd := spherical_fisher_hasDerivAt_gamma2 hN β J hρ hpos t hPDE
  have hi := hd.differentiableAt.hasDerivAt
  have he := ((hasDerivAt_id t).const_mul (-curvatureRate β J)).exp
  have he' : HasDerivAt (fun s => Real.exp (-curvatureRate β J*s))
      (Real.exp (-curvatureRate β J*t)*(-curvatureRate β J)) t := by
    simpa only [id_eq, mul_one] using he
  unfold fisherClock
  convert he'.fun_mul hi using 1
  ring

/-- The genuine exponentially weighted Fisher clock decreases on nonnegative
time for the actual forward density equation. -/
theorem fisherClock_antitoneOn {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x) :
    AntitoneOn (fisherClock β J ρ) (Ici 0) := by
  have hc : Continuous (fisherClock β J ρ) := by
    unfold fisherClock
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (spherical_fisher_continuous hN β J (hρ.of_le (by norm_num)) hpos)
  have hd t (ht : 0≤t) := fisherClock_hasDerivAt hN β J hρ hpos t (hPDE t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hc.continuousOn
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (spherical_fisher_deriv_le hN hp hβ J hρ hpos t (hPDE t (interior_subset ht))))

/-- True pointwise Fisher comparison between any two nonnegative times. -/
theorem spherical_fisher_exponential_comparison {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    fisherInformation β J (ρ t) ≤
      Real.exp (curvatureRate β J*(t-s))*fisherInformation β J (ρ s) := by
  have hh := fisherClock_antitoneOn hN hp hβ J hρ hpos hPDE hs (hs.trans hst) hst
  unfold fisherClock at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (curvatureRate β J*t)).le
  have he₁ : Real.exp (curvatureRate β J*t)*Real.exp (-curvatureRate β J*t)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have he₂ : Real.exp (curvatureRate β J*t)*Real.exp (-curvatureRate β J*s)=
      Real.exp (curvatureRate β J*(t-s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc, he₁, he₂, one_mul] using hm

theorem spherical_fisher_normalized_exponential_comparison {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    fisherInformation β J (ρ t)/(N : ℝ) ≤
      Real.exp (curvatureRate β J*(t-s))*(fisherInformation β J (ρ s)/(N : ℝ)) := by
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
    (spherical_fisher_exponential_comparison hN hp hβ J hρ hpos hPDE hs hst) (Nat.cast_nonneg N)

end SphericalAging.SphereFisherClock
