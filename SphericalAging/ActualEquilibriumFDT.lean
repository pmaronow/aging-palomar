module

public import SphericalAging.ActualSphereOnlyFDT
public import SphericalAging.ActualSphereGibbsReversibility
public import SphericalAging.ActualExpectedTwoTimeResponse

public section

/-! Remark 3.1: actual Gibbs equilibrium FDT in the manuscript's force
normalization. The backward mean comes from the genuine sphere diffusion,
and the Gibbs current vanishes by its proved exponential density formula. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualEquilibriumFDT
open FiniteModel HardSphereDynamics SphereInitialLaw SphereGibbsEntropy
  SphereQuenchedFDT SphereFisherCurrent SphereRotationGeometry SphereEntropyDissipation
  SphereGibbsGenerator ActualSphereMeanSpatialInterface ActualSphereMeanBackward
  SphereOnlyOnSphereFDT SphereCoordinateScore SphereGeneratorIntegrationByParts
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

@[expose]  def equilibriumCorrelation (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ) : ℝ :=
  quenchedCorrelation (fun _ => gibbsDensity N p β J) (realMean β R hR J) τ 0

@[expose]  def equilibriumResponse (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ) : ℝ :=
  SphereQuenchedFDT.quenchedResponse (fun _ => gibbsDensity N p β J) (realMean β R hR J) τ 0

 theorem gibbs_current_zero (hN : 0<N) (hp : 1≤p) (β : ℝ≥0) (J : Disorder N p)
    (m : State N→State N) : currentDefect β J (gibbsDensity N p β J) m=0 := by
  unfold currentDefect tangentScore
  rw [relativeLog_gibbs_zero hN hp β.coe_nonneg J]
  simp only [gradient_fun_const',projection,inner_zero_right,zero_div,zero_smul,sub_zero,
    inner_zero_right,mul_zero,integral_zero,zero_div]

 theorem equilibriumCorrelation_eq_inner (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ) :
    equilibriumCorrelation β R hR J τ=
      (∫x : State N,gibbsDensity N p β J x*⟪x,realMean β R hR J τ x⟫_ℝ ∂sphereLaw N)/(N:ℝ) := by
  simpa only [equilibriumCorrelation,sub_zero] using quenchedCorrelation_eq_inner (ρ:=fun _ : ℝ => gibbsDensity N p β J) hN
    ((gibbsDensity_contDiff β J).continuous.comp continuous_snd)
      (realMean_joint_continuous β R hR J) τ 0

 theorem equilibriumCorrelation_lag (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t s : ℝ) :
    quenchedCorrelation (fun _ => gibbsDensity N p β J) (realMean β R hR J) t s=
      equilibriumCorrelation β R hR J (t-s) := by
  simp only [equilibriumCorrelation,quenchedCorrelation,SphereFiniteFDT.correlationPairing,sub_zero]

 theorem equilibriumResponse_lag (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t s : ℝ) :
    SphereQuenchedFDT.quenchedResponse (fun _ => gibbsDensity N p β J) (realMean β R hR J) t s=
      equilibriumResponse β R hR J (t-s) := by
  simp only [equilibriumResponse,SphereQuenchedFDT.quenchedResponse,sub_zero]

 /-- The actual Gibbs correlation has derivative minus actual force response.
There is no β factor because the perturbing force has coefficient one. -/
 theorem equilibrium_fdt_hasDerivAt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {τ : ℝ} (hτ : 0<τ) :
    HasDerivAt (equilibriumCorrelation β R hR J) (-equilibriumResponse β R hR J τ) τ := by
  have hh := quenched_fdt_hasDerivAt_onSphere hN β J
    (ρ:=fun _ => gibbsDensity N p β J) (ρdot:=fun _ _ => 0) (m:=realMean β R hR J)
    ((gibbsDensity_contDiff β J).continuous.comp continuous_snd)
    (fun _ => (gibbsDensity_contDiff β J).of_le (by simp)) continuous_const
    (fun v _ x _ => hasDerivAt_const v (gibbsDensity N p β J x))
    (realMean_joint_continuous β R hR J) (realMean_spatial_contDiff β R hR J)
    (realMean_coordinate_generator_joint_continuous β R hR J)
    (fun i v hv x hx => mean_coordinate_backward_canonical_hasDerivAt
      (Nat.ne_of_gt hN) β R hR hNR J i v hv x hx)
    (t:=τ+1) (s:=1) (by norm_num) (by linarith)
    (fun x _ => gibbsDensity_positive hN hp β.coe_nonneg J x)
    (fun x _ => by
      have he := congrFun (gibbs_forwardDensitySlope_zero hN hp (1/(2*(N:ℝ)))
        β.coe_nonneg J (canonicalRotations N)) x
      exact he.symm)
  rw [gibbs_current_zero hN hp β J,sub_zero,equilibriumResponse_lag] at hh
  have hc := hh.comp_of_eq τ ((hasDerivAt_id τ).const_sub (τ+1)) (by ring : (1:ℝ)=τ+1-τ)
  have he : (fun v => quenchedCorrelation (fun _ => gibbsDensity N p β J)
      (realMean β R hR J) (τ+1) ((τ+1)-v))=equilibriumCorrelation β R hR J := by
    funext v
    rw [equilibriumCorrelation_lag]
    congr 1
    ring
  simpa only [Function.comp_def,id_eq,he,add_sub_cancel_right,mul_neg_one] using hc

 theorem equilibrium_fdt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {τ : ℝ} (hτ : 0<τ) :
    equilibriumResponse β R hR J τ=-deriv (equilibriumCorrelation β R hR J) τ := by
  rw [(equilibrium_fdt_hasDerivAt hN hp β R hR hNR J hτ).deriv]
  simp only [neg_neg]

 /-- Multiplying the perturbing force by β multiplies its linear response
by β, giving the other stated convention. -/
 theorem beta_force_equilibrium_fdt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {τ : ℝ} (hτ : 0<τ) :
    (β:ℝ)*equilibriumResponse β R hR J τ=-(β:ℝ)*deriv (equilibriumCorrelation β R hR J) τ := by
  rw [equilibrium_fdt hN hp β R hR hNR J hτ]
  ring

end SphericalAging.ActualEquilibriumFDT
