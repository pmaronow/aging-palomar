module

public import SphericalAging.SphereOnlyFisherGrowth
public import SphericalAging.ActualSphereForwardDensitySlopeJointC1
public import SphericalAging.ActualForwardFisherMeasurability

public section

/-! Literal actual forward-density Fisher clock and per-time Gaussian
integrability. Every field of the sphere-only calculus interface is
constructed from the genuine diffusion and its spatial jets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SphericalAging.ActualSphereFisherClock
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereRotationGeometry SphereFisherClock SphereCanonicalEntropy
open SphereOnlyForwardCalculus ActualSphereGibbsDensity ActualSphereForwardDensityRegularity
open ActualSphereForwardDensityC3 ActualSphereForwardDensitySlopeC1
open ActualSphereForwardDensitySlopeJointC1 ActualForwardFisherMeasurability
open scoped Topology NNReal
variable {N p : ℕ}

@[expose] def actualForwardData (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) : SphereForwardData N p β J where
  ρ := forwardDensity β R hR J
  ρdot := fun t x => sphericalForwardDensitySlope β J (forwardDensity β R hR J t) x
  joint := forwardDensity_joint_continuous hN hp β R hR J
  jointDot := by
    change Continuous (fun z : ℝ×Vector N => sphericalForwardDensitySlope β J
      (forwardDensity β R hR J z.1) z.2)
    exact forwardDensity_slope_joint_continuous hN hp β R hR J
  jointFirst := forwardDensity_first_joint_continuous hN hp β R hR J
  jointDotFirst := by
    change Continuous (fun z : ℝ×Vector N => fderiv ℝ
      (sphericalForwardDensitySlope β J (forwardDensity β R hR J z.1)) z.2)
    exact forwardDensitySlope_first_joint_continuous hN hp β R hR J
  spatial := forwardDensity_spatial_contDiff_three hN hp β R hR J
  spatialDot := forwardDensitySlope_spatial_contDiff_one hN hp β R hR J
  positive := forwardDensity_positive_onSphere hN hp β R hR hNR J
  timeDerivative := forwardDensity_hasDerivAt_forwardPDE hN hp β R hR hNR J
  spherePDE := fun _ _ _ _ => rfl

theorem actual_forwardDensity_fisher_clock_antitone (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) :
    AntitoneOn (fisherClock β J (forwardDensity β R hR J)) (Ici 0) :=
  (actualForwardData hN (by omega) β R hR hNR J).clock_antitoneOn hN hp β.coe_nonneg

theorem actual_forwardDensity_fisher_exponential_comparison (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    fisherInformation β J (forwardDensity β R hR J t) ≤
      Real.exp (curvatureRate β J*(t-s))*fisherInformation β J (forwardDensity β R hR J s) :=
  (actualForwardData hN (by omega) β R hR hNR J).fisher_exponential_comparison hN hp β.coe_nonneg hs hst

theorem actual_forwardDensity_fisher_growth_bound (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {t : ℝ} (ht : 0≤t) :
    fisherInformation β J (forwardDensity β R hR J t)/(N:ℝ) ≤
      (β:ℝ)^2*(p:ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t) :=
  SphereOnlyFisherGrowth.initial_fisher_growth_bound hN hp β.coe_nonneg J
    (actualForwardData hN (by omega) β R hR hNR J)
    (forwardDensity_initial_onSphere hN (by omega) β R hR hNR J) ht

theorem actual_forwardDensity_fisher_section_measurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ) :
    Measurable (fun J : Disorder N p => fisherInformation β J (forwardDensity β R hR J t)) := by
  have hJoint : Measurable (fun z : Disorder N p×ℝ =>
      fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)) :=
    (forwardDensity_fisher_joint_stronglyMeasurable (N:=N) (p:=p) hN hp β R hR hNR).measurable
  have hArg : Measurable (fun J : Disorder N p => (J,t)) :=
    measurable_id.prodMk measurable_const
  have hComp : Measurable ((fun z : Disorder N p×ℝ =>
      fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)) ∘
      (fun J : Disorder N p => (J,t))) := hJoint.comp hArg
  simpa only [Function.comp_def] using hComp

theorem actual_forwardDensity_fisher_disorder_integrable (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    Integrable (fun J => fisherInformation β J (forwardDensity β R hR J t)/(N:ℝ)) (disorderLaw N p) := by
  have hm := actual_forwardDensity_fisher_section_measurable hN (by omega : 1≤p) β R hR hNR t
  exact SphereOnlyFisherGrowth.fisher_disorder_integrable hN hp β.coe_nonneg
    (fun J => actualForwardData hN (by omega) β R hR hNR J)
    (fun J => forwardDensity_initial_onSphere hN (by omega) β R hR hNR J) ht hm.aestronglyMeasurable

end SphericalAging.ActualSphereFisherClock
