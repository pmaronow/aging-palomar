module

public import SphericalAging.ActualSphereGibbsDensity
public import SphericalAging.ActualSphereUniformInitialLaw
public import SphericalAging.SphereSmoothTestMeasureExt

public section

/-! The concrete semigroup density is the literal uniform-initial waiting
law of the genuine sphere SDE, as an equality of probability measures. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereForwardDensityLaw
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open ActualSphereGibbsDensity ActualSphereUniformInitialLaw SphereSmoothTestMeasureExt
open SphericalIntegrationByParts
open scoped NNReal ENNReal Topology
variable {N p : ℕ}

@[expose] def densityLaw (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ≥0) : Measure (State N) :=
  (sphereLaw N).withDensity (fun x => ENNReal.ofReal (forwardDensity β R hR J t x))

theorem forwardDensity_nonneg_ae (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) :
    ∀ᵐx∂sphereLaw N,0≤forwardDensity β R hR J t x := by
  filter_upwards [sphereLaw_support hN] with x hx
  exact (forwardDensity_positive_onSphere hN hp β R hR hNR J t x
    ((onSphere_iff_norm_sq x).mpr hx)).le

theorem densityLaw_probability (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) :
    IsProbabilityMeasure (densityLaw β R hR J t) := by
  constructor
  rw [densityLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal
      (continuous_sphere_integrable hN (forwardDensity_spatial_contDiff hN hp β R hR J t).continuous)
      (forwardDensity_nonneg_ae hN hp β R hR hNR J t),
    forwardDensity_mass_one hN hp β R hR hNR J t]
  simp

theorem densityLaw_sphere_support (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ≥0) :
    ∀ᵐx∂densityLaw β R hR J t,OnSphere x := by
  apply (withDensity_absolutelyContinuous (sphereLaw N) _).ae_le
  exact (sphereLaw_support hN).mono (fun x hx => (onSphere_iff_norm_sq x).mpr hx)

theorem densityLaw_test_integral (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (t : ℝ≥0) (f : State N→ℝ) :
    (∫x,f x ∂densityLaw β R hR J t)=
      ∫x,forwardDensity β R hR J t x*f x ∂sphereLaw N := by
  rw [densityLaw,integral_withDensity_eq_integral_toReal_smul
    ((forwardDensity_spatial_contDiff hN hp β R hR J t).continuous.measurable.ennreal_ofReal)
    (.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [forwardDensity_nonneg_ae hN hp β R hR hNR J t] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul]

/-- Genuine actual waiting-law density realization. No law, density
existence, smoothing, forward equation, or reversibility identity is assumed. -/
theorem waitingLaw_eq_densityLaw (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) :
    waitingLaw β R hR J t=densityLaw β R hR J t := by
  letI := densityLaw_probability hN hp β R hR hNR J t
  apply measure_eq_of_compactC2_integrals
    (waitingLaw_sphere_support hN β R hR hNR J t) (densityLaw_sphere_support hN β R hR J t)
  intro f hf hfc
  rw [waitingLaw_compact_test_integral β R hR J hf.continuous hfc t,
    densityLaw_test_integral hN hp β R hR hNR J t f]
  exact forwardDensity_compact_test_identity hN hp β R hR hNR J hf hfc t

end SphericalAging.ActualSphereForwardDensityLaw
