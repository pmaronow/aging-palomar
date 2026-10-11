module

public import SphericalAging.ActualSphereFisherClock
public import SphericalAging.SphereOnlyEntropyDissipation
public import SphericalAging.SphereOnlyAllTimeContinuity
public import Mathlib.Analysis.Calculus.FDeriv.Extend

public section

/-! Genuine time-zero right derivatives of the physical forward density
and relative entropy. Positive-time equations and continuous actual slopes
give the endpoint derivatives; no evolution off the sphere is imposed. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace SphericalAging.ActualSphereForwardZeroEndpoint
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry
open ActualSphereGibbsDensity ActualSphereForwardDensityRegularity ActualSphereFisherClock
open SphereCanonicalEntropy SphereOnlyEntropyDissipation SphereOnlyAllTimeContinuity
open SphereEntropyDissipation
variable {N p : ℕ}

theorem right_derivative_of_continuous_slope {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt f (g t) t) :
    HasDerivWithinAt f (g 0) (Ici 0) 0 := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have he : (fun t => deriv f t) =ᶠ[𝓝[>] (0 : ℝ)] g :=
    hpos.mono fun t ht => (hd t ht).deriv
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioi (0 : ℝ))
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    hf.continuousAt.continuousWithinAt self_mem_nhdsWithin
  exact (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

theorem nonnegative_derivative_of_continuous_slope {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt f (g t) t)
    {t : ℝ} (ht : 0 ≤ t) : HasDerivWithinAt f (g t) (Ici 0) t := by
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    exact right_derivative_of_continuous_slope hf hg hd
  · exact (hd t hpos).hasDerivWithinAt

theorem actual_forwardDensity_hasDerivWithinAt_forwardPDE (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    (J : Disorder N p) {t : ℝ} (ht : 0 ≤ t) {x : Vector N} (hx : OnSphere x) :
    HasDerivWithinAt (fun s => forwardDensity β R hR J s x)
      (sphericalForwardDensitySlope β J (forwardDensity β R hR J t) x) (Ici 0) t := by
  have hρ := (forwardDensity_joint_continuous hN hp β R hR J).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
  have hdot := (forwardDensity_slope_joint_continuous hN hp β R hR J).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
  exact nonnegative_derivative_of_continuous_slope hρ hdot
    (fun s hs => forwardDensity_hasDerivAt_forwardPDE hN hp β R hR hNR J s hs x hx) ht

theorem actual_forwardDensity_entropy_hasDerivWithinAt (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    (J : Disorder N p) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => relativeEntropy β J (forwardDensity β R hR J s))
      (-fisherInformation β J (forwardDensity β R hR J t)) (Ici 0) t := by
  have hρ := forwardDensity_joint_continuous hN hp β R hR J
  have hpos := forwardDensity_positive_onSphere hN hp β R hR hNR J
  have hE := relativeEntropy_continuous hN β J hρ hpos
  have hF := fisher_continuous hN β J hρ
    (forwardDensity_first_joint_continuous hN hp β R hR J)
    (forwardDensity_spatial_contDiff hN hp β R hR J) hpos
  exact nonnegative_derivative_of_continuous_slope hE hF.neg
    (fun s hs => actual_forwardDensity_entropy_hasDerivAt hN hp β R hR hNR J hs) ht

end SphericalAging.ActualSphereForwardZeroEndpoint
