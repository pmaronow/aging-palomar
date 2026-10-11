module

public import SphericalAging.ActualEquilibriumResponseNormalization

public section

/-! Actual Gibbs stationarity and literal Brownian correlation realization
underlying Remark 3.1. Compact transition balance and genuine sphere
preservation yield stationarity; no invariant-law premise is supplied. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualEquilibriumGibbsInvariance
open FiniteModel HardSphereDynamics SphereInitialLaw SphereGibbsEntropy SphereGibbsGenerator
  ActualSphereCompactSemigroup ActualSphereGibbsReversibility ActualSphereGibbsDensity
  ActualEquilibriumFDT ActualSphereMeanSpatialInterface ActualSphereLinearTransition
  ActualSphereTransition SphericalIntegrationByParts
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

 /-- Gibbs averaging is invariant under the true sphere SDE semigroup. -/
 theorem compact_gibbs_transition_stationary (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    (∫x : State N,gibbsDensity N p β J x*realTransition β R hR J f t x ∂sphereLaw N)=
      ∫x : State N,gibbsDensity N p β J x*f x ∂sphereLaw N := by
  have hb : ContDiff ℝ 2 (fun x : State N => coefficientBump (N:=N) R hR x) :=
    (coefficientBump (N:=N) R hR).contDiff
  have hh := compact_transition_reversible hN hp β R hR hNR J hb
    (coefficientBump (N:=N) R hR).hasCompactSupport hf hfc t
  have hleft : (∫x : State N,gibbsDensity N p β J x*
      realTransition β R hR J (coefficientBump (N:=N) R hR) t x*f x ∂sphereLaw N)=
        ∫x : State N,gibbsDensity N p β J x*f x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [SphereOnlyParameterIntegral.physicalSphere_ae hN] with x hx
    rw [realTransition_const_onSphere hN β R hR hNR J _ t 1
      (fun y hy => sphere_coefficientBump_eq_one R hR hNR hy) x hx,mul_one]
  have hright : (∫x : State N,gibbsDensity N p β J x*
      coefficientBump (N:=N) R hR x*realTransition β R hR J f t x ∂sphereLaw N)=
        ∫x : State N,gibbsDensity N p β J x*realTransition β R hR J f t x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [SphereOnlyParameterIntegral.physicalSphere_ae hN] with x hx
    rw [sphere_coefficientBump_eq_one R hR hNR hx,mul_one]
  rw [hleft,hright] at hh
  exact hh.symm

 /-- The equilibrium correlation is the literal expected overlap of the
actual SDE with its Gibbs-distributed initial state. -/
 theorem equilibriumCorrelation_eq_actual_brownian_pairing (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ≥0) :
    equilibriumCorrelation β R hR J τ=
      (∫x : State N,gibbsDensity N p β J x*
        (∫ω,⟪x,jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR (J,x) τ ω⟫_ℝ ∂VectorBrownian.law N) ∂sphereLaw N)/(N:ℝ) := by
  rw [equilibriumCorrelation_eq_inner hN β R hR J]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun x => by
    dsimp only
    have he := transition_inner_eq_mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J τ x x
    unfold realMean
    rw [Real.toNNReal_coe,←he]
    rfl)

end SphericalAging.ActualEquilibriumGibbsInvariance
