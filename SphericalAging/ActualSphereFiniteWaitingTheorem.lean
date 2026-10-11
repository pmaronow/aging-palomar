module

public import SphericalAging.ActualSphereWaitingCurrent
public import SphericalAging.SphereActualWaitingCurrent
public import SphericalAging.ActualSphereDensityCorrelation

public section

/-! The finite part of source 5.5 for the constructed spherical diffusion.
The actual density is used directly. Its waiting derivative at zero is a
physical right derivative, obtained from the exact current integral. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SphericalAging.ActualSphereFiniteWaitingTheorem

open Set Filter MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics
open ActualSphereWaitingCurrent ActualSphereMeanSpatialInterface
open ActualSphereGibbsDensity ActualSphereFisherClock SphereSharpMeanGradient
open SphereWaitingCurrent SphereRotationGeometry ActualSphereTransition
open LandscapeDerivatives
open scoped Topology InnerProductSpace NNReal

variable {N p : ℕ}

/-- The waiting observable is literally the physical same-path overlap,
with the uniform sphere initial state and genuine Brownian law. -/
theorem actual_waitingCovariance_eq_samePathMoment (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) (τ w : ℝ≥0) :
    waitingCovariance β R hR J τ w =
      ActualSphereForkEndpoints.samePathMoment (k := 1) β R hR J w τ := by
  have he := ActualSphereDensityCorrelation.densityCorrelation_eq_samePathMoment
    hN hp β R hR hNR J (w+τ) w (le_add_of_nonneg_right (by exact bot_le))
  simpa only [waitingCovariance, NNReal.coe_add, add_tsub_cancel_left] using he

/-- The true current primitive agrees on nonnegative times with an ordinary
smooth primitive. Thus its derivative exists within physical time at zero. -/
theorem actual_waiting_hasDerivWithinAt (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) (τ : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    HasDerivWithinAt (waitingCovariance β R hR J τ)
      (waitingCurrent β R hR J τ w) (Ici 0) w := by
  have hc := actual_waitingCurrent_continuous hN hp β R hR hNR J τ
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 w) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).const_add (waitingCovariance β R hR J τ 0)
  have he : ∀v ∈ Ici (0 : ℝ), waitingCovariance β R hR J τ v =
      waitingCovariance β R hR J τ 0 + ∫u in (0 : ℝ)..v, waitingCurrent β R hR J τ u := by
    intro v hv
    have hi := actual_waiting_increment_current hN hp β R hR hNR J τ
      (show (0 : ℝ) ≤ 0 from le_rfl) hv
    linarith
  exact hd.hasDerivWithinAt.congr_of_mem he hw

/-- The endpoint is the genuine right-time derivative of the actual
fixed-lag waiting correlation. -/
theorem actual_waiting_initial_hasDerivWithinAt (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) (τ : ℝ) :
    HasDerivWithinAt (waitingCovariance β R hR J τ)
      (waitingCurrent β R hR J τ 0) (Ici 0) 0 :=
  actual_waiting_hasDerivWithinAt hN hp β R hR hNR J τ le_rfl

theorem actual_mean_projected_gradient_bound (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {τ : ℝ} (hτ : 0 ≤ τ) (x : State N) (hx : OnSphere x) :
    ‖(fderiv ℝ (realMean β R hR J τ) x).comp (tangentProjection x)‖ ≤
      Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ) := by
  change ‖(fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N))
    β R hR J τ.toNNReal) x).comp (tangentProjection x)‖ ≤ _
  simpa only [Real.coe_toNNReal _ hτ, mul_assoc] using
    actual_mean_projected_operator_bound hN hp (VectorBrownian.driver N)
      β R hR hNR J x hx τ.toNNReal

theorem actual_waiting_observable_gradient_bound (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {τ : ℝ} (hτ : 0 ≤ τ) (x : State N) (hx : OnSphere x) :
    ‖projection x (gradient (waitingObservable (realMean β R hR J τ)) x)‖ ≤
      (1+Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ)) /
        Real.sqrt N := by
  change ‖projection x (gradient (waitingObservable
    (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J τ.toNNReal)) x)‖ ≤ _
  simpa only [SphereActualWaitingCurrent.actualWaitingObservable,
    Real.coe_toNNReal _ hτ] using
    SphereActualWaitingCurrent.actualWaitingObservable_gradient_bound hN hp
      (VectorBrownian.driver N) β R hR hNR J τ.toNNReal x hx

/-- Pointwise quenched Fisher domination for the actual waiting current,
including the initial physical time. -/
theorem actual_waitingCurrent_square_bound (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {τ w : ℝ} (hτ : 0 ≤ τ) (hw : 0 ≤ w) :
    (waitingCurrent β R hR J τ w)^2 ≤
      (1+Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ))^2 *
        (fisherInformation β J (forwardDensity β R hR J w)/(N : ℝ)) := by
  have hp1 : 1 ≤ p := by omega
  let D := actualForwardData hN hp1 β R hR hNR J
  let f := waitingObservable (realMean β R hR J τ)
  have hf : ContDiff ℝ 2 f :=
    waitingObservable_contDiff_two (realMean_spatial_contDiff β R hR J τ)
  have hb : ∀x, OnSphere x → ‖projection x (gradient f x)‖^2 ≤
      (1+Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ))^2/(N : ℝ) := by
    intro x hx
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (actual_waiting_observable_gradient_bound hN hp β R hR hNR J hτ x hx)
    simpa only [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using hs
  have hm : (∫x, D.ρ w x ∂SphereInitialLaw.sphereLaw N) = 1 :=
    forwardDensity_mass_one hN hp1 β R hR hNR J ⟨w, hw⟩
  have hs := SphereOnlyObservableCurrent.current_square_le_fisher hN D hf w hm hb
  change (waitingCurrent β R hR J τ w)^2 ≤
    ((1+Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ))^2/(N : ℝ)) *
      fisherInformation β J (forwardDensity β R hR J w) at hs
  convert hs using 1 <;> ring

/-- Literal actual finite-dimensional conclusions; all analytic density
data, sphere-only evolution and physical means are constructed internally. -/
structure FiniteConclusions (β R : ℝ≥0) (hR : 0 < (R : ℝ)) : Prop where
  physical_correlation : ∀J : Disorder N p, ∀τ w : ℝ≥0,
    waitingCovariance β R hR J τ w =
      ActualSphereForkEndpoints.samePathMoment (k := 1) β R hR J w τ
  mean_gradient : ∀J : Disorder N p, ∀τ : ℝ, 0 ≤ τ → ∀x : State N, OnSphere x →
    ‖(fderiv ℝ (realMean β R hR J τ) x).comp (tangentProjection x)‖ ≤
      Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ)
  waiting_gradient : ∀J : Disorder N p, ∀τ : ℝ, 0 ≤ τ → ∀x : State N, OnSphere x →
    ‖projection x (gradient (waitingObservable (realMean β R hR J τ)) x)‖ ≤
      (1+Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ))/Real.sqrt N
  waiting_current : ∀J : Disorder N p, ∀τ : ℝ, 0 ≤ τ → ∀w : ℝ, 0 ≤ w →
    HasDerivWithinAt (waitingCovariance β R hR J τ)
      (waitingCurrent β R hR J τ w) (Ici 0) w
  waiting_current_interior : ∀J : Disorder N p, ∀τ : ℝ, 0 ≤ τ → ∀w : ℝ, 0 < w →
    HasDerivAt (waitingCovariance β R hR J τ) (waitingCurrent β R hR J τ w) w
  current_fisher : ∀J : Disorder N p, ∀τ : ℝ, 0 ≤ τ → ∀w : ℝ, 0 ≤ w →
    (waitingCurrent β R hR J τ w)^2 ≤
      (1+Real.exp ((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ))^2 *
        (fisherInformation β J (forwardDensity β R hR J w)/(N : ℝ))
  waiting_increment : ∀J : Disorder N p, ∀τ : ℝ, 0 ≤ τ → ∀u v : ℝ, 0 ≤ u → u ≤ v →
    waitingCovariance β R hR J τ v-waitingCovariance β R hR J τ u =
      ∫w in u..v, waitingCurrent β R hR J τ w

theorem source5_5_finite (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2) :
    FiniteConclusions (N := N) (p := p) β R hR := by
  have hp1 : 1 ≤ p := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun J τ w => actual_waitingCovariance_eq_samePathMoment hN hp1 β R hR hNR J τ w
  · exact fun J τ hτ x hx => actual_mean_projected_gradient_bound hN hp β R hR hNR J hτ x hx
  · exact fun J τ hτ x hx => actual_waiting_observable_gradient_bound hN hp β R hR hNR J hτ x hx
  · exact fun J τ _ w hw => actual_waiting_hasDerivWithinAt hN hp1 β R hR hNR J τ hw
  · exact fun J τ _ w hw => actual_waiting_hasDerivAt hN hp1 β R hR hNR J τ hw
  · exact fun J τ hτ w hw => actual_waitingCurrent_square_bound hN hp β R hR hNR J hτ hw
  · exact fun J τ _ u v hu huv => actual_waiting_increment_current hN hp1 β R hR hNR J τ hu huv

@[expose] def canonicalRadius (N : ℕ) : ℝ≥0 := N+1

theorem canonicalRadius_pos (N : ℕ) : 0 < (canonicalRadius N : ℝ) := by
  unfold canonicalRadius
  positivity

theorem canonicalRadius_sq (N : ℕ) : (N : ℝ) < (canonicalRadius N : ℝ)^2 := by
  simp only [canonicalRadius, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N]

/-- The finite source receipt with the cutoff constructed internally.
Only the actual dimension, spin and drift parameter are supplied. -/
theorem source5_5_actual_model (hN : 0 < N) (hp : 2 ≤ p) (β : ℝ≥0) :
    FiniteConclusions (N := N) (p := p) β (canonicalRadius N) (canonicalRadius_pos N) :=
  source5_5_finite hN hp β (canonicalRadius N) (canonicalRadius_pos N) (canonicalRadius_sq N)

end SphericalAging.ActualSphereFiniteWaitingTheorem
