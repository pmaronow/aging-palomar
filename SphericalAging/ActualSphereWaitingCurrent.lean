module

public import SphericalAging.SphereOnlyObservableCurrent
public import SphericalAging.ActualSphereFisherClock
public import SphericalAging.ActualSphereMeanSpatialInterface
public import SphericalAging.SphereSharpMeanDerivative

public section

/-! Literal actual fixed-lag waiting correlation calculus. The density
sphere PDE and actual sharp tangent-mean bound construct every current
and finite Fisher increment estimate. No backward-mean interface or
ambient mixed time-space smoothness is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualSphereWaitingCurrent
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open ActualSphereGibbsDensity ActualSphereFisherClock ActualSphereMeanSpatialInterface
open SphereOnlyForwardCalculus SphereWaitingCurrent SphereQuenchedFDT SphereSharpMeanDerivative
open SphereRotationGeometry SphereGoodEventFisherClock SphereBadEventFisherMass
open ActualSphereTransition
open scoped Topology InnerProductSpace NNReal
variable {N p : ℕ}

@[expose] def waitingCovariance (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (τ w : ℝ) : ℝ :=
  quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) (w+τ) w

@[expose] def waitingCurrent (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (τ w : ℝ) : ℝ :=
  -(∫x : State N,forwardDensity β R hR J w x*⟪tangentScore β J (forwardDensity β R hR J w) x,
    projection x (gradient (waitingObservable (realMean β R hR J τ)) x)⟫_ℝ ∂sphereLaw N)

theorem actual_waitingCovariance_eq_expectation (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (τ : ℝ) :
    waitingCovariance β R hR J τ=SphereOnlyObservableCurrent.expectation
      (actualForwardData hN hp β R hR hNR J) (waitingObservable (realMean β R hR J τ)) := by
  funext w
  unfold waitingCovariance SphereOnlyObservableCurrent.expectation
  rw [quenchedCorrelation_eq_inner hN
    (ActualSphereGibbsDensity.forwardDensity_joint_continuous hN hp β R hR J)
    (realMean_joint_continuous β R hR J),add_sub_cancel_left,←integral_div]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change forwardDensity β R hR J w x*⟪x,realMean β R hR J τ x⟫_ℝ/(N:ℝ)=
      forwardDensity β R hR J w x*waitingObservable (realMean β R hR J τ) x
    unfold waitingObservable
    ring

theorem actual_waiting_hasDerivAt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (τ : ℝ)
    {w : ℝ} (hw : 0<w) :
    HasDerivAt (waitingCovariance β R hR J τ) (waitingCurrent β R hR J τ w) w := by
  rw [actual_waitingCovariance_eq_expectation hN hp β R hR hNR J τ]
  exact SphereOnlyObservableCurrent.expectation_hasDerivAt hN (actualForwardData hN hp β R hR hNR J)
    ((waitingObservable_contDiff_two (realMean_spatial_contDiff β R hR J τ)).of_le (by norm_num)) hw

theorem actual_waitingCurrent_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (τ : ℝ) :
    Continuous (waitingCurrent β R hR J τ) :=
  SphereOnlyObservableCurrent.current_continuous hN (actualForwardData hN hp β R hR hNR J)
    (waitingObservable_contDiff_two (realMean_spatial_contDiff β R hR J τ))

theorem actual_waiting_increment_current (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (τ : ℝ)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    waitingCovariance β R hR J τ v-waitingCovariance β R hR J τ u=
      ∫w in u..v,waitingCurrent β R hR J τ w := by
  rw [actual_waitingCovariance_eq_expectation hN hp β R hR hNR J τ]
  exact SphereOnlyObservableCurrent.expectation_increment_current hN (actualForwardData hN hp β R hR hNR J)
    (waitingObservable_contDiff_two (realMean_spatial_contDiff β R hR J τ)) hu huv

theorem actual_mean_tangent_bound_good (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (hJ : J∈goodEvent N p (cutoff p)) {τ L : ℝ} (hτ : 0≤τ) (hτL : τ≤L)
    (x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (realMean β R hR J τ) x (projection x v)‖≤
      Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)*‖v‖ := by
  let t := τ.toNNReal
  have hh := mean_tangent_derivative_norm_le hN hp (VectorBrownian.driver N) β R hR hNR J
    x v hx (t+1) t (by simp) (by positivity)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  apply Real.exp_le_exp.mpr
  have hQ : GaussianLandscape.landscapeNorm N p J≤cutoff p := hJ
  have hQc : 0≤cutoff p := (GaussianLandscape.landscapeNorm_nonnegative N p J).trans hQ
  have hc : 0≤(β:ℝ)*(p:ℝ)^2 := mul_nonneg β.coe_nonneg (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_left hQ hc
  have h₂ := mul_le_mul_of_nonneg_right h₁ hτ
  have h₃ := mul_le_mul_of_nonneg_left hτL (mul_nonneg hc hQc)
  simpa only [t,Real.coe_toNNReal _ hτ,mul_assoc] using h₂.trans h₃

theorem actual_waiting_increment_square_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {τ B u v : ℝ} (hB : 0≤B) (hu : 0≤u) (huv : u≤v)
    (hDm : ∀x,OnSphere x→∀z,‖fderiv ℝ (realMean β R hR J τ) x (projection x z)‖≤B*‖z‖) :
    (waitingCovariance β R hR J τ v-waitingCovariance β R hR J τ u)^2≤
      (1+B)^2*(v-u)*(∫w in u..v,fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ)) := by
  rw [actual_waitingCovariance_eq_expectation hN hp β R hR hNR J τ]
  have hφ := waitingObservable_contDiff_two (realMean_spatial_contDiff β R hR J τ)
  have hb x (hx : OnSphere x) :
      ‖projection x (gradient (waitingObservable (realMean β R hR J τ)) x)‖^2≤(1+B)^2/(N:ℝ) := by
    have hn := mean_norm_sq_le (Nat.ne_of_gt hN) (VectorBrownian.driver N)
      β R hR hNR J τ.toNNReal x hx
    have hmean : ‖realMean β R hR J τ x‖≤Real.sqrt N := by
      change ‖mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J τ.toNNReal x‖≤Real.sqrt N
      nlinarith [norm_nonneg (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J τ.toNNReal x),
        Real.sq_sqrt (Nat.cast_nonneg N),Real.sqrt_nonneg (N:ℝ)]
    have hh := waitingObservable_gradient_bound hN
      ((realMean_spatial_contDiff β R hR J τ).of_le (by norm_num)) hB x hx hmean (hDm x hx)
    have hsqrt : 0<Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (div_nonneg (by linarith) hsqrt.le)).mpr hh
    rwa [div_pow,Real.sq_sqrt (Nat.cast_nonneg N)] at hsquare
  have hh := SphereOnlyObservableCurrent.expectation_increment_square_bound hN
    (actualForwardData hN hp β R hR hNR J) hφ hu huv
    (fun w hw => forwardDensity_mass_one hN hp β R hR hNR J ⟨w,hu.trans hw.1⟩) hb
  convert hh using 1
  change (1+B)^2*(v-u)*(∫w in u..v,fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ))=
    (1+B)^2/(N:ℝ)*(v-u)*(∫w in u..v,fisherInformation β J (forwardDensity β R hR J w))
  rw [intervalIntegral.integral_div]
  ring

end SphericalAging.ActualSphereWaitingCurrent
