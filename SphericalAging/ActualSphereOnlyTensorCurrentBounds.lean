module

public import SphericalAging.ActualSphereOnlyTensorProductCurrent
public import SphericalAging.SphereOnlyTensorFisherBound
public import SphericalAging.ActualTensorFirstJetContinuity
public import SphericalAging.ActualSphereRestrictedFisherBudget

public section

/-! All-time continuity, probability bounds, sharp Fisher control and FTC
for the native actual tensor current. Every density input is constructed
from the actual diffusion, with positivity only on the supported sphere. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace BigOperators
namespace SphericalAging.ActualSphereOnlyTensorCurrentBounds
open FiniteModel HardSphereDynamics SphereInitialLaw AdaptiveGradientDisclosure
open ActualSphereTensorSemigroup ActualSphereTensorGradient ActualSphereTensorProductCurrent
open ActualSphereOnlyTensorProductCurrent ActualSphereGibbsDensity ActualSphereForwardDensityRegularity
open SphereRotationGeometry SphereOnlyTensorFisherBound SphereOnlyParameterIntegral
open SphereOnlyAllTimeContinuity SphereOnlyFisherContinuity SphereOnlyFisherCurrentContinuity
open ActualSphereRestrictedFisherBudget GaussianLandscape SphereGoodEventFisherClock
open SphericalIntegrationByParts SphereEntropyBudget ActualTensorFirstJetContinuity
variable {N p k : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem actualTensorPairing_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (T a d : ℝ) :
    Continuous (ActualSphereOnlyTensorProductCurrent.actualTensorPairing (k:=k) β R hR J T a d) := by
  unfold ActualSphereOnlyTensorProductCurrent.actualTensorPairing
  apply continuous_sphere_parameter_integral hN
  have hρ : Continuous (fun w : ℝ×State N => forwardDensity β R hR J (T+w.1) w.2) := by
    simpa only [Function.comp_def,Function.uncurry] using
      (forwardDensity_joint_continuous hN hp β R hR J).comp
        (show Continuous (fun w : ℝ×State N => (T+w.1,w.2)) from
          (continuous_const.add continuous_fst).prodMk continuous_snd)
  have hf : Continuous (fun w : ℝ×State N => realTensorMean (k:=k) β R hR J (a-w.1) w.2) := by
    simpa only [Function.comp_def] using
      (realTensorMean_joint_continuous (k:=k) β R hR J).comp
        (show Continuous (fun w : ℝ×State N => (a-w.1,w.2)) from
          (continuous_const.sub continuous_fst).prodMk continuous_snd)
  have hg : Continuous (fun w : ℝ×State N => realTensorMean (k:=k) β R hR J (d+w.1) w.2) := by
    simpa only [Function.comp_def] using
      (realTensorMean_joint_continuous (k:=k) β R hR J).comp
        (show Continuous (fun w : ℝ×State N => (d+w.1,w.2)) from
          (continuous_const.add continuous_fst).prodMk continuous_snd)
  change Continuous (fun w : ℝ×State N => forwardDensity β R hR J (T+w.1) w.2*
    ⟪realTensorMean (k:=k) β R hR J (a-w.1) w.2,realTensorMean (k:=k) β R hR J (d+w.1) w.2⟫_ℝ)
  exact hρ.mul (hf.inner hg)

theorem actualTensorCurrent_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (T a d : ℝ) :
    Continuous (ActualSphereOnlyTensorProductCurrent.actualTensorCurrent (k:=k) β R hR J T a d) := by
  change Continuous (fun z : ℝ => tensorCurrent β J (forwardDensity β R hR J (T+z))
    (realTensorMean (k:=k) β R hR J (a-z)) (realTensorMean (k:=k) β R hR J (d+z)))
  apply tensorCurrent_continuous hN β J
  · change Continuous (fun w : ℝ×State N => forwardDensity β R hR J (T+w.1) w.2)
    simpa only [Function.comp_def,Function.uncurry] using
      (forwardDensity_joint_continuous hN hp β R hR J).comp
        (show Continuous (fun w : ℝ×State N => (T+w.1,w.2)) from
          (continuous_const.add continuous_fst).prodMk continuous_snd)
  · change Continuous (fun w : ℝ×State N => fderiv ℝ (forwardDensity β R hR J (T+w.1)) w.2)
    simpa only [Function.comp_def] using
      (forwardDensity_first_joint_continuous hN hp β R hR J).comp
        (show Continuous (fun w : ℝ×State N => (T+w.1,w.2)) from
          (continuous_const.add continuous_fst).prodMk continuous_snd)
  · intro t
    exact forwardDensity_spatial_contDiff hN hp β R hR J (T+t)
  · intro t x hx
    exact forwardDensity_positive_onSphere hN hp β R hR hNR J (T+t) x hx
  · change Continuous (fun w : ℝ×State N => realTensorMean (k:=k) β R hR J (a-w.1) w.2)
    simpa only [Function.comp_def] using
      (realTensorMean_joint_continuous (k:=k) β R hR J).comp
        (show Continuous (fun w : ℝ×State N => (a-w.1,w.2)) from
          (continuous_const.sub continuous_fst).prodMk continuous_snd)
  · change Continuous (fun w : ℝ×State N => fderiv ℝ (realTensorMean (k:=k) β R hR J (d+w.1)) w.2)
    simpa only [Function.comp_def] using
      (realTensorMean_first_joint_continuous (k:=k) β R hR J).comp
        (show Continuous (fun w : ℝ×State N => (d+w.1,w.2)) from
          (continuous_const.add continuous_fst).prodMk continuous_snd)


theorem actualTensorPairing_abs_le_one (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (T a d z : ℝ) (hT : 0≤T+z) :
    |ActualSphereOnlyTensorProductCurrent.actualTensorPairing (k:=k) β R hR J T a d z|≤1 := by
  have hρ := (forwardDensity_spatial_contDiff hN hp β R hR J (T+z)).continuous
  have hf := (tensorMean_contDiff_two (k:=k) β R hR J (a-z).toNNReal).continuous
  have hg := (tensorMean_contDiff_two (k:=k) β R hR J (d+z).toNNReal).continuous
  have hi := continuous_sphere_integrable hN (hρ.mul (hf.inner hg))
  have hb : ∀ᵐx ∂sphereLaw N,‖forwardDensity β R hR J (T+z) x*
      ⟪realTensorMean (k:=k) β R hR J (a-z) x,realTensorMean (k:=k) β R hR J (d+z) x⟫_ℝ‖≤
        forwardDensity β R hR J (T+z) x := by
    filter_upwards [physicalSphere_ae hN] with x hx
    have hn₁ := tensorMean_norm_le_one (k:=k) hN β R hR hNR J (a-z).toNNReal x hx
    have hn₂ := tensorMean_norm_le_one (k:=k) hN β R hR hNR J (d+z).toNNReal x hx
    have hpρ := (forwardDensity_positive_onSphere hN hp β R hR hNR J (T+z) x hx).le
    rw [norm_mul,Real.norm_of_nonneg hpρ]
    simpa only [mul_one,realTensorMean] using mul_le_mul_of_nonneg_left
      ((norm_inner_le_norm (𝕜:=ℝ) _ _).trans (mul_le_mul hn₁ hn₂ (norm_nonneg _) (by norm_num))) hpρ
  unfold ActualSphereOnlyTensorProductCurrent.actualTensorPairing
  change ‖∫x,forwardDensity β R hR J (T+z) x*
    ⟪realTensorMean (k:=k) β R hR J (a-z) x,realTensorMean (k:=k) β R hR J (d+z) x⟫_ℝ ∂sphereLaw N‖≤1
  exact (norm_integral_le_integral_norm _).trans
    ((integral_mono_ae hi.norm (continuous_sphere_integrable hN hρ) hb).trans_eq
      (forwardDensity_mass_one hN hp β R hR hNR J ⟨T+z,hT⟩))

theorem actualTensorCurrent_square_bound (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (T a d z : ℝ) (hT : 0≤T+z) (hd : 0≤d+z) :
    (ActualSphereOnlyTensorProductCurrent.actualTensorCurrent (k:=k) β R hR J T a d z)^2≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J*(d+z)))^2*
        (fisherInformation β J (forwardDensity β R hR J (T+z))/(N:ℝ)) := by
  let c := ((k:ℝ)/Real.sqrt N)*Real.exp ((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J*(d+z))
  have hc : 0≤c := by dsimp only [c];positivity
  have hh := tensorCurrent_square_bound_onSphere hN β J
    (forwardDensity_spatial_contDiff hN (by omega) β R hR J (T+z))
    (fun x hx => forwardDensity_positive_onSphere hN (by omega) β R hR hNR J (T+z) x hx)
    (forwardDensity_mass_one hN (by omega) β R hR hNR J ⟨T+z,hT⟩)
    (f:=realTensorMean (k:=k) β R hR J (a-z))
    (g:=realTensorMean (k:=k) β R hR J (d+z))
    (tensorMean_contDiff_two β R hR J (a-z).toNNReal).continuous
    (tensorMean_contDiff_two β R hR J (d+z).toNNReal)
    (fun x hx => tensorMean_norm_le_one hN β R hR hNR J (a-z).toNNReal x hx) hc
    (fun x hx v hv => by
      have hb := tensorMean_tangent_derivative_norm_le hN hp hk β R hR hNR J x v hx (d+z).toNNReal
      rw [hv,Real.coe_toNNReal _ hd] at hb
      exact hb)
  change (ActualSphereOnlyTensorProductCurrent.actualTensorCurrent (k:=k) β R hR J T a d z)^2≤
    4*c^2*fisherInformation β J (forwardDensity β R hR J (T+z)) at hh
  refine hh.trans_eq ?_
  dsimp only [c]
  rw [mul_pow,div_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

theorem actualTensorPairing_increment_current (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (T a d : ℝ) {u v : ℝ} (huv : u≤v) (hT : 0≤T+u) (ha : v≤a) (hd : 0≤d+u) :
    ActualSphereOnlyTensorProductCurrent.actualTensorPairing (k:=k) β R hR J T a d v-
      ActualSphereOnlyTensorProductCurrent.actualTensorPairing (k:=k) β R hR J T a d u=
        ∫z in u..v,ActualSphereOnlyTensorProductCurrent.actualTensorCurrent (k:=k) β R hR J T a d z :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (actualTensorPairing_continuous hN hp β R hR J T a d).continuousOn
    (fun z hz => ActualSphereOnlyTensorProductCurrent.actualTensorPairing_hasDerivAt hN hp β R hR hNR J T a d z
      (by linarith [hz.1]) (hz.2.trans_le ha) (by linarith [hz.1]))
    ((actualTensorCurrent_continuous hN hp β R hR hNR J T a d).intervalIntegrable u v)).symm

end SphericalAging.ActualSphereOnlyTensorCurrentBounds
