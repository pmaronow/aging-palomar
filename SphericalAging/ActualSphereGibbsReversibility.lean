module

public import SphericalAging.ActualSphereCompactSemigroup
public import SphericalAging.SphereGibbsGenerator
public import SphericalAging.SphereEntropyBudget
public import SphericalAging.SphereTwoFunctionCurrent

public section

/-! Reversibility of the literal actual sphere semigroup in the genuine
Gibbs measure. The identity is derived by backward interpolation, actual
C² regularity, differentiation under the sphere integral, and generator
integration by parts. No invariant-law or symmetry identity is assumed. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereGibbsReversibility
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open ActualSphereCompactSemigroup SphereGibbsEntropy SphereGibbsGenerator
open SphereGeneratorIntegrationByParts SphereFDTAlgebra SphereEntropyBudget SphereEntropyDissipation
open SphereRotationGeometry SphereQuenchedFDT SphericalIntegrationByParts
open SphereForwardAdjoint
open scoped NNReal Topology
variable {N p : ℕ}

@[expose] def gibbsInterpolation (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (f g : State N→ℝ) (t z : ℝ) : ℝ :=
  ∫x : State N,gibbsDensity N p β J x*
    realTransition β R hR J f (t-z) x*realTransition β R hR J g z x ∂sphereLaw N

theorem gibbsInterpolation_continuous (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f g : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ) :
    Continuous (gibbsInterpolation β R hR J f g t) := by
  unfold gibbsInterpolation
  apply continuous_sphere_parameter_integral hN
  exact (((gibbsDensity_contDiff β J).continuous.comp continuous_snd).mul
    ((realTransition_joint_continuous β R hR J hf hfc).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd))).mul
        (realTransition_joint_continuous β R hR J hg hgc)

theorem gibbsInterpolation_hasDerivAt_zero (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {f g : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t z : ℝ) (hz : 0<z) (hzt : z<t) :
    HasDerivAt (gibbsInterpolation β R hR J f g t) 0 z := by
  have hρ : ContDiff ℝ 2 (fun w : ℝ×State N => gibbsDensity N p β J w.2) :=
    ((gibbsDensity_contDiff β J).of_le (by simp)).comp contDiff_snd
  have hh := SphereTwoFunctionCurrent.product_pairing_hasDerivAt
    (ρ:=fun _ => gibbsDensity N p β J) (ρdot:=fun _ _ => 0)
    (m:=realTransition β R hR J f) (n:=realTransition β R hR J g)
    hN (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ continuous_const
    (fun v x => hasDerivAt_const v (gibbsDensity N p β J x))
    (realTransition_joint_continuous β R hR J hf hfc)
    (realTransition_spatial_contDiff β R hR J hf hfc)
    (realTransition_generator_joint_continuous β R hR J hf hfc)
    (realTransition_backward hN β R hR hNR J hf hfc)
    (realTransition_joint_continuous β R hR J hg hgc)
    (realTransition_spatial_contDiff β R hR J hg hgc)
    (realTransition_generator_joint_continuous β R hR J hg hgc)
    (realTransition_backward hN β R hR hNR J hg hgc)
    0 t 0 z hzt (by simpa only [zero_add] using hz)
    (gibbsDensity_positive hN hp β.coe_nonneg J)
    (fun x _ => by rw [gibbs_forwardDensitySlope_zero hN hp (1/(2*(N:ℝ))) β.coe_nonneg J (canonicalRotations N)])
  simp only [zero_add,relativeLog_gibbs_zero hN hp β.coe_nonneg J,
    rotationGamma,lieDerivative_const,zero_mul,Finset.sum_const_zero,mul_zero,integral_zero] at hh
  have he : (fun v : ℝ => ∫x : State N,gibbsDensity N p β J x*
      realTransition β R hR J f (t-v) x*realTransition β R hR J g v x ∂sphereLaw N)=
        gibbsInterpolation β R hR J f g t := rfl
  rw [he] at hh
  exact hh

/-- Genuine detailed balance for compact C² tests of the actual semigroup. -/
theorem compact_transition_reversible (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {f g : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ≥0) :
    (∫x : State N,gibbsDensity N p β J x*realTransition β R hR J f t x*g x ∂sphereLaw N)=
      (∫x : State N,gibbsDensity N p β J x*f x*realTransition β R hR J g t x ∂sphereLaw N) := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg
    (gibbsInterpolation_continuous hN β R hR J hf hfc hg hgc t).continuousOn
    (fun z hz => gibbsInterpolation_hasDerivAt_zero hN hp β R hR hNR J hf hfc hg hgc t z hz.1 hz.2)
    ((continuous_const : Continuous (fun _ : ℝ => (0:ℝ))).intervalIntegrable 0 t)
  simp only [intervalIntegral.integral_zero,gibbsInterpolation,realTransition_zero,sub_self,sub_zero] at hh
  exact (sub_eq_zero.mp hh.symm).symm

end SphericalAging.ActualSphereGibbsReversibility
