module

public import SphericalAging.ActualSphereTensorProductCurrent
public import SphericalAging.SphereOnlyTwoSemigroupCurrent
public import SphericalAging.ActualSphereFisherClock

public section

/-! The literal tensor pairing/current of the actual diffusion. All forward
and backward analytic inputs are derived from the genuine process. Density
positivity and the positive-time PDE concern only the supported sphere. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereOnlyTensorProductCurrent
open MeasureTheory Set Filter
open FiniteModel HardSphereDynamics SphereInitialLaw AdaptiveGradientDisclosure
open ActualSphereTensorSemigroup ActualSphereTensorGradient SphereFisherHelly
open ActualSphereTensorProductCurrent ActualSphereFisherClock ActualSphereGibbsDensity
open SphereOnlyTwoSemigroupCurrent SmoothPositiveSpatialReplacement SphereOnlySpatialLocalization
open SphereOnlyParameterIntegral
open SphereGeneratorIntegrationByParts SphereEntropyDissipation
open SphereMixedDerivatives SphereSpatialGeneratorRegularity SphereQuenchedFDT
open SphereRotationGeometry SphereCarreDuChamp SphericalIntegrationByParts
open scoped Topology NNReal InnerProductSpace BigOperators
variable {N p k : ℕ}

@[expose] def actualTensorPairing (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (T a d z : ℝ) : ℝ :=
  ∫x : State N,forwardDensity β R hR J (T+z) x*⟪realTensorMean (k:=k) β R hR J (a-z) x,
    realTensorMean (k:=k) β R hR J (d+z) x⟫_ℝ ∂sphereLaw N

@[expose] def actualTensorCurrent (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (T a d z : ℝ) : ℝ :=
  -2*(∫x : State N,forwardDensity β R hR J (T+z) x*⟪realTensorMean (k:=k) β R hR J (a-z) x,
    fderiv ℝ (realTensorMean (k:=k) β R hR J (d+z)) x
      (tangentScore β J (forwardDensity β R hR J (T+z)) x)⟫_ℝ ∂sphereLaw N)

theorem actualTensorPairing_eq_sum (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (T a d z : ℝ) :
    actualTensorPairing (k:=k) β R hR J T a d z=
      ∑I : TensorIndex N k,∫x : State N,forwardDensity β R hR J (T+z) x*
        realTensorMean (k:=k) β R hR J (a-z) x I*
        realTensorMean (k:=k) β R hR J (d+z) x I ∂sphereLaw N := by
  classical
  unfold actualTensorPairing
  simp_rw [tensor_inner_eq_sum,Finset.mul_sum,mul_assoc]
  apply integral_finset_sum
  intro I _
  exact continuous_sphere_integrable hN
    (((forwardDensity_joint_continuous hN hp β R hR J).comp (continuous_const.prodMk continuous_id)).mul
      ((realTensorMean_coordinate_contDiff β R hR J (a-z) I).continuous.mul
        (realTensorMean_coordinate_contDiff β R hR J (d+z) I).continuous))

theorem actualTensorPairing_hasDerivAt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (T a d z : ℝ) (hT : 0<T+z) (ha : z<a) (hd : 0<d+z) :
    HasDerivAt (actualTensorPairing (k:=k) β R hR J T a d)
      (actualTensorCurrent (k:=k) β R hR J T a d z) z := by
  classical
  let D := actualForwardData hN hp β R hR hNR J
  have hI I := product_pairing_hasDerivAt (m:=fun t x => realTensorMean (k:=k) β R hR J t x I)
    hN (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) D.joint
    (fun t => (D.spatial t).of_le (by norm_num)) D.jointDot D.timeDerivative
    (realTensorMean_coordinate_joint_continuous β R hR J I)
    (fun t => realTensorMean_coordinate_contDiff β R hR J t I)
    (realTensorMean_coordinate_generator_continuous β R hR J I)
    (realTensorMean_coordinate_backward hN β R hR hNR J I) T a d z ha hd hT
    (D.positive (T+z)) (D.spherePDE (T+z) hT)
  have hh := HasDerivAt.fun_sum (u:=Finset.univ) (fun I _ => hI I)
  dsimp only [D, actualForwardData] at hh
  have he : (fun v => ∑I : TensorIndex N k,∫x : State N,forwardDensity β R hR J (T+v) x*
      realTensorMean (k:=k) β R hR J (a-v) x I*
      realTensorMean (k:=k) β R hR J (d+v) x I ∂sphereLaw N)=
      actualTensorPairing (k:=k) β R hR J T a d := by
    funext v
    exact (actualTensorPairing_eq_sum hN hp β R hR J T a d v).symm
  rw [he] at hh
  apply hh.congr_deriv
  unfold actualTensorCurrent
  have hρs : ContDiff ℝ 2 (forwardDensity β R hR J (T+z)) :=
    (D.spatial (T+z)).of_le (by norm_num)
  obtain ⟨r,hr,hrpos,hnear⟩ := exists_positive_near_sphere hρs (D.positive (T+z))
  have hrel : ContDiff ℝ 2 (relativeLog β J r) :=
    ((hr.log (fun x => (hrpos x).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  rw [←Finset.mul_sum,←integral_finset_sum]
  · congr 1
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    have hxs := (onSphere_iff_norm_sq x).mpr hx
    simp_rw [scalar_coordinate_score_identity hN β J (forwardDensity β R hR J (T+z))
      (realTensorMean (k:=k) β R hR J (d+z)) (tensorMean_contDiff_two β R hR J (d+z).toNNReal) x hxs]
    rw [tensor_inner_eq_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring
  · intro I _
    have hΓ := SphereFDTAlgebra.rotationGamma_continuous (1/(2*(N:ℝ)))
      (canonicalRotations N) (hrel.of_le (by norm_num))
      ((realTensorMean_coordinate_contDiff β R hR J (d+z) I).of_le (by norm_num))
    apply (continuous_sphere_integrable hN
      ((hr.continuous.mul (realTensorMean_coordinate_contDiff β R hR J (a-z) I).continuous).mul hΓ)).congr
    filter_upwards [physicalSphere_ae hN] with x hx
    simp only [Pi.mul_apply]
    rw [(hnear x hx).eq_of_nhds,
      (SphereOnlyGeneratorLocalization.rotationGamma_eventuallyEq _ _
        (relativeLog_eventuallyEq β J (hnear x hx)) EventuallyEq.rfl).eq_of_nhds]

end SphericalAging.ActualSphereOnlyTensorProductCurrent
