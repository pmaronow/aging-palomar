module

public import SphericalAging.ActualSphereTensorGradient
public import SphericalAging.SphereTwoSemigroupCurrent
public import SphericalAging.SphereFisherHelly
public import SphericalAging.SphereCarreDuChamp

public section

/-! The literal actual tensor semigroup product and its exact density current.
The actual SDE supplies all backward regularity and equations; the honest
positive forward density is the sole analytic realization input. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereTensorProductCurrent
open MeasureTheory Set Filter
open FiniteModel HardSphereDynamics SphereInitialLaw AdaptiveGradientDisclosure
open ActualSphereTensorSemigroup ActualSphereTensorGradient SphereFisherHelly
open SphereTwoSemigroupCurrent SphereGeneratorIntegrationByParts SphereEntropyDissipation
open SphereMixedDerivatives SphereSpatialGeneratorRegularity SphereQuenchedFDT
open SphereRotationGeometry SphereCarreDuChamp SphericalIntegrationByParts
open scoped Topology NNReal InnerProductSpace BigOperators
variable {N p k : ℕ}

@[expose] def actualTensorPairing (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (J : Disorder N p) (T a d z : ℝ) : ℝ :=
  ∫x : State N,E.ρ J (T+z) x*⟪realTensorMean (k:=k) β R hR J (a-z) x,
    realTensorMean (k:=k) β R hR J (d+z) x⟫_ℝ ∂sphereLaw N

@[expose] def actualTensorCurrent (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (J : Disorder N p) (T a d z : ℝ) : ℝ :=
  -2*(∫x : State N,E.ρ J (T+z) x*⟪realTensorMean (k:=k) β R hR J (a-z) x,
    fderiv ℝ (realTensorMean (k:=k) β R hR J (d+z)) x
      (tangentScore β J (E.ρ J (T+z)) x)⟫_ℝ ∂sphereLaw N)

theorem tensor_inner_eq_sum (u v : TensorSpace N k) :
    ⟪u,v⟫_ℝ=∑I : TensorIndex N k,u I*v I := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

theorem realTensorMean_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) :
    Continuous (fun w : ℝ×State N => realTensorMean (k:=k) β R hR J w.1 w.2) := by
  have hh := (EuclideanSpace.equiv (TensorIndex N k) ℝ).symm.continuous.comp
    (continuous_pi (fun I => realTensorMean_coordinate_joint_continuous β R hR J I))
  exact hh

theorem realTensorMean_coordinate_contDiff (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (t : ℝ) (I : TensorIndex N k) :
    ContDiff ℝ 2 (fun x => realTensorMean (k:=k) β R hR J t x I) :=
  (PiLp.proj (𝕜:=ℝ) 2 (fun _ : TensorIndex N k => ℝ) I).contDiff.comp
    (tensorMean_contDiff_two β R hR J t.toNNReal)

theorem realTensorMean_coordinate_generator_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (I : TensorIndex N k) :
    Continuous (fun w : ℝ×State N => rotationGenerator (1/(2*(N:ℝ))) β J
      (canonicalRotations N) (fun x => realTensorMean (k:=k) β R hR J w.1 x I) w.2) :=
  joint_rotationGenerator_continuous (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (fun t => realTensorMean_coordinate_contDiff β R hR J t I)
    (realTensorMean_coordinate_first_joint_continuous β R hR J I)
    (realTensorMean_coordinate_second_joint_continuous β R hR J I)

theorem scalar_coordinate_score_identity (hN : 0<N) (β : ℝ) (J : Disorder N p)
    (ρ : State N→ℝ) (g : State N→TensorSpace N k) (hg : ContDiff ℝ 2 g)
    (x : State N) (hx : OnSphere x) (I : TensorIndex N k) :
    rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N) (relativeLog β J ρ) (fun y => g y I) x=
      (fderiv ℝ g x (tangentScore β J ρ x)) I := by
  rw [canonical_rotationGamma hN _ _ _ hx]
  change ⟪projection x (gradient (relativeLog β J ρ) x),projection x (gradient (fun y => g y I) x)⟫_ℝ=_
  rw [←projection_self_adjoint,projection_idempotent (Nat.ne_of_gt hN) x _ hx]
  rw [real_inner_comm,inner_gradient_left]
  have hd := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : TensorIndex N k => ℝ) I).hasFDerivAt.comp x
    ((hg.differentiable (by norm_num)) x).hasFDerivAt
  simp only [Function.comp_def,PiLp.proj_apply] at hd
  rw [hd.fderiv]
  rfl

theorem actualTensorPairing_eq_sum (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (J : Disorder N p) (T a d z : ℝ) :
    actualTensorPairing (k:=k) β R hR E J T a d z=
      ∑I : TensorIndex N k,∫x : State N,E.ρ J (T+z) x*
        realTensorMean (k:=k) β R hR J (a-z) x I*
        realTensorMean (k:=k) β R hR J (d+z) x I ∂sphereLaw N := by
  classical
  unfold actualTensorPairing
  simp_rw [tensor_inner_eq_sum,Finset.mul_sum,mul_assoc]
  apply integral_finset_sum
  intro I _
  exact continuous_sphere_integrable hN
    (((E.smooth J).continuous.comp (continuous_const.prodMk continuous_id)).mul
      ((realTensorMean_coordinate_contDiff β R hR J (a-z) I).continuous.mul
        (realTensorMean_coordinate_contDiff β R hR J (d+z) I).continuous))

theorem actualTensorPairing_hasDerivAt (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β) (J : Disorder N p)
    (T a d z : ℝ) (hT : 0≤T+z) (ha : z<a) (hd : 0<d+z) :
    HasDerivAt (actualTensorPairing (k:=k) β R hR E J T a d)
      (actualTensorCurrent (k:=k) β R hR E J T a d z) z := by
  classical
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hI I := product_pairing_hasDerivAt (m:=fun t x => realTensorMean (k:=k) β R hR J t x I)
    hN (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ
    (timeSlope_contDiff_one hρ).continuous (timeSlope_hasDerivAt (hρ.of_le (by norm_num)))
    (realTensorMean_coordinate_joint_continuous β R hR J I)
    (fun t => realTensorMean_coordinate_contDiff β R hR J t I)
    (realTensorMean_coordinate_generator_continuous β R hR J I)
    (realTensorMean_coordinate_backward hN β R hR hNR J I) T a d z ha hd
    (E.positive J (T+z)) (fun x _ => E.forward J (T+z) hT x)
  have hh := HasDerivAt.fun_sum (u:=Finset.univ) (fun I _ => hI I)
  have he : (fun v => ∑I : TensorIndex N k,∫x : State N,E.ρ J (T+v) x*
      realTensorMean (k:=k) β R hR J (a-v) x I*
      realTensorMean (k:=k) β R hR J (d+v) x I ∂sphereLaw N)=
      actualTensorPairing (k:=k) β R hR E J T a d := by
    funext v
    exact (actualTensorPairing_eq_sum hN β R hR E J T a d v).symm
  rw [he] at hh
  apply hh.congr_deriv
  unfold actualTensorCurrent
  have hρs : ContDiff ℝ 2 (E.ρ J (T+z)) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using hρ.comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : State N => (T+z,x)))
  have hrel : ContDiff ℝ 2 (relativeLog β J (E.ρ J (T+z))) :=
    ((hρs.log (fun x => (E.positive J (T+z) x).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  rw [←Finset.mul_sum,←integral_finset_sum]
  · congr 1
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    have hxs := (onSphere_iff_norm_sq x).mpr hx
    simp_rw [scalar_coordinate_score_identity hN β J (E.ρ J (T+z))
      (realTensorMean (k:=k) β R hR J (d+z)) (tensorMean_contDiff_two β R hR J (d+z).toNNReal) x hxs]
    rw [tensor_inner_eq_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring
  · intro I _
    have hΓ := SphereFDTAlgebra.rotationGamma_continuous (1/(2*(N:ℝ)))
      (canonicalRotations N) (hrel.of_le (by norm_num))
      ((realTensorMean_coordinate_contDiff β R hR J (d+z) I).of_le (by norm_num))
    exact continuous_sphere_integrable hN
      ((hρs.continuous.mul (realTensorMean_coordinate_contDiff β R hR J (a-z) I).continuous).mul hΓ)

end SphericalAging.ActualSphereTensorProductCurrent
