module

public import SphericalAging.ActualSphereLinearRegularity
public import SphericalAging.ActualSphereMeanBackward
public import SphericalAging.SphereSpatialGeneratorRegularity

public section

/-! The true mean supplies spatial C² slices and jointly continuous
spatial derivatives on the real time parameter through its nonnegative
time projection. This does not assert mixed ambient time-space C². -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereMeanSpatialInterface
open Set Filter MeasureTheory HardSphereDynamics FiniteModel LocalSDE
open ActualSphereTransition ActualSphereMeanSpatialC2 ActualSphereMeanJointSpatialContinuity
open ActualSphereMeanBackward ActualSphereLinearRegularity ActualSphereBackwardIto
open SphericalIntegrationByParts SphereGeneratorIntegrationByParts SphereQuenchedFDT
open scoped Topology NNReal InnerProductSpace
variable {N p : ℕ}

@[expose] def realMean (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (τ : ℝ) (x : State N) : State N :=
  mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J τ.toNNReal x

theorem realMean_joint_continuous (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) :
    Continuous (Function.uncurry (realMean β R hR J)) :=
  (mean_joint_continuous (VectorBrownian.driver N) β J R hR).comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

theorem realMean_spatial_contDiff (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (τ : ℝ) : ContDiff ℝ 2 (realMean β R hR J τ) :=
  mean_contDiff_two (VectorBrownian.driver N) β J R hR τ.toNNReal

theorem realMean_coordinate_spatial_contDiff (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (i : Fin N) (τ : ℝ) :
    ContDiff ℝ 2 (fun x => realMean β R hR J τ x i) :=
  mean_coordinate_contDiff_two (VectorBrownian.driver N) β J R hR τ.toNNReal i

theorem realMean_coordinate_first_joint_continuous (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (i : Fin N) :
    Continuous (fun z : ℝ×State N => fderiv ℝ (fun x => realMean β R hR J z.1 x i) z.2) := by
  have hr := linear_spatialC2Transition β R hR J (basisVector i)
  have hobs : (fun y : State N => ⟪basisVector i,y⟫_ℝ)=(fun y => y i) := by
    funext y
    rw [real_inner_comm,basis_inner]
  rw [hobs] at hr
  have he (t : ℝ≥0) : transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t (fun y : State N => y i)=fun y => realMean β R hR J (t:ℝ) y i := by
    funext y
    simpa only [realMean,Real.toNNReal_coe] using transition_coordinate_eq_mean β R hR J t i y
  have hh := hr.first.comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  simpa only [Function.comp_def,he,realMean,Real.toNNReal_coe] using hh

theorem realMean_coordinate_second_joint_continuous (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (i : Fin N) :
    Continuous (fun z : ℝ×State N => fderiv ℝ
      (fderiv ℝ (fun x => realMean β R hR J z.1 x i)) z.2) := by
  have hr := linear_spatialC2Transition β R hR J (basisVector i)
  have hobs : (fun y : State N => ⟪basisVector i,y⟫_ℝ)=(fun y => y i) := by
    funext y
    rw [real_inner_comm,basis_inner]
  rw [hobs] at hr
  have he (t : ℝ≥0) : transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t (fun y : State N => y i)=fun y => realMean β R hR J (t:ℝ) y i := by
    funext y
    simpa only [realMean,Real.toNNReal_coe] using transition_coordinate_eq_mean β R hR J t i y
  have hh := hr.second.comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  simpa only [Function.comp_def,he,realMean,Real.toNNReal_coe,MultivariateTaylor.Hessian] using hh

theorem realMean_coordinate_generator_joint_continuous (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (i : Fin N) :
    Continuous (fun z : ℝ×State N => rotationGenerator (1/(2*(N:ℝ))) β J (canonicalRotations N)
      (fun y => realMean β R hR J z.1 y i) z.2) :=
  SphereSpatialGeneratorRegularity.joint_rotationGenerator_continuous _ β J _
    (realMean_coordinate_spatial_contDiff β R hR J i)
    (realMean_coordinate_first_joint_continuous β R hR J i)
    (realMean_coordinate_second_joint_continuous β R hR J i)

end SphericalAging.ActualSphereMeanSpatialInterface
