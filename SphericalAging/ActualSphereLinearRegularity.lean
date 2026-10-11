module

public import SphericalAging.ActualSphereMeanJointSpatialContinuity
public import SphericalAging.ActualSphereLinearInnovation

public section

/-! The constructed linear transition has genuine spatial C² and joint
spatial derivative continuity. This closes the analytic input in the actual
linear backward stochastic-integral and variance formulas. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualSphereLinearRegularity
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereLinearTransition
open ActualSphereMeanSpatialC2 ActualSphereMeanJointSpatialContinuity
open ActualSphereBackwardIto MultivariateTaylor
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def postcompose (a : State N) :
    (State N →L[ℝ] State N) →L[ℝ] (State N →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ (State N) (State N) ℝ (innerSL ℝ a)

theorem fderiv_transition_inner_eq (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (a x : State N) :
    fderiv ℝ (transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t (fun y => ⟪a,y⟫_ℝ)) x=
    postcompose a (fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t) x) := by
  ext v
  exact fderiv_transition_inner (VectorBrownian.driver N) β R hR J t a x v

theorem hessian_transition_inner_eq (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (a x : State N) :
    Hessian (transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t (fun y => ⟪a,y⟫_ℝ)) x=
    (postcompose a).comp (fderiv ℝ (fderiv ℝ
      (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t)) x) := by
  have he : fderiv ℝ (transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t (fun y => ⟪a,y⟫_ℝ))=
      fun y => postcompose a (fderiv ℝ (mean
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t) y) :=
    funext (fun y => fderiv_transition_inner_eq β R hR J t a y)
  unfold Hessian
  rw [he]
  have hd := ((mean_contDiff_two (VectorBrownian.driver N) β J R hR t).fderiv_right
    (m := 1) (by norm_num)).differentiable (by norm_num)
  exact ((postcompose a).hasFDerivAt.comp x (hd x).hasFDerivAt).fderiv

/-- All transition regularity needed by the linear backward formula is
proved from the actual first and second variational SDEs. -/
theorem linear_spatialC2Transition (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (a : State N) :
    SpatialC2Transition β R hR J (fun y => ⟪a,y⟫_ℝ) := by
  have he (t : ℝ≥0) : transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t (fun y => ⟪a,y⟫_ℝ)=
      fun y => ⟪a,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t y⟫_ℝ :=
    funext (fun y => transition_inner_eq_mean _ β R hR J t a y)
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    rw [he]
    exact (innerSL ℝ a).contDiff.comp (mean_contDiff_two (VectorBrownian.driver N) β J R hR t)
  · exact ((innerSL ℝ a).continuous.comp
      (mean_joint_continuous (VectorBrownian.driver N) β J R hR)).congr
      (fun q => (transition_inner_eq_mean _ β R hR J q.1 a q.2).symm)
  · exact ((postcompose a).continuous.comp
      (mean_fderiv_joint_continuous (VectorBrownian.driver N) β J R hR)).congr
      (fun q => (fderiv_transition_inner_eq β R hR J q.1 a q.2).symm)
  · exact (continuous_const.clm_comp
      (mean_second_fderiv_joint_continuous (VectorBrownian.driver N) β J R hR)).congr
      (fun q => (hessian_transition_inner_eq β R hR J q.1 a q.2).symm)

end SphericalAging.ActualSphereLinearRegularity
