module

public import SphericalAging.CompactC2SpatialFamily
public import SphericalAging.ActualGammaPredictorHessianRegularity

public section

/-! Uniform compact-horizon Taylor bounds for the actual state mean and
Brownian pairing mean. All spatial regularity comes from actual variational
flows and no Γ variance or asymptotic-limit assumption is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualGammaPredictorCompactTaylor
open FiniteModel HardSphereDynamics ActualSphereTransition
open ActualSphereGammaVariance ActualGammaBackwardPredictor
open ActualSphereMeanJointSpatialContinuity ActualGammaPredictorRegularity
open ActualGammaPredictorHessianRegularity CompactC2SpatialFamily
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def SpatialBound (f : State N→State N) (g : State N→ℝ) (C : ℝ) : Prop :=
  ∀ x∈Metric.closedBall (0 : State N) (Real.sqrt N),
    ‖fderiv ℝ f x‖≤C ∧ ‖fderiv ℝ g x‖≤C ∧
    ∀ y∈Metric.closedBall (0 : State N) (Real.sqrt N),
      ‖f y-f x‖≤C*‖y-x‖ ∧ ‖g y-g x‖≤C*‖y-x‖ ∧
      ‖f y-f x-fderiv ℝ f x (y-x)‖≤C*‖y-x‖^2 ∧
      ‖g y-g x-fderiv ℝ g x (y-x)‖≤C*‖y-x‖^2

theorem exists_actual_spatialBound (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T t s : ℝ≥0) (hT : 0<T) :
    ∃ C : ℝ,0≤C ∧ ∀ q∈Icc (0 : ℝ≥0) s,
      SpatialBound (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q))
        (initialMean β R hR J T (t-q) (s-q)) C := by
  let f : ℝ≥0→State N→State N := fun q => mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q)
  let g : ℝ≥0→State N→ℝ := fun q => initialMean β R hR J T (t-q) (s-q)
  have hmf : ∀ q,ContDiff ℝ 2 (f q) := fun q => ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-q)
  have hgf : ∀ q,ContDiff ℝ 2 (g q) := fun q => gammaMean_initial_contDiff_two β R hR J T (t-q) (s-q) hT
  have hmap : Continuous (fun q : ℝ≥0×State N => (t-q.1,q.2)) := by fun_prop
  have hgmap : Continuous (fun q : ℝ≥0×State N => ((t-q.1,s-q.1),q.2)) := by fun_prop
  have hmd := (mean_fderiv_joint_continuous (VectorBrownian.driver N) β J R hR).comp hmap
  have hmh := (mean_second_fderiv_joint_continuous (VectorBrownian.driver N) β J R hR).comp hmap
  have hgd := (gammaMean_fderiv_joint_continuous β R hR J T hT).comp hgmap
  have hgh := (gammaMean_second_fderiv_joint_continuous β R hR J T hT).comp hgmap
  obtain ⟨Cm,hCm,hm⟩ := exists_uniform_bounds f hmf hmd hmh (Icc (0 : ℝ≥0) s) isCompact_Icc (Real.sqrt N)
  obtain ⟨Cg,hCg,hg⟩ := exists_uniform_bounds g hgf hgd hgh (Icc (0 : ℝ≥0) s) isCompact_Icc (Real.sqrt N)
  refine ⟨max Cm Cg,le_trans hCm (le_max_left _ _),?_⟩
  intro q hq x hx
  obtain ⟨hmdx,hmxy⟩ := hm q hq x hx
  obtain ⟨hgdx,hgxy⟩ := hg q hq x hx
  refine ⟨hmdx.trans (le_max_left _ _),hgdx.trans (le_max_right _ _),?_⟩
  intro y hy
  obtain ⟨hml,hmt⟩ := hmxy y hy
  obtain ⟨hgl,hgt⟩ := hgxy y hy
  exact ⟨hml.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
    hgl.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)),
    hmt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)),
    hgt.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩

end SphericalAging.ActualGammaPredictorCompactTaylor
