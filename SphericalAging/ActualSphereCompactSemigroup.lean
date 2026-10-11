module

public import SphericalAging.ActualCompactTransitionRegularity
public import SphericalAging.ActualC2BackwardGenerator
public import SphericalAging.SphereSpatialGeneratorRegularity

public section

/-! Genuine real-time spatial jets and backward equation of the actual
sphere semigroup for compact C² tests, including continuity at time zero. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereCompactSemigroup
open MeasureTheory Set Filter FiniteModel HardSphereDynamics ActualSphereTransition
open ActualCompactTransitionRegularity ActualC2BackwardGenerator SphereQuenchedFDT
open SphereGeneratorIntegrationByParts SphereSpatialGeneratorRegularity
open scoped NNReal Topology
variable {N p : ℕ}

@[expose] def realTransition (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (f : State N→ℝ) (t : ℝ) (x : State N) : ℝ :=
  transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f x

theorem realTransition_spatial_contDiff (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : ℝ) :
    ContDiff ℝ 2 (realTransition β R hR J f t) :=
  (compact_spatialC2Transition β R hR J hf hfc).slices t.toNNReal

theorem realTransition_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (Function.uncurry (realTransition β R hR J f)) := by
  exact (compact_spatialC2Transition β R hR J hf hfc).value.comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

theorem realTransition_first_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (fun w : ℝ×State N => fderiv ℝ (realTransition β R hR J f w.1) w.2) :=
  (compact_spatialC2Transition β R hR J hf hfc).first.comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

theorem realTransition_second_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (fun w : ℝ×State N => fderiv ℝ (fderiv ℝ (realTransition β R hR J f w.1)) w.2) :=
  (compact_spatialC2Transition β R hR J hf hfc).second.comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

theorem realTransition_generator_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (fun w : ℝ×State N => rotationGenerator (1/(2*(N:ℝ))) β J
      (canonicalRotations N) (realTransition β R hR J f w.1) w.2) :=
  joint_rotationGenerator_continuous (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (realTransition_spatial_contDiff β R hR J hf hfc)
    (realTransition_first_joint_continuous β R hR J hf hfc)
    (realTransition_second_joint_continuous β R hR J hf hfc)

theorem realTransition_backward (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t : ℝ) (ht : 0<t) (x : State N) (hx : OnSphere x) :
    HasDerivAt (fun s => realTransition β R hR J f s x)
      (rotationGenerator (1/(2*(N:ℝ))) β J (canonicalRotations N)
        (realTransition β R hR J f t) x) t :=
  transition_backward_canonicalGenerator_of_contDiff (Nat.ne_of_gt hN) β R hR hNR J x hx hf t ht
    ((compact_spatialC2Transition β R hR J hf hfc).slices t.toNNReal)

theorem realTransition_zero (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (f : State N→ℝ) (x : State N) : realTransition β R hR J f 0 x=f x := by
  simp only [realTransition,Real.toNNReal_zero]
  exact transition_zero _ β R hR J f x

end SphericalAging.ActualSphereCompactSemigroup
