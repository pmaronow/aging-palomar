module

public import SphericalAging.ActualSphereTensorCurrentBounds
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

public section

/-! The genuine coordinate tensor jets assemble into joint continuity
of the complete first spatial derivative operator. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace SphericalAging.ActualTensorFirstJetContinuity
open FiniteModel HardSphereDynamics AdaptiveGradientDisclosure ActualSphereTensorSemigroup
open ActualSphereTensorProductCurrent ActualSphereTensorCurrentBounds
variable {N p k : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] TensorSpace N k) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] TensorSpace N k) := inferInstance

theorem realTensorMean_first_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) :
    Continuous (fun z : ℝ×State N => fderiv ℝ (realTensorMean (k:=k) β R hR J z.1) z.2) := by
  let rows := fun z : ℝ×State N => fun I : TensorIndex N k =>
    fderiv ℝ (fun x => realTensorMean (k:=k) β R hR J z.1 x I) z.2
  have hrows : Continuous rows := continuous_pi (fun I =>
    realTensorMean_coordinate_first_joint_continuous β R hR J I)
  let C : (TensorIndex N k→ℝ)→L[ℝ] TensorSpace N k :=
    (EuclideanSpace.equiv (TensorIndex N k) ℝ).symm.toContinuousLinearMap
  have hp : Continuous (fun z : ℝ×State N => ContinuousLinearMap.pi (rows z)) :=
    (ContinuousLinearMap.piEquivL ℝ (State N) (fun _ : TensorIndex N k => ℝ)).continuous.comp hrows
  have hh := continuous_const.clm_comp hp (g:=fun _ : ℝ×State N => C)
  apply hh.congr
  intro z
  ext v I
  change fderiv ℝ (fun x => realTensorMean (k:=k) β R hR J z.1 x I) z.2 v=
    (fderiv ℝ (realTensorMean (k:=k) β R hR J z.1) z.2 v) I
  exact (tensor_fderiv_coordinate (tensorMean_contDiff_two β R hR J z.1.toNNReal) _ _ I).symm

end SphericalAging.ActualTensorFirstJetContinuity
