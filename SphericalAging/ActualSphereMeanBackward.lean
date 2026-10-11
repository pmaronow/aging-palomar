module

public import SphericalAging.ActualSphereMeanSpatialC2
public import SphericalAging.ActualSphereLinearTransition
public import SphericalAging.ActualC2BackwardGenerator

public section

/-! The actual expected state satisfies the canonical backward coordinate
PDE on the physical sphere. Spatial C² is derived from the constructed
second variation rather than supplied as a regularity hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereMeanBackward
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereLinearTransition
open ActualSphereMeanSpatialC2 ActualC2BackwardGenerator
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem transition_coordinate_eq_mean (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (i : Fin N) (x : State N) :
    transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t
      (fun y : State N => y i) x=
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t x i := by
  have he := transition_inner_eq_mean (NullAugmentation.driver (VectorBrownian.driver N))
    β R hR J t (basisVector i) x
  have hb (y : State N) : ⟪basisVector i,y⟫_ℝ=y i := by
    rw [real_inner_comm,basis_inner]
  simpa only [hb] using he

/-- Genuine actual mean backward equation in Frechet coefficient-generator form. -/
theorem mean_coordinate_backward_hasDerivAt (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (i : Fin N) (t : ℝ) (ht : 0<t) (x : State N) (hx : OnSphere x) :
    HasDerivAt (fun s : ℝ => mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J s.toNNReal x i)
      (SphereGenerator.coefficientGenerator β J
        (fun y => mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal y i) x) t := by
  have he (u : ℝ≥0) : transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J u (fun y : State N => y i)=
      fun y => mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u y i :=
    funext (fun y => transition_coordinate_eq_mean β R hR J u i y)
  have hg : ContDiff ℝ 2 (transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t.toNNReal (fun y : State N => y i)) := by
    rw [he]
    exact mean_coordinate_contDiff_two (VectorBrownian.driver N) β J R hR t.toNNReal i
  have hd := transition_backward_hasDerivAt_of_contDiff hN β R hR hNR J x hx
    (f := fun y : State N => y i) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff t ht hg
  simpa only [he] using hd

/-- Canonical rotational backward PDE for the actual expected SDE state. -/
theorem mean_coordinate_backward_canonical_hasDerivAt (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (i : Fin N) (t : ℝ) (ht : 0<t) (x : State N) (hx : OnSphere x) :
    HasDerivAt (fun s : ℝ => mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J s.toNNReal x i)
      (SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N : ℝ))) β J
        (fun ij : Fin N × Fin N => SphereRotationGeometry.coordinateRotation ij.1 ij.2)
        (fun y => mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal y i) x) t := by
  rw [SphereCanonicalGenerator.canonical_rotationGenerator_eq_coefficientGenerator (by omega) β J
    (mean_coordinate_contDiff_two (VectorBrownian.driver N) β J R hR t.toNNReal i) x hx]
  exact mean_coordinate_backward_hasDerivAt hN β R hR hNR J i t ht x hx

end SphericalAging.ActualSphereMeanBackward
