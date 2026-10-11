module

public import SphericalAging.FiniteDisclosureResidual
public import SphericalAging.GaussianIsometricRange

public section

/-! The literal terminal residual Gaussian has exactly the projected
ambient Gaussian law at the constructed physical vector span. -/
noncomputable section
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureGaussianProjection
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open TensorOrthogonalAction TensorResidualRotation
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual

@[expose] def physicalInclusion {N p : ℕ} (W : Submodule ℝ (Vector N)) (F : Frame N) :
    residualTensorSpace (p:=p) W→ₗᵢ[ℝ]TensorSpace N p :=
  (action F).toLinearIsometry.comp (residualTensorSpace W).subtypeₗᵢ

theorem physicalInclusion_range {N p : ℕ} (W : Submodule ℝ (Vector N)) (F : Frame N) :
    LinearMap.range (physicalInclusion (p:=p) W F).toLinearMap=
      residualTensorSpace (rotatedSpace F W) := by
  change LinearMap.range ((action F).toLinearEquiv.toLinearMap.comp (residualTensorSpace W).subtype)=_
  rw [LinearMap.range_comp,Submodule.range_subtype,residualTensorSpace_rotated]

theorem actual_average_projected_gaussian (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (φ : TensorSpace N p→ℝ)
    (hφ : StronglyMeasurable φ) (s : Past N p n r S) :
    FiniteDisclosurePast.average N p n r S (φ∘physicalResidual N p n r S P F) s=
      ∫J,φ ((residualTensorSpace (physicalSpace N p n r S P F s)).starProjection J)
        ∂stdGaussian (TensorSpace N p) := by
  induction n generalizing r S with
  | zero =>
    have hh := GaussianIsometricRange.integral_isometry_eq_projected
      (physicalInclusion (CanonicalVectorSpan.space N r) (F s)) φ hφ
    change (∫R : Residual N p r,φ (action (F s) R.val) ∂stdGaussian (Residual N p r))=
      ∫J,φ ((LinearMap.range (physicalInclusion (CanonicalVectorSpan.space N r) (F s)).toLinearMap).starProjection J)
        ∂stdGaussian (TensorSpace N p) at hh
    simpa only [physicalInclusion_range,FiniteDisclosurePast.average,physicalResidual,physicalSpace,
      Function.comp_def] using hh

  | succ n ih =>
    cases s with
    | inl s => exact ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F) s
    | inr s => exact ih r S P.2.2 F s

end SphericalAging.FiniteDisclosureGaussianProjection
