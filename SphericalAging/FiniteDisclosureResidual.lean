module

public import SphericalAging.FiniteDisclosurePhysicalState
public import SphericalAging.FiniteDisclosurePast

public section

/-! Identification of the finite-history Gaussian remainder with the
literal orthogonal projection of the original physical disorder. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureResidual
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan CanonicalGramSelector CanonicalGramFlag PredictableGramStep
open TensorOrthogonalAction TensorResidualRotation TensorActionComposition
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState

@[expose] def physicalSpace (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S→Frame N)→Past N p n r S→Submodule ℝ (Vector N)
  | 0,r,_,_,_,F,s => rotatedSpace (F s) (space N r)
  | n+1,r,S,_,P,F,s =>
    Sum.elim (physicalSpace N p n (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F))
      (physicalSpace N p n r S P.2.2 F) s

@[expose] def physicalResidual (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S→Frame N)→Leaves N p n r S→TensorSpace N p
  | 0,_,_,_,_,F,z => action (F z.1) z.2.val
  | n+1,r,S,_,P,F,z =>
    Sum.elim (physicalResidual N p n (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F))
      (physicalResidual N p n r S P.2.2 F) z

theorem frame_projection {N p : ℕ} (W : Submodule ℝ (Vector N))
    (F : Frame N) (D : TensorSpace N p) (hD : D∈(residualTensorSpace W)ᗮ)
    (R : residualTensorSpace (p:=p) W) :
    (residualTensorSpace (rotatedSpace F W)).starProjection (action F (D+R.val))=action F R.val := by
  have hh := (action F).toLinearIsometry.map_starProjection (residualTensorSpace (p:=p) W) (D+R.val)
  change action F ((residualTensorSpace (p:=p) W).starProjection (D+R.val))=
    ((residualTensorSpace (p:=p) W).map (action F).toLinearEquiv.toLinearMap).starProjection
      (action F (D+R.val)) at hh
  have hh' : action F ((residualTensorSpace (p:=p) W).starProjection (D+R.val))=
      (residualTensorSpace (rotatedSpace F W)).starProjection (action F (D+R.val)) := by
    simpa only [residualTensorSpace_rotated] using hh
  have hDP : (residualTensorSpace (p:=p) W).starProjection D=0 :=
    (residualTensorSpace (p:=p) W).starProjection_apply_eq_zero_iff.mpr hD
  rw [map_add,hDP,(residualTensorSpace (p:=p) W).starProjection_eq_self_iff.mpr R.property,zero_add] at hh'
  exact hh'.symm

theorem actual_residual_is_projection (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (D : S→TensorSpace N p)
    (hD : ∀s,D s∈(Residual N p r)ᗮ) (z : Leaves N p n r S) :
    physicalResidual N p n r S P F z=
      (residualTensorSpace (physicalSpace N p n r S P F (past N p n r S z))).starProjection
        (decode N p n r S P F D z) := by
  induction n generalizing r S with
  | zero => exact (frame_projection (space N r) (F z.1) (D z.1) (hD z.1) z.2).symm
  | succ n ih =>
    cases z with
    | inl z =>
      exact ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F) (freshDisclosed P.1.val D)
        (freshDisclosed_mem P.1.val D hD) z
    | inr z => exact ih r S P.2.2 F D hD z

theorem actual_original_disorder_projection (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (D : S→TensorSpace N p)
    (hD : ∀s,D s∈(Residual N p r)ᗮ) (z : S×Residual N p r) :
    physicalResidual N p n r S P F (execute N p n r S P z)=
      (residualTensorSpace (physicalSpace N p n r S P F
        (past N p n r S (execute N p n r S P z)))).starProjection
        (action (F z.1) (D z.1+z.2.val)) := by
  have hh := actual_residual_is_projection N p n r S P F D hD (execute N p n r S P z)
  rw [actual_disorder_preserved] at hh
  exact hh

end SphericalAging.FiniteDisclosureResidual
