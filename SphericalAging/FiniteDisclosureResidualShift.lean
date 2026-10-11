module

public import SphericalAging.FiniteDisclosureQuerySpan

public section

/-! Algebraic invariance of an actual disclosure step under adding a
terminal undisclosed tensor. This is the replay foundation for identifying
the exact sigma algebra of literal projected disorder. -/
noncomputable section
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureResidualShift
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan CanonicalGramSelector CanonicalGramFlag PredictableGramStep
open PredictableTensorDisclosureStep PredictableTensorCanonicalRegeneration
open PredictableTensorProjectionIdentification PredictableTensorFrameState
open TensorOrthogonalAction TensorResidualRotation TensorActionComposition
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual

 theorem action_mem_residual_iff {N p : ℕ} (F : Frame N) (W : Submodule ℝ (Vector N))
    (J : TensorSpace N p) :
    action F J∈residualTensorSpace (rotatedSpace F W)↔J∈residualTensorSpace W := by
  constructor
  · intro h
    have hh : action F J∈(residualTensorSpace (p:=p) W).map (action F).toLinearEquiv.toLinearMap := by
      simpa only [residualTensorSpace_rotated] using h
    obtain ⟨K,hK,hEq⟩ := Submodule.mem_map.mp hh
    have he : K=J := (action F).injective hEq
    simpa only [he] using hK
  · exact action_mem_residual F W

 theorem updated_physical_residual {N p r : ℕ} {S : Type} (x : S→Vector N)
    (F : S→Frame N) (s : S) (J : TensorSpace N p) (b : Block N p r) :
    action (freshFrame x F (s,b)) (action (frameUpdate (space N r) (direction N r) (x s)) J)=
      action (F s) J := by
  rw [freshFrame,←action_trans,frame_tensor_involution]

 theorem updated_residual_mem_block_orthogonal {N p r : ℕ} {S : Type} (x : S→Vector N)
    (z : S×Residual N p r) (R : Residual N p r)
    (hR : action (frameUpdate (space N r) (direction N r) (x z.1)) R.val∈Residual N p (r+1)) :
    tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) R∈(Block N p r)ᗮ := by
  change tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) R∈
    (newResidualSubspace (space N r) (direction N r))ᗮᗮ
  rw [Submodule.orthogonal_orthogonal]
  change action (frameUpdate (space N r) (direction N r) (x z.1)) R.val∈
    residualTensorSpace (space N r⊔ℝ ∙ direction N r)
  simpa only [←space_next] using hR

 theorem fresh_history_shift {N p r : ℕ} {S : Type} (x : S→Vector N)
    (z : S×Residual N p r) (R : Residual N p r)
    (hR : action (frameUpdate (space N r) (direction N r) (x z.1)) R.val∈Residual N p (r+1)) :
    history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) x (z.1,z.2+R)=
      history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) x z := by
  have ht := updated_residual_mem_block_orthogonal x z R hR
  change (z.1,(Block N p r).orthogonalProjectionOnto
      (tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) (z.2+R)))=
    (z.1,(Block N p r).orthogonalProjectionOnto
      (tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) z.2))
  rw [map_add,map_add,(Block N p r).orthogonalProjectionOnto_eq_zero_iff.mpr ht,add_zero]

 theorem nextResidual_coe_remainder {N p r : ℕ} {S : Type} (x : S→Vector N)
    (z : S×Residual N p r) :
    (nextResidual x z).val=
      (remainder (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) x z).val.val := by
  rw [nextResidual,LinearIsometryEquiv.coe_ofEq_apply]
  exact remainingIso_coe (space N r) (direction N r) _

 theorem remainder_shift {N p r : ℕ} {S : Type} (x : S→Vector N)
    (z : S×Residual N p r) (R : Residual N p r)
    (ht : tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) R∈(Block N p r)ᗮ) :
    remainder (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) x (z.1,z.2+R)=
      remainder (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) x z+
        ⟨tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) R,ht⟩ := by
  let t : (Block N p r)ᗮ := ⟨tensorUpdate (space N r) (direction N r)
    (direction_mem_orthogonal N r) (x z.1) R,ht⟩
  have hp : (Block N p r)ᗮ.orthogonalProjectionOnto
      (tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) R)=t :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self t
  change (Block N p r)ᗮ.orthogonalProjectionOnto
      (tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) (z.2+R))=
    (Block N p r)ᗮ.orthogonalProjectionOnto
      (tensorUpdate (space N r) (direction N r) (direction_mem_orthogonal N r) (x z.1) z.2)+t
  rw [map_add,map_add,hp]

 theorem fresh_residual_shift {N p r : ℕ} {S : Type} (x : S→Vector N)
    (z : S×Residual N p r) (R : Residual N p r)
    (hR : action (frameUpdate (space N r) (direction N r) (x z.1)) R.val∈Residual N p (r+1)) :
    (nextResidual x (z.1,z.2+R)).val=(nextResidual x z).val+
      action (frameUpdate (space N r) (direction N r) (x z.1)) R.val := by
  have ht := updated_residual_mem_block_orthogonal x z R hR
  have hh := congrArg (fun v : (Block N p r)ᗮ => v.val.val) (remainder_shift x z R ht)
  simpa only [←nextResidual_coe_remainder,Submodule.coe_add,tensorUpdate_coe] using hh

end SphericalAging.FiniteDisclosureResidualShift
