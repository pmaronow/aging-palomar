module

public import SphericalAging.TensorActionComposition

public section

/-! The actual fresh Householder tensor remainder equals the literal
orthogonal projection onto the tensor space undisclosed after the query. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PredictableTensorProjectionIdentification
open Set FiniteModel AdaptiveGradientDisclosure PredictableGramStep TensorOrthogonalAction
open TensorActionComposition PredictableTensorDisclosureStep PredictableTensorSpanIdentification
open scoped InnerProductSpace

theorem residualTensorSpace_antitone {N p : ℕ} {W V : Submodule ℝ (Vector N)} (h : W≤V) :
    residualTensorSpace (p:=p) V≤residualTensorSpace W := by
  apply Submodule.span_le.mpr
  rintro J ⟨v,rfl⟩
  exact Submodule.subset_span ⟨(fun i => ⟨(v i:Vector N),
    (Submodule.orthogonal_le h) (v i).property⟩),rfl⟩

theorem newResidualSubspace_map_subtype {N p : ℕ} (W : Submodule ℝ (Vector N)) (e : Vector N) :
    (newResidualSubspace (p:=p) W e).map (residualTensorSpace W).subtype=
      residualTensorSpace (p:=p) (W⊔ℝ ∙ e) := by
  rw [newResidualSubspace,Submodule.map_comap_eq,Submodule.range_subtype]
  exact inf_eq_right.mpr (residualTensorSpace_antitone (show W≤W⊔ℝ ∙ e from le_sup_left))

theorem newResidualSubspace_projection_coe {N p : ℕ}
    (W : Submodule ℝ (Vector N)) (e : Vector N) (J : residualTensorSpace (p:=p) W) :
    ((newResidualSubspace W e).starProjection J:TensorSpace N p)=
      (residualTensorSpace (W⊔ℝ ∙ e)).starProjection (J:TensorSpace N p) := by
  have hh := (residualTensorSpace (p:=p) W).subtypeₗᵢ.map_starProjection
    (newResidualSubspace W e) J
  change ((newResidualSubspace W e).starProjection J:TensorSpace N p)=
    ((newResidualSubspace W e).map (residualTensorSpace W).subtype).starProjection
      (J:TensorSpace N p) at hh
  simpa only [newResidualSubspace_map_subtype] using hh

theorem remainder_projection_coe {N p : ℕ} {S : Type*}
    (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    (x : S→Vector N) (z : S×residualTensorSpace (p:=p) W) :
    (remainder W e he x z).val.val=
      (residualTensorSpace (W⊔ℝ ∙ e)).starProjection
        (action (frameUpdate W e (x z.1)) (z.2:TensorSpace N p)) := by
  change ((freshBlock (p:=p) W e)ᗮ.starProjection (tensorUpdate W e he (x z.1) z.2):TensorSpace N p)=_
  simp only [freshBlock,Submodule.orthogonal_orthogonal]
  exact newResidualSubspace_projection_coe W e _

theorem actual_query_remainder {N p : ℕ} {S : Type*}
    (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ) (hen : ‖e‖=1)
    (x : S→Vector N) (z : S×residualTensorSpace (p:=p) W) (hz : x z.1∉W) :
    action (frameUpdate W e (x z.1))
      (remainder W e he x z).val.val=
      (residualTensorSpace (W⊔ℝ ∙ x z.1)).starProjection (z.2:TensorSpace N p) := by
  rw [remainder_projection_coe]
  have hh := (action (frameUpdate W e (x z.1))).toLinearIsometry.map_starProjection
    (residualTensorSpace (p:=p) (W⊔ℝ ∙ e))
    (action (frameUpdate W e (x z.1)) (z.2:TensorSpace N p))
  change action (frameUpdate W e (x z.1))
      ((residualTensorSpace (W⊔ℝ ∙ e)).starProjection
        (action (frameUpdate W e (x z.1)) (z.2:TensorSpace N p)))=
    ((residualTensorSpace (W⊔ℝ ∙ e)).map
      (action (frameUpdate W e (x z.1))).toLinearEquiv.toLinearMap).starProjection
        (action (frameUpdate W e (x z.1)) (action (frameUpdate W e (x z.1)) (z.2:TensorSpace N p))) at hh
  simpa only [tensor_residual_newSpan W he hen hz,frame_tensor_involution] using hh

theorem dependent_query_span {N : ℕ} (W : Submodule ℝ (Vector N))
    {x : Vector N} (hx : x∈W) : W⊔ℝ ∙ x=W :=
  sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem x W).mpr hx)

theorem dependent_query_remainder {N p : ℕ} (W : Submodule ℝ (Vector N))
    {x : Vector N} (hx : x∈W) (J : residualTensorSpace (p:=p) W) :
    (residualTensorSpace (W⊔ℝ ∙ x)).starProjection (J:TensorSpace N p)=J := by
  rw [dependent_query_span W hx]
  exact Submodule.starProjection_eq_self_iff.mpr J.property

end SphericalAging.PredictableTensorProjectionIdentification
