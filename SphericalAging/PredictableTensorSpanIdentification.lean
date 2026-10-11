module

public import SphericalAging.PredictableTensorDisclosureStep

public section

/-! The constructed Householder tensor disclosure corresponds exactly to
the new actual query span when a fresh vector direction is read. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PredictableTensorSpanIdentification
open Set FiniteModel HardSphereDynamics AdaptiveGradientDisclosure
open PredictableGramStep TensorOrthogonalAction TensorResidualRotation PredictableTensorDisclosureStep
open scoped InnerProductSpace BigOperators

 theorem frameUpdate_involution {N : ℕ} (W : Submodule ℝ (Vector N)) (e x z : Vector N) :
    frameUpdate W e x (frameUpdate W e x z)=z := by
  classical
  unfold frameUpdate
  split_ifs
  · rfl
  · exact Submodule.reflection_reflection _ _

 theorem sup_span_residual {N : ℕ} (W : Submodule ℝ (Vector N)) (x : Vector N) :
    W⊔ℝ ∙ PredictableGramStep.residual W x=W⊔ℝ ∙ x := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro z hz
    simp only [mem_singleton_iff] at hz
    subst z
    exact (W⊔ℝ ∙ x).sub_mem
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_left (W.orthogonalProjectionOnto x).property)
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro z hz
    simp only [mem_singleton_iff] at hz
    subst z
    have h1 : W.starProjection x∈W⊔ℝ ∙ PredictableGramStep.residual W x :=
      Submodule.mem_sup_left (W.orthogonalProjectionOnto x).property
    have h2 : PredictableGramStep.residual W x∈W⊔ℝ ∙ PredictableGramStep.residual W x :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have hh := (W⊔ℝ ∙ PredictableGramStep.residual W x).add_mem h1 h2
    have he : W.starProjection x+PredictableGramStep.residual W x=x := by
      unfold PredictableGramStep.residual
      abel
    rw [he] at hh
    exact hh

 theorem sup_span_unitResidual {N : ℕ} (W : Submodule ℝ (Vector N)) {x : Vector N} (hx : x∉W) :
    W⊔ℝ ∙ unitResidual W x=W⊔ℝ ∙ x := by
  have hn : ‖PredictableGramStep.residual W x‖≠0 := norm_ne_zero_iff.mpr
    (fun hz => hx ((residual_eq_zero_iff W x).mp hz))
  rw [unitResidual,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hn))]
  exact sup_span_residual W x

 theorem rotated_newSpan {N : ℕ} (W : Submodule ℝ (Vector N)) {e x : Vector N}
    (he : e∈Wᗮ) (hen : ‖e‖=1) (hx : x∉W) :
    rotatedSpace (frameUpdate W e x) (W⊔ℝ ∙ e)=W⊔ℝ ∙ x := by
  unfold rotatedSpace
  rw [Submodule.map_sup]
  have hw := frameUpdate_rotatedSpace W he x
  change W.map (frameUpdate W e x).toLinearEquiv.toLinearMap=W at hw
  rw [hw,Submodule.map_span]
  have himg : (frameUpdate W e x).toLinearEquiv.toLinearMap '' ({e}:Set (Vector N))={unitResidual W x} := by
    rw [Set.image_singleton]
    congr 1
    exact frameUpdate_new_direction W hen hx
  rw [himg]
  exact sup_span_unitResidual W hx

 theorem tensor_residual_newSpan {N p : ℕ} (W : Submodule ℝ (Vector N)) {e x : Vector N}
    (he : e∈Wᗮ) (hen : ‖e‖=1) (hx : x∉W) :
    (residualTensorSpace (p:=p) (W⊔ℝ ∙ e)).map (action (frameUpdate W e x)).toLinearEquiv.toLinearMap=
      residualTensorSpace (p:=p) (W⊔ℝ ∙ x) := by
  rw [residualTensorSpace_rotated,rotated_newSpan W he hen hx]

end SphericalAging.PredictableTensorSpanIdentification
