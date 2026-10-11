module

public import SphericalAging.PredictableTensorSpanIdentification

public section

/-! Composition and involution of the literal ordered tensor action. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TensorActionComposition
open FiniteModel HardSphereDynamics AdaptiveGradientDisclosure TensorOrthogonalAction
open PredictableGramStep PredictableTensorSpanIdentification
open scoped BigOperators InnerProductSpace

theorem action_trans {N p : ℕ} (O U : Vector N≃ₗᵢ[ℝ]Vector N) (J : TensorSpace N p) :
    action O (action U J)=action (U.trans O) J := by
  classical
  let b := EuclideanSpace.basisFun (TensorIndex N p) ℝ
  have hJ : J=∑I : TensorIndex N p,J I • b I := by
    simpa only [b,EuclideanSpace.basisFun_repr] using (b.sum_repr J).symm
  rw [hJ]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  dsimp only [b]
  rw [EuclideanSpace.basisFun_apply]
  rw [action_basis,rotatedFamily,action_pureTensor,action_basis,rotatedFamily]
  rfl

theorem action_refl {N p : ℕ} (J : TensorSpace N p) :
    action (LinearIsometryEquiv.refl ℝ (Vector N)) J=J := by
  classical
  have hU : (LinearIsometryEquiv.refl ℝ (Vector N)).trans (LinearIsometryEquiv.refl ℝ (Vector N))=
      LinearIsometryEquiv.refl ℝ (Vector N) := rfl
  have hh := action_trans (p:=p) (LinearIsometryEquiv.refl ℝ (Vector N))
    (LinearIsometryEquiv.refl ℝ (Vector N)) J
  rw [hU] at hh
  exact (action (LinearIsometryEquiv.refl ℝ (Vector N))).injective hh

theorem frame_tensor_involution {N p : ℕ} (W : Submodule ℝ (Vector N)) (e x : Vector N)
    (J : TensorSpace N p) : action (frameUpdate W e x) (action (frameUpdate W e x) J)=J := by
  rw [action_trans]
  have he : (frameUpdate W e x).trans (frameUpdate W e x)=LinearIsometryEquiv.refl ℝ (Vector N) := by
    apply LinearIsometryEquiv.ext
    intro z
    change frameUpdate W e x (frameUpdate W e x z)=z
    exact frameUpdate_involution W e x z
  rw [he,action_refl]

end SphericalAging.TensorActionComposition
