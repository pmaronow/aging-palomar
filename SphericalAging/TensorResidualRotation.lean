module

public import SphericalAging.TensorOrthogonalAction

public section

/-! Actual tensor residual subspaces transform under the literal vector
rotation. This identifies the p-fold undisclosed subspace in source10.6. -/
noncomputable section
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TensorResidualRotation
open Set FiniteModel AdaptiveGradientDisclosure TensorOrthogonalAction
open scoped InnerProductSpace BigOperators

@[expose]  def rotatedSpace {N : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (W : Submodule ℝ (Vector N)) :
    Submodule ℝ (Vector N) := W.map O.toLinearEquiv.toLinearMap

 theorem orthogonal_rotated {N : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (W : Submodule ℝ (Vector N))
    {x : Vector N} (hx : x∈Wᗮ) : O x∈(rotatedSpace O W)ᗮ := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := Submodule.mem_map.mp hy
  change ⟪O z,O x⟫_ℝ=0
  rw [O.inner_map_map]
  exact hx z hz

 theorem orthogonal_inverse {N : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (W : Submodule ℝ (Vector N))
    {x : Vector N} (hx : x∈(rotatedSpace O W)ᗮ) : O.symm x∈Wᗮ := by
  intro y hy
  have hh := hx (O y) (Submodule.mem_map.mpr ⟨y,hy,rfl⟩)
  rw [←O.apply_symm_apply x,O.inner_map_map] at hh
  exact hh

 theorem action_mem_residual {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (W : Submodule ℝ (Vector N))
    {J : TensorSpace N p} (hJ : J∈residualTensorSpace W) :
    action O J∈residualTensorSpace (rotatedSpace O W) := by
  classical
  induction hJ using Submodule.span_induction with
  | mem J hJ =>
    obtain ⟨v,rfl⟩ := hJ
    rw [action_pureTensor]
    exact Submodule.subset_span ⟨(fun k => ⟨O (v k),orthogonal_rotated O W (v k).property⟩),rfl⟩
  | zero => rw [map_zero];exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add];exact Submodule.add_mem _ ihu ihv
  | smul c v hv ih => rw [map_smul];exact Submodule.smul_mem _ c ih

 theorem residualTensorSpace_rotated {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (W : Submodule ℝ (Vector N)) :
    (residualTensorSpace (p:=p) W).map (action O).toLinearEquiv.toLinearMap=
      residualTensorSpace (rotatedSpace O W) := by
  classical
  apply le_antisymm
  · intro J hJ
    obtain ⟨K,hK,rfl⟩ := Submodule.mem_map.mp hJ
    exact action_mem_residual O W hK
  · apply Submodule.span_le.mpr
    intro J hJ
    obtain ⟨v,rfl⟩ := hJ
    let u : Fin p→Wᗮ := fun k => ⟨O.symm (v k),orthogonal_inverse O W (v k).property⟩
    apply Submodule.mem_map.mpr
    refine ⟨pureTensor (fun k => (u k:Vector N)),Submodule.subset_span ⟨u,rfl⟩,?_⟩
    change action O (pureTensor (fun k => (u k:Vector N)))=pureTensor (fun k => (v k:Vector N))
    rw [action_pureTensor]
    congr 1
    funext k
    exact O.apply_symm_apply (v k)

end SphericalAging.TensorResidualRotation
