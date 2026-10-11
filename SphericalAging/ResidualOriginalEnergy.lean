module

public import SphericalAging.ResidualTensorEnergy
public import SphericalAging.FiniteDisclosureSpaceMeasurable

public section

/-! The true original tensor contributes only its residual component on
the actual vector complement. This identifies the model energy exactly. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualOriginalEnergy
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure
open ResidualTensorAlgorithm ResidualTensorEnergy TensorOrthogonalAction TensorHamiltonianRotation
open TensorResidualRotation FiniteDisclosureSpaceMeasurable
open scoped InnerProductSpace

 theorem physicalProjection_eq {N : ℕ} (W : Submodule ℝ (Vector N))
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (x : Vector N) :
    physicalProjection W F x=(rotatedSpace F W)ᗮ.starProjection x := by
  have hh := rotated_projection W F x
  change F ((Wᗮ).starProjection (F.symm x))=(rotatedSpace F W)ᗮ.starProjection x
  rw [Submodule.starProjection_orthogonal_val,Submodule.starProjection_orthogonal_val,
    map_sub,F.apply_symm_apply]
  exact congrArg (fun y => x-y) hh.symm

 theorem original_energy_eq_residual {N p : ℕ} (W : Submodule ℝ (Vector N))
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p)
    (hD : D∈(residualTensorSpace W)ᗮ) (R : residualTensorSpace (p:=p) W) (x : Vector N) :
    Hamiltonian N p (action F (D+R.val)).ofLp (physicalProjection W F x)=
      Hamiltonian N p (action F R.val).ofLp (physicalProjection W F x) := by
  let y : Wᗮ := (Wᗮ).orthogonalProjectionOnto (F.symm x)
  have hY : pureTensor (fun _ : Fin p => (y : Vector N))∈residualTensorSpace W :=
    Submodule.subset_span ⟨(fun _ => y),rfl⟩
  have hid : pureTensor (fun _ : Fin p => physicalProjection W F x)=
      action F (pureTensor (fun _ : Fin p => (y : Vector N))) := by
    rw [action_pureTensor]
    rfl
  rw [Hamiltonian_eq_tensor_inner,Hamiltonian_eq_tensor_inner,WithLp.toLp_ofLp,WithLp.toLp_ofLp,
    map_add,inner_add_left,hid,(action F).inner_map_map,(action F).inner_map_map,
    Submodule.inner_left_of_mem_orthogonal hY hD,zero_add]

end SphericalAging.ResidualOriginalEnergy
