module

public import SphericalAging.TensorActionComposition

public section

/-! The literal undisclosed ordered tensor space at the empty and full
vector spans. These include the rank-saturation and zero-query cases. -/
noncomputable section
set_option maxHeartbeats 350000
namespace SphericalAging.TensorBoundarySpaces
open Set FiniteModel HardSphereDynamics AdaptiveGradientDisclosure TensorOrthogonalAction
open TensorActionComposition
open scoped BigOperators InnerProductSpace

theorem pureTensor_basis {N p : ℕ} (I : TensorIndex N p) :
    pureTensor (fun k => basisVector (I k))=EuclideanSpace.single I 1 := by
  have hh := action_basis (p:=p) (LinearIsometryEquiv.refl ℝ (Vector N)) I
  simpa only [action_refl,rotatedFamily,LinearIsometryEquiv.coe_refl,id_eq] using hh.symm

theorem residualTensorSpace_bot (N p : ℕ) :
    residualTensorSpace (p:=p) (⊥ : Submodule ℝ (Vector N))=⊤ := by
  classical
  apply top_unique
  intro J _
  let b := EuclideanSpace.basisFun (TensorIndex N p) ℝ
  rw [←b.sum_repr J]
  apply Submodule.sum_mem
  intro I _
  apply Submodule.smul_mem
  rw [EuclideanSpace.basisFun_apply,←pureTensor_basis]
  exact Submodule.subset_span ⟨(fun k => ⟨basisVector (I k),by simp⟩),rfl⟩

theorem residualTensorSpace_top {N p : ℕ} (hp : 1≤p) :
    residualTensorSpace (p:=p) (⊤ : Submodule ℝ (Vector N))=⊥ := by
  classical
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro J ⟨v,rfl⟩
  have hv : ∀k : Fin p,(v k : Vector N)=0 := by
    intro k
    simpa only [Submodule.top_orthogonal_eq_bot,Submodule.mem_bot] using (v k).property
  have hp0 : Nonempty (Fin p) := ⟨⟨0,by omega⟩⟩
  letI := hp0
  simp only [Submodule.mem_bot]
  ext I
  simp only [pureTensor,WithLp.ofLp_toLp,hv,Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ (Classical.choice hp0)) rfl

end SphericalAging.TensorBoundarySpaces
