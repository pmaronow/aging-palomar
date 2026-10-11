module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

public section

/-! An actual isometry between coordinate subspaces extends to an isometric
embedding of the whole Hilbert space, with the orthogonal residual retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalCoordinateExtension
variable {G E F : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

instance rangeComplete (U : G →ₗᵢ[ℝ] E) : CompleteSpace U.toLinearMap.range :=
  (show IsComplete (U.toLinearMap.range : Set E) from
    U.isometry.isUniformInducing.isComplete_range).completeSpace_coe

@[expose] def embedding (U : G →ₗᵢ[ℝ] E) (W : G →ₗᵢ[ℝ] F) : E →ₗᵢ[ℝ] WithLp 2 (F × E) :=
  ((W.comp U.equivRange.symm.toLinearIsometry).withLpProdMap 2
    U.toLinearMap.rangeᗮ.subtypeₗᵢ).comp
      U.toLinearMap.range.orthogonalDecomposition.toLinearIsometry

theorem embedding_apply (U : G →ₗᵢ[ℝ] E) (W : G →ₗᵢ[ℝ] F) (x : E) :
    embedding U W x=WithLp.toLp 2
      (W (U.equivRange.symm (U.toLinearMap.range.orthogonalProjectionOnto x)),
        x-U.toLinearMap.range.starProjection x) := by
  simp [embedding,Submodule.orthogonalDecomposition_apply,
    Submodule.orthogonalProjectionOnto_orthogonal]

theorem embedding_coordinate (U : G →ₗᵢ[ℝ] E) (W : G →ₗᵢ[ℝ] F) (z : G) :
    embedding U W (U z)=WithLp.toLp 2 (W z,0) := by
  have he : (U.equivRange z : E)=U z := rfl
  have hP : U.toLinearMap.range.orthogonalProjectionOnto (U z)=U.equivRange z := by
    simpa only [he] using U.toLinearMap.range.orthogonalProjectionOnto_mem_subspace_eq_self (U.equivRange z)
  have hS : U.toLinearMap.range.starProjection (U z)=U z := by
    simpa only [he] using U.toLinearMap.range.starProjection_mem_subspace_eq_self (U.equivRange z)
  rw [embedding_apply,hP,hS,U.equivRange.symm_apply_apply,sub_self]

end SphericalAging.OrthogonalCoordinateExtension
