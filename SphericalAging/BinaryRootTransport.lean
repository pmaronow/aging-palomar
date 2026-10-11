module

public import SphericalAging.HeightCoordinateEmbedding
public import SphericalAging.TreeCoherentOperator

public section

/-! Canonical binary completed-tensor transport of actual root operators,
including the finite right-unit removal and actual height-block pairings. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open UniformSpace
open scoped TensorProduct InnerProductSpace
namespace SphericalAging.BinaryRootTransport
open CausalTree CausalTree.HilbertDatum TreeRootBlocks TreeCoherentRoot
open HeightCoordinateEmbedding UniversalRootInterval HeightCoordinateIntervals

@[expose] def tensorEmbedding (A B C D : HilbertDatum)
    (f : A.Carrier →ₗᵢ[ℝ] C.Carrier) (g : B.Carrier →ₗᵢ[ℝ] D.Carrier) :
    (tensor A B).Carrier →ₗᵢ[ℝ] (tensor C D).Carrier :=
  (TensorProduct.mapIsometry f g).completion

theorem tensorEmbedding_pure (A B C D : HilbertDatum)
    (f : A.Carrier →ₗᵢ[ℝ] C.Carrier) (g : B.Carrier →ₗᵢ[ℝ] D.Carrier)
    (x : A.Carrier) (y : B.Carrier) :
    tensorEmbedding A B C D f g (pure A B x y)=pure C D (f x) (g y) := by
  rw [tensorEmbedding,CausalTree.HilbertDatum.pure,LinearIsometry.completion_apply_coe]
  simp only [TensorProduct.mapIsometry_apply,TensorProduct.map_tmul]
  rfl

@[expose] def binaryEquiv : TensorSpace 2 ≃ₗᵢ[ℝ] (tensor (spaceDatum 2) (spaceDatum 2)).Carrier :=
  TreeCoherentOperator.binaryEquiv

theorem binaryEquiv_pure (x y : Space 2) :
    binaryEquiv (binaryPure x y)=pure (spaceDatum 2) (spaceDatum 2) x y :=
  TreeCoherentOperator.binaryEquiv_pure x y

@[expose, reducible] def ambientDatum : HilbertDatum := ⟨Ambient,inferInstance,inferInstance,inferInstance⟩

@[expose] def transport (v : Space 2) (hv : ‖v‖=1) :
    TensorSpace 2 →ₗᵢ[ℝ] (tensor ambientDatum ambientDatum).Carrier :=
  (tensorEmbedding (spaceDatum 2) (spaceDatum 2) ambientDatum ambientDatum
    (embedding v hv) (embedding v hv)).comp binaryEquiv.toLinearIsometry

theorem transport_pure (v : Space 2) (hv : ‖v‖=1) (x y : Space 2) :
    transport v hv (binaryPure x y)=pure ambientDatum ambientDatum (embedding v hv x) (embedding v hv y) := by
  change tensorEmbedding _ _ _ _ _ _ (binaryEquiv (binaryPure x y))=_
  rw [binaryEquiv_pure,tensorEmbedding_pure]

theorem transport_pairing (v : Space 2) (hv : ‖v‖=1) (u : TensorSpace 2) (x y : Space 2) :
    inner ℝ (transport v hv u)
      (pure ambientDatum ambientDatum (embedding v hv x) (embedding v hv y))=
        inner ℝ u (binaryPure x y) := by
  rw [←transport_pure,(transport v hv).inner_map_map]

theorem transport_height_rankOne (v : Space 2) (hv : ‖v‖=1) (i j : ℕ) :
    transport v hv (binaryPure (heightProjection i v) (heightProjection j v))=
      pure ambientDatum ambientDatum (WithLp.toLp 2 (heightIndicator v i,0))
        (WithLp.toLp 2 (heightIndicator v j,0)) := by
  rw [transport_pure,embedding_height,embedding_height]

theorem coherentRoot_transported_block (v x y : Space 2) (hv : ‖v‖=1) (i j : ℕ) :
    inner ℝ (transport v hv (coherentRoot v))
      (pure ambientDatum ambientDatum (embedding v hv (heightProjection i x))
        (embedding v hv (heightProjection j y)))=
      (TreeCeilings.cubicWeight v (max i j+1))⁻¹*
        (inner ℝ v (heightProjection i x)*inner ℝ v (heightProjection j y)) := by
  rw [transport_pairing]
  exact coherentRoot_block_pairing v x y i j

@[expose] def intervalInclusion : IntervalL2 →ₗᵢ[ℝ] Ambient where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (IntervalL2 × Space 2)).symm.toLinearMap.comp
    (LinearMap.inl ℝ IntervalL2 (Space 2))
  norm_map' f := by
    change ‖WithLp.toLp 2 (f,(0:Space 2))‖=‖f‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [WithLp.prod_norm_sq_eq_of_L2]

theorem intervalInclusion_apply (f : IntervalL2) : intervalInclusion f=WithLp.toLp 2 (f,0) := rfl

@[expose] def kernelInclusion : KernelL2 →ₗᵢ[ℝ] (tensor ambientDatum ambientDatum).Carrier :=
  (tensorEmbedding intervalDatum intervalDatum ambientDatum ambientDatum intervalInclusion intervalInclusion).comp
    kernelEquiv.symm.toLinearIsometry

theorem kernelInclusion_product (f g : IntervalL2) :
    kernelInclusion (LpProductTensor.product f g)=
      pure ambientDatum ambientDatum (WithLp.toLp 2 (f,0)) (WithLp.toLp 2 (g,0)) := by
  have hp : kernelEquiv (pure intervalDatum intervalDatum f g)=LpProductTensor.product f g :=
    LpProductTensor.completedIsometry_tmul f g
  rw [←hp]
  change tensorEmbedding _ _ _ _ _ _ (kernelEquiv.symm (kernelEquiv (pure intervalDatum intervalDatum f g)))=_
  rw [LinearIsometryEquiv.symm_apply_apply,tensorEmbedding_pure]
  rfl

end SphericalAging.BinaryRootTransport
