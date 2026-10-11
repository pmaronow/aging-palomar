module

public import SphericalAging.UniversalRootTransportConvergence
public import SphericalAging.SeparableHilbertEmbedding

public section

/-! Actual height-coordinate embeddings into any fixed infinite-dimensional
real Hilbert space, and the universal-root limit in that fixed ambient space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.UniversalRootFixedAmbient
open CausalTree CausalTree.HilbertDatum TreeCeilings UniversalRootInterval UniversalRootKernel
open HeightCoordinateEmbedding BinaryRootTransport
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

@[expose] abbrev FixedAmbient (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K] :=
  WithLp 2 (IntervalL2 × K)

@[expose, reducible] def fixedDatum (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] : HilbertDatum := ⟨FixedAmbient K,inferInstance,inferInstance,inferInstance⟩

@[expose] def residualEmbedding (J : Space 2 →ₗᵢ[ℝ] K) : Ambient →ₗᵢ[ℝ] FixedAmbient K where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (IntervalL2 × K)).symm.toLinearMap.comp
    ((LinearMap.prodMap (LinearMap.id : IntervalL2 →ₗ[ℝ] IntervalL2) J.toLinearMap).comp
      (WithLp.linearEquiv 2 ℝ (IntervalL2 × Space 2)).toLinearMap)
  norm_map' x := by
    change ‖WithLp.toLp 2 ((WithLp.ofLp x).1,J (WithLp.ofLp x).2)‖=‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change ‖(WithLp.ofLp x).1‖^2+‖J (WithLp.ofLp x).2‖^2=
      ‖(WithLp.ofLp x).1‖^2+‖(WithLp.ofLp x).2‖^2
    rw [J.norm_map]

theorem residualEmbedding_apply (J : Space 2 →ₗᵢ[ℝ] K) (f : IntervalL2) (x : Space 2) :
    residualEmbedding J (WithLp.toLp 2 (f,x))=WithLp.toLp 2 (f,J x) := rfl

@[expose] def fixedEmbedding (hK : ¬Module.Finite ℝ K) (v : Space 2) (hv : ‖v‖=1) :
    Space 2 →ₗᵢ[ℝ] FixedAmbient K :=
  (residualEmbedding (SeparableHilbertEmbedding.treeInto hK 2)).comp (embedding v hv)

theorem fixedEmbedding_vector (hK : ¬Module.Finite ℝ K) (v : Space 2) (hv : ‖v‖=1) :
    fixedEmbedding hK v hv v=WithLp.toLp 2 (one,(0:K)) := by
  change residualEmbedding _ (embedding v hv v)=_
  rw [embedding_vector,residualEmbedding_apply,map_zero]

@[expose] def ambientTensorEmbedding (hK : ¬Module.Finite ℝ K) :
    (tensor ambientDatum ambientDatum).Carrier →ₗᵢ[ℝ] (tensor (fixedDatum K) (fixedDatum K)).Carrier :=
  tensorEmbedding ambientDatum ambientDatum (fixedDatum K) (fixedDatum K)
    (residualEmbedding (SeparableHilbertEmbedding.treeInto hK 2))
    (residualEmbedding (SeparableHilbertEmbedding.treeInto hK 2))

@[expose] def fixedTransport (hK : ¬Module.Finite ℝ K) (v : Space 2) (hv : ‖v‖=1) :
    TensorSpace 2 →ₗᵢ[ℝ] (tensor (fixedDatum K) (fixedDatum K)).Carrier :=
  (ambientTensorEmbedding hK).comp (transport v hv)

theorem fixedTransport_pure (hK : ¬Module.Finite ℝ K) (v x y : Space 2) (hv : ‖v‖=1) :
    fixedTransport hK v hv (TreeRootBlocks.binaryPure x y)=
      pure (fixedDatum K) (fixedDatum K) (fixedEmbedding hK v hv x) (fixedEmbedding hK v hv y) := by
  change ambientTensorEmbedding hK (transport v hv (TreeRootBlocks.binaryPure x y))=_
  rw [transport_pure]
  exact tensorEmbedding_pure _ _ _ _ _ _ _ _

@[expose] def fixedKernelInclusion (hK : ¬Module.Finite ℝ K) :
    KernelL2 →ₗᵢ[ℝ] (tensor (fixedDatum K) (fixedDatum K)).Carrier :=
  (ambientTensorEmbedding hK).comp kernelInclusion

theorem fixedKernelInclusion_product (hK : ¬Module.Finite ℝ K) (f g : IntervalL2) :
    fixedKernelInclusion hK (LpProductTensor.product f g)=
      pure (fixedDatum K) (fixedDatum K) (WithLp.toLp 2 (f,(0:K))) (WithLp.toLp 2 (g,(0:K))) := by
  change ambientTensorEmbedding hK (kernelInclusion (LpProductTensor.product f g))=_
  rw [kernelInclusion_product]
  change tensorEmbedding _ _ _ _ _ _ _=_
  rw [tensorEmbedding_pure,residualEmbedding_apply,residualEmbedding_apply,map_zero]

theorem root_transport_tendsto (hK : ¬Module.Finite ℝ K)
    (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    Tendsto (fun n => fixedTransport hK (v n) (hv n) (graftTensorAdjoint 2 (v n))) atTop
      (𝓝 (fixedKernelInclusion hK kernelL2)) :=
  (ambientTensorEmbedding hK).continuous.tendsto _ |>.comp
    (UniversalRootTransportConvergence.root_transport_tendsto v hv hf)

theorem source13_2_embeddings (hK : ¬Module.Finite ℝ K)
    (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    (∀ n, fixedEmbedding hK (v n) (hv n) (v n)=WithLp.toLp 2 (one,(0:K))) ∧
      Tendsto (fun n => fixedTransport hK (v n) (hv n) (graftTensorAdjoint 2 (v n))) atTop
        (𝓝 (fixedKernelInclusion hK kernelL2)) :=
  ⟨fun n => fixedEmbedding_vector hK (v n) (hv n),root_transport_tendsto hK v hv hf⟩

end SphericalAging.UniversalRootFixedAmbient
