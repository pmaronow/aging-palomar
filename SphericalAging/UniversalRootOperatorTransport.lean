module

public import SphericalAging.UniversalRootFixedAmbient
public import SphericalAging.TensorEmbeddingConjugation

public section

/-! The source conjugated operators and their literal zero extension to a fixed
auxiliary Hilbert space, proved from genuine completed-tensor transport. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
namespace SphericalAging.UniversalRootOperatorTransport
open CausalTree CausalTree.HilbertDatum UniversalRootInterval UniversalRootKernel
open HeightCoordinateEmbedding BinaryRootTransport UniversalRootFixedAmbient
open HilbertSchmidtTensor TensorEmbeddingConjugation
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

theorem fixedTransport_eq (hK : ¬Module.Finite ℝ K) (v : Space 2) (hv : ‖v‖=1)
    (u : TensorSpace 2) :
    fixedTransport hK v hv u=tensorEmbedding (spaceDatum 2) (spaceDatum 2)
      (fixedDatum K) (fixedDatum K) (fixedEmbedding hK v hv) (fixedEmbedding hK v hv) (binaryEquiv u) := by
  change tensorEmbedding _ _ _ _ _ _ (tensorEmbedding _ _ _ _ _ _ (binaryEquiv u))=_
  exact tensorEmbedding_comp _ _ _ _ _ _ _ _ _ _ _

theorem fixedTransport_conjugation (hK : ¬Module.Finite ℝ K)
    (v : Space 2) (hv : ‖v‖=1) (u : TensorSpace 2) :
    operator (fixedDatum K) (fixedDatum K) (fixedTransport hK v hv u)=
      (fixedEmbedding hK v hv).toContinuousLinearMap.comp
        ((operator (spaceDatum 2) (spaceDatum 2) (binaryEquiv u)).comp
          (fixedEmbedding hK v hv).toContinuousLinearMap.adjoint) := by
  rw [fixedTransport_eq]
  exact tensorEmbedding_operator _ _ _ _ _ _ _

@[expose] def fixedIntervalInclusion (hK : ¬Module.Finite ℝ K) : IntervalL2 →ₗᵢ[ℝ] FixedAmbient K :=
  (residualEmbedding (SeparableHilbertEmbedding.treeInto hK 2)).comp intervalInclusion

theorem fixedIntervalInclusion_apply (hK : ¬Module.Finite ℝ K) (f : IntervalL2) :
    fixedIntervalInclusion hK f=WithLp.toLp 2 (f,(0:K)) := by
  change residualEmbedding _ (WithLp.toLp 2 (f,0))=_
  rw [residualEmbedding_apply,map_zero]

theorem fixedIntervalInclusion_adjoint (hK : ¬Module.Finite ℝ K) (x : FixedAmbient K) :
    (fixedIntervalInclusion hK).toContinuousLinearMap.adjoint x=(WithLp.ofLp x).1 := by
  apply ext_inner_left ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (fixedIntervalInclusion hK f) x=_
  rw [fixedIntervalInclusion_apply,WithLp.prod_inner_apply]
  simp

theorem fixedKernelInclusion_eq (hK : ¬Module.Finite ℝ K) (k : KernelL2) :
    fixedKernelInclusion hK k=tensorEmbedding intervalDatum intervalDatum
      (fixedDatum K) (fixedDatum K) (fixedIntervalInclusion hK) (fixedIntervalInclusion hK)
        (kernelEquiv.symm k) := by
  change tensorEmbedding _ _ _ _ _ _ (tensorEmbedding _ _ _ _ _ _ (kernelEquiv.symm k))=_
  exact tensorEmbedding_comp _ _ _ _ _ _ _ _ _ _ _

theorem fixedKernelInclusion_operator (hK : ¬Module.Finite ℝ K)
    (k : KernelL2) (x : FixedAmbient K) :
    operator (fixedDatum K) (fixedDatum K) (fixedKernelInclusion hK k) x=
      WithLp.toLp 2 (operatorOfKernel k (WithLp.ofLp x).1,(0:K)) := by
  rw [fixedKernelInclusion_eq,tensorEmbedding_operator_apply,
    fixedIntervalInclusion_adjoint,fixedIntervalInclusion_apply]
  rfl

theorem fixedUniversalOperator_zeroExtension (hK : ¬Module.Finite ℝ K) (x : FixedAmbient K) :
    operator (fixedDatum K) (fixedDatum K) (fixedKernelInclusion hK kernelL2) x=
      WithLp.toLp 2 (universalOperator (WithLp.ofLp x).1,(0:K)) :=
  fixedKernelInclusion_operator hK kernelL2 x

end SphericalAging.UniversalRootOperatorTransport
