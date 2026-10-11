module

public import SphericalAging.UniversalRootOperatorTransport
public import SphericalAging.UniversalRootTrace

public section

/-! The complete universal threshold-root theorem: constructed embeddings,
actual conjugated-root Hilbert--Schmidt convergence, the literal integral
kernel, its positive rank-one frame, trace class, trace, and unit HS norm. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.UniversalRootTheorem
open CausalTree CausalTree.HilbertDatum TreeCeilings UniversalRootInterval UniversalRootKernel
open UniversalRootPrefix UniversalRootFrame UniversalRootTrace UniversalRootFixedAmbient
open UniversalRootOperatorTransport HilbertSchmidtTensor
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

theorem source13_2 (hK : ¬Module.Finite ℝ K)
    (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    (∀ n, fixedEmbedding hK (v n) (hv n) (v n)=WithLp.toLp 2 (one,(0:K))) ∧
    (∀ n, operator (fixedDatum K) (fixedDatum K)
        (fixedTransport hK (v n) (hv n) (graftTensorAdjoint 2 (v n)))=
      (fixedEmbedding hK (v n) (hv n)).toContinuousLinearMap.comp
        ((TreeCoherentOperator.rootHS (v n) |> operator (spaceDatum 2) (spaceDatum 2)).comp
          (fixedEmbedding hK (v n) (hv n)).toContinuousLinearMap.adjoint)) ∧
    Tendsto (fun n => fixedTransport hK (v n) (hv n) (graftTensorAdjoint 2 (v n))) atTop
      (𝓝 (fixedKernelInclusion hK kernelL2)) ∧
    (∀ x : FixedAmbient K, operator (fixedDatum K) (fixedDatum K)
        (fixedKernelInclusion hK kernelL2) x=
      WithLp.toLp 2 (universalOperator (WithLp.ofLp x).1,(0:K))) ∧
    (∀ f g : IntervalL2, inner ℝ f (universalOperator g)=
      ∫ z, f z.1*kernel z*g z.2 ∂unitMeasure.prod unitMeasure) ∧
    (∀ f : IntervalL2, 0 ≤ inner ℝ f (universalOperator f)) ∧
    (universalRoot=(Real.sqrt 2)⁻¹ • pure intervalDatum intervalDatum one one+
      (2*Real.sqrt 2)⁻¹ • ∫ z,weightedPrefix z ∂unitMeasure) ∧
    (∀ (ι : Type) (b : HilbertBasis ι ℝ IntervalL2),
      HasSum (fun i => |inner ℝ (b i) (universalOperator (b i))|) (Real.sqrt 2)) ∧
    (∃ (s : Set IntervalL2) (b : HilbertBasis s ℝ IntervalL2),
      Summable (fun i => |inner ℝ (b i) (universalOperator (b i))|) ∧
        (∑' i,inner ℝ (b i) (universalOperator (b i)))=Real.sqrt 2) ∧
    ‖universalRoot‖=1 := by
  refine ⟨fun n => fixedEmbedding_vector hK (v n) (hv n),?_,
    UniversalRootFixedAmbient.root_transport_tendsto hK v hv hf,
    fixedUniversalOperator_zeroExtension hK,universalOperator_pairing,
    universalOperator_positive,universalRoot_frame,?_,universalOperator_traceClass,
    universalRoot_norm⟩
  · intro n
    exact fixedTransport_conjugation hK (v n) (hv n) (graftTensorAdjoint 2 (v n))
  · intro ι b
    exact universalOperator_absolute_trace b

end SphericalAging.UniversalRootTheorem
