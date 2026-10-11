module

public import SphericalAging.BinaryRootTransport
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

/-! Actual conjugation of bounded operators represented by completed tensors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open UniformSpace
open scoped InnerProductSpace TensorProduct
namespace SphericalAging.TensorEmbeddingConjugation
open CausalTree CausalTree.HilbertDatum BinaryRootTransport HilbertSchmidtTensor

theorem tensorEmbedding_operator_apply (A B C D : HilbertDatum)
    (f : A.Carrier →ₗᵢ[ℝ] C.Carrier) (g : B.Carrier →ₗᵢ[ℝ] D.Carrier)
    (u : (tensor A B).Carrier) (z : D.Carrier) :
    operator C D (tensorEmbedding A B C D f g u) z=
      f (operator A B u (g.toContinuousLinearMap.adjoint z)) := by
  refine Completion.induction_on u
    (isClosed_eq
      (((operatorL C D).continuous.comp (tensorEmbedding A B C D f g).continuous).clm_apply continuous_const)
      (f.continuous.comp ((operatorL A B).continuous.clm_apply continuous_const))) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    change operator C D (tensorEmbedding A B C D f g (pure A B x y)) z=
      f (operator A B (pure A B x y) (g.toContinuousLinearMap.adjoint z))
    rw [tensorEmbedding_pure,operator_pure,operator_pure,map_smul]
    rw [ContinuousLinearMap.adjoint_inner_right]
    rfl
  | add t t' ht ht' =>
    simp only [Completion.coe_add,map_add,←operatorL_apply,map_add,
      ContinuousLinearMap.add_apply]
    exact congrArg₂ (·+·) ht ht'

theorem tensorEmbedding_operator (A B C D : HilbertDatum)
    (f : A.Carrier →ₗᵢ[ℝ] C.Carrier) (g : B.Carrier →ₗᵢ[ℝ] D.Carrier)
    (u : (tensor A B).Carrier) :
    operator C D (tensorEmbedding A B C D f g u)=
      f.toContinuousLinearMap.comp ((operator A B u).comp g.toContinuousLinearMap.adjoint) := by
  ext z
  exact tensorEmbedding_operator_apply A B C D f g u z

theorem tensorEmbedding_comp (A B C D E F : HilbertDatum)
    (f : A.Carrier →ₗᵢ[ℝ] C.Carrier) (g : B.Carrier →ₗᵢ[ℝ] D.Carrier)
    (f' : C.Carrier →ₗᵢ[ℝ] E.Carrier) (g' : D.Carrier →ₗᵢ[ℝ] F.Carrier)
    (u : (tensor A B).Carrier) :
    tensorEmbedding C D E F f' g' (tensorEmbedding A B C D f g u)=
      tensorEmbedding A B E F (f'.comp f) (g'.comp g) u := by
  refine Completion.induction_on u
    (isClosed_eq ((tensorEmbedding C D E F f' g').continuous.comp
      (tensorEmbedding A B C D f g).continuous)
      (tensorEmbedding A B E F (f'.comp f) (g'.comp g)).continuous) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    change tensorEmbedding C D E F f' g' (tensorEmbedding A B C D f g (pure A B x y))=
      tensorEmbedding A B E F (f'.comp f) (g'.comp g) (pure A B x y)
    rw [tensorEmbedding_pure,tensorEmbedding_pure,tensorEmbedding_pure]
    rfl
  | add t t' ht ht' => simp only [Completion.coe_add,map_add,ht,ht']

end SphericalAging.TensorEmbeddingConjugation
