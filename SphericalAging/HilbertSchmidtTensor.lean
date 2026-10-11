module

public import SphericalAging.HilbertTensorContraction

public section

/-! The genuine completed rank-one Hilbert--Schmidt space and its faithful
realization as bounded operators. The Hilbert norm is the actual Hilbert tensor
norm; the operator embedding is constructed and proved injective. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace TensorProduct
open UniformSpace Set
namespace SphericalAging.HilbertSchmidtTensor
open CausalTree CausalTree.HilbertDatum HilbertTensorContraction

@[expose] def swap (A B : HilbertDatum) : (tensor A B).Carrier ≃ₗᵢ[ℝ] (tensor B A).Carrier :=
  completionCongr (TensorProduct.commIsometry ℝ A.Carrier B.Carrier)

@[simp] theorem swap_pure (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) :
    swap A B (pure A B x y)=pure B A y x := by
  rw [swap,CausalTree.HilbertDatum.pure,completionCongr_coe]
  rfl

theorem contractLeft_parameter_add (A B : HilbertDatum) (z z' : A.Carrier)
    (u : (tensor A B).Carrier) :
    contractLeft A B (z+z') u=contractLeft A B z u+contractLeft A B z' u := by
  refine Completion.induction_on u
    (isClosed_eq (contractLeft A B (z+z')).continuous
      ((contractLeft A B z).continuous.add (contractLeft A B z').continuous)) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    change contractLeft A B (z+z') (pure A B x y)=
      contractLeft A B z (pure A B x y)+contractLeft A B z' (pure A B x y)
    rw [contractLeft_pure,contractLeft_pure,contractLeft_pure,inner_add_left,add_smul]
  | add t t' ht ht' =>
    simp only [Completion.coe_add,map_add,ht,ht']
    abel

theorem contractLeft_parameter_smul (A B : HilbertDatum) (a : ℝ) (z : A.Carrier)
    (u : (tensor A B).Carrier) :
    contractLeft A B (a • z) u=a • contractLeft A B z u := by
  refine Completion.induction_on u
    (isClosed_eq (contractLeft A B (a • z)).continuous
      ((contractLeft A B z).continuous.const_smul a)) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    change contractLeft A B (a • z) (pure A B x y)=a • contractLeft A B z (pure A B x y)
    rw [contractLeft_pure,contractLeft_pure,real_inner_smul_left,smul_smul]
  | add t t' ht ht' =>
    simp only [Completion.coe_add,map_add,ht,ht',smul_add]

/-- Canonical bounded operator of a completed rank-one tensor, with the source
orientation x⊗y ↦ (z ↦ <y,z>x). -/
@[expose] def operator (A B : HilbertDatum) (u : (tensor A B).Carrier) : B.Carrier →L[ℝ] A.Carrier :=
  ({ toFun := fun z => contractLeft B A z (swap A B u),
     map_add' := fun z z' => contractLeft_parameter_add B A z z' _,
     map_smul' := fun a z => contractLeft_parameter_smul B A a z _ } : B.Carrier →ₗ[ℝ] A.Carrier).mkContinuous
    ‖u‖ (fun z => by
      change ‖contractLeft B A z (swap A B u)‖ ≤ ‖u‖*‖z‖
      have hh := contractLeft_norm_le B A z (swap A B u)
      rw [LinearIsometryEquiv.norm_map,mul_comm] at hh
      exact hh)

@[simp] theorem operator_apply (A B : HilbertDatum) (u : (tensor A B).Carrier) (z : B.Carrier) :
    operator A B u z=contractLeft B A z (swap A B u) := rfl

@[simp] theorem operator_pure (A B : HilbertDatum) (x : A.Carrier) (y z : B.Carrier) :
    operator A B (pure A B x y) z=inner ℝ y z • x := by
  rw [operator_apply,swap_pure,contractLeft_pure,real_inner_comm z y]

/-- The embedding is a genuine continuous linear map in the tensor itself. -/
@[expose] def operatorL (A B : HilbertDatum) : (tensor A B).Carrier →L[ℝ] (B.Carrier →L[ℝ] A.Carrier) :=
  ({ toFun := operator A B,
     map_add' := by
       intro u v; ext z
       change contractLeft B A z (swap A B (u+v))=
         contractLeft B A z (swap A B u)+contractLeft B A z (swap A B v)
       rw [map_add,map_add],
     map_smul' := by
       intro a u; ext z
       change contractLeft B A z (swap A B (a • u))=a • contractLeft B A z (swap A B u)
       rw [map_smul,map_smul] } :
      (tensor A B).Carrier →ₗ[ℝ] (B.Carrier →L[ℝ] A.Carrier)).mkContinuous 1 (fun u => by
        change ‖operator A B u‖ ≤ 1*‖u‖
        rw [one_mul]
        apply (operator A B u).opNorm_le_bound (norm_nonneg _)
        intro z
        change ‖contractLeft B A z (swap A B u)‖ ≤ ‖u‖*‖z‖
        have hh := contractLeft_norm_le B A z (swap A B u)
        rw [LinearIsometryEquiv.norm_map,mul_comm] at hh
        exact hh)

@[simp] theorem operatorL_apply (A B : HilbertDatum) (u : (tensor A B).Carrier) :
    operatorL A B u=operator A B u := rfl

/-- Canonical tensor/operator duality, proved on actual pure tensors and extended
through algebraic tensor generation and completion density. -/
theorem operator_pairing (A B : HilbertDatum) (u : (tensor A B).Carrier)
    (x : A.Carrier) (y : B.Carrier) :
    inner ℝ x (operator A B u y)=inner ℝ (pure A B x y) u := by
  refine Completion.induction_on u
    (isClosed_eq
      (continuous_const.inner (((operatorL A B).continuous.clm_apply continuous_const)))
      (continuous_const.inner continuous_id)) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    change inner ℝ x (operator A B (pure A B a b) y)=inner ℝ (pure A B x y) (pure A B a b)
    rw [operator_pure,real_inner_smul_right,inner_pure,real_inner_comm b y]
    ring
  | add t t' ht ht' =>
    simp only [Completion.coe_add,←operatorL_apply,map_add,ContinuousLinearMap.add_apply,
      inner_add_right] at *
    exact congrArg₂ (·+·) ht ht'

/-- The actual operator embedding loses no Hilbert-tensor information. -/
theorem operator_injective (A B : HilbertDatum) : Function.Injective (operator A B) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply (norm_eq_zero.mp)
  have hp (x : A.Carrier) (y : B.Carrier) : inner ℝ (pure A B x y) (u-v)=0 := by
    rw [inner_sub_right,←operator_pairing,←operator_pairing,huv,sub_self]
  have hall (w : (tensor A B).Carrier) : inner ℝ w (u-v)=0 := by
    refine Completion.induction_on w (isClosed_eq (continuous_id.inner continuous_const) continuous_const) ?_
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => exact hp x y
    | add t t' ht ht' => simp only [Completion.coe_add,inner_add_left,ht,ht',add_zero]
  have hself := hall (u-v)
  rw [real_inner_self_eq_norm_sq] at hself
  nlinarith [norm_nonneg (u-v)]

/-- Completed finite-rank operators with their actual Hilbert--Schmidt norm.
The faithful operator embedding above gives the concrete operator interpretation. -/
@[expose] abbrev HilbertSchmidt (A B : HilbertDatum) := (tensor A B).Carrier

@[expose] def rankOne (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) : HilbertSchmidt A B := pure A B x y

@[simp] theorem rankOne_inner (A B : HilbertDatum) (x x' : A.Carrier) (y y' : B.Carrier) :
    inner ℝ (rankOne A B x y) (rankOne A B x' y')=inner ℝ x x'*inner ℝ y y' := inner_pure _ _ _ _ _ _

@[simp] theorem rankOne_operator (A B : HilbertDatum) (x : A.Carrier) (y z : B.Carrier) :
    operator A B (rankOne A B x y) z=inner ℝ y z • x := operator_pure _ _ _ _ _

theorem operator_norm_le (A B : HilbertDatum) (u : HilbertSchmidt A B) : ‖operator A B u‖ ≤ ‖u‖ := by
  apply (operator A B u).opNorm_le_bound (norm_nonneg _)
  intro z
  change ‖contractLeft B A z (swap A B u)‖ ≤ ‖u‖*‖z‖
  have hh := contractLeft_norm_le B A z (swap A B u)
  rw [LinearIsometryEquiv.norm_map,mul_comm] at hh
  exact hh

end SphericalAging.HilbertSchmidtTensor
