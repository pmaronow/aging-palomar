module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

public section

/-! Canonical Hilbert tensor representation by literal L² product functions.
The pure product and its isometry are derived from Fubini, not assumed. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace TensorProduct
namespace SphericalAging.HilbertL2ExternalProduct
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
set_option maxHeartbeats 500000

/-- A pure product of two genuine L² classes is square integrable on the product law. -/
theorem product_memLp (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    MemLp (fun z : α×β=>f z.1*g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq
    ((Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd)).mpr
  change Integrable (fun z : α×β=>(f z.1*g z.2)^2) (μ.prod ν)
  simpa only [mul_pow] using (Lp.memLp f).integrable_sq.mul_prod (Lp.memLp g).integrable_sq

@[expose] def product (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (product_memLp μ ν f g).toLp (fun z : α×β=>f z.1*g z.2)

theorem product_coe (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    product μ ν f g=ᵐ[μ.prod ν] (fun z : α×β=>f z.1*g z.2) :=
  (product_memLp μ ν f g).coeFn_toLp

theorem product_add_left (f f' : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    product μ ν (f+f') g=product μ ν f g+product μ ν f' g := by
  apply Lp.ext
  filter_upwards [product_coe μ ν (f+f') g,product_coe μ ν f g,product_coe μ ν f' g,
    Lp.coeFn_add (product μ ν f g) (product μ ν f' g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add f f')] with z ha hb hc hd he
  rw [ha,hd]
  simp only [Pi.add_apply] at he ⊢
  rw [hb,hc,he]
  change (f z.1+f' z.1)*g z.2=f z.1*g z.2+f' z.1*g z.2
  ring

theorem product_add_right (f : Lp ℝ 2 μ) (g g' : Lp ℝ 2 ν) :
    product μ ν f (g+g')=product μ ν f g+product μ ν f g' := by
  apply Lp.ext
  filter_upwards [product_coe μ ν f (g+g'),product_coe μ ν f g,product_coe μ ν f g',
    Lp.coeFn_add (product μ ν f g) (product μ ν f g'),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add g g')] with z ha hb hc hd he
  rw [ha,hd]
  simp only [Pi.add_apply] at he ⊢
  rw [hb,hc,he]
  change f z.1*(g z.2+g' z.2)=f z.1*g z.2+f z.1*g' z.2
  ring

theorem product_smul_left (a : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    product μ ν (a • f) g=a • product μ ν f g := by
  apply Lp.ext
  filter_upwards [product_coe μ ν (a • f) g,product_coe μ ν f g,
    Lp.coeFn_smul a (product μ ν f g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul a f)] with z ha hb hc hd
  rw [ha,hc]
  simp only [Pi.smul_apply,smul_eq_mul] at hd ⊢
  rw [hb,hd]
  change (a*f z.1)*g z.2=a*(f z.1*g z.2)
  ring

theorem product_smul_right (a : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    product μ ν f (a • g)=a • product μ ν f g := by
  apply Lp.ext
  filter_upwards [product_coe μ ν f (a • g),product_coe μ ν f g,
    Lp.coeFn_smul a (product μ ν f g),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul a g)] with z ha hb hc hd
  rw [ha,hc]
  simp only [Pi.smul_apply,smul_eq_mul] at hd ⊢
  rw [hb,hd]
  change f z.1*(a*g z.2)=a*(f z.1*g z.2)
  ring

/-- The literal pure-function product, as a bilinear map on L² classes. -/
@[expose] def productLinear : Lp ℝ 2 μ→ₗ[ℝ] Lp ℝ 2 ν→ₗ[ℝ] Lp ℝ 2 (μ.prod ν) where
  toFun f :=
    { toFun := product μ ν f
      map_add' := product_add_right μ ν f
      map_smul' := fun a g=>product_smul_right μ ν a f g }
  map_add' f f' := by apply LinearMap.ext;intro g;exact product_add_left μ ν f f' g
  map_smul' a f := by apply LinearMap.ext;intro g;exact product_smul_left μ ν a f g

/-- The product-function representation on the algebraic Hilbert tensor product. -/
@[expose] def tensorLinear : (Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν)→ₗ[ℝ]Lp ℝ 2 (μ.prod ν) :=
  TensorProduct.lift (productLinear μ ν)

@[simp] theorem tensorLinear_tmul (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    tensorLinear μ ν (f⊗ₜ[ℝ]g)=product μ ν f g := rfl

/-- Fubini gives exactly the Hilbert tensor pure-product inner product. -/
theorem product_inner (f f' : Lp ℝ 2 μ) (g g' : Lp ℝ 2 ν) :
    ⟪product μ ν f g,product μ ν f' g'⟫_ℝ=⟪f,f'⟫_ℝ*⟪g,g'⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def,L2.inner_def]
  calc
    _ = ∫z : α×β,(f z.1*f' z.1)*(g z.2*g' z.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [product_coe μ ν f g,product_coe μ ν f' g'] with z h1 h2
      rw [h1,h2]
      simp only [RCLike.inner_apply,conj_trivial]
      ring
    _ = _ := by simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using
      integral_prod_mul (μ:=μ) (ν:=ν) (fun x=>f x*f' x) (fun y=>g y*g' y)

/-- The representation preserves every algebraic tensor inner product. -/
theorem tensorLinear_inner (x y : Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν) :
    ⟪tensorLinear μ ν x,tensorLinear μ ν y⟫_ℝ=⟪x,y⟫_ℝ := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    induction y using TensorProduct.inductionOn with
    | tmul f' g' =>
      simp only [tensorLinear_tmul,TensorProduct.inner_tmul]
      exact product_inner μ ν f f' g g'
    | add y y' hy hy' => simp only [map_add,inner_add_right,hy,hy']
  | add x x' hx hx' => simp only [map_add,inner_add_left,hx,hx']

/-- The isometry can be extended to the Hilbert completion. -/
@[expose] def tensorIsometry : (Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν)→ₗᵢ[ℝ]Lp ℝ 2 (μ.prod ν) :=
  (tensorLinear μ ν).isometryOfInner (tensorLinear_inner μ ν)

open UniformSpace

/-- The actual continuous extension into the already complete L² product space. -/
@[expose] def completedTensor : Completion (Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν)→L[ℝ]Lp ℝ 2 (μ.prod ν) :=
  (tensorIsometry μ ν).toContinuousLinearMap.extend Completion.toComplL

@[simp] theorem completedTensor_coe (x : Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν) :
    completedTensor μ ν (x : Completion _)=tensorLinear μ ν x := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _) x

/-- Inner-product preservation survives Hilbert completion by continuity. -/
theorem completedTensor_inner (x y : Completion (Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν)) :
    ⟪completedTensor μ ν x,completedTensor μ ν y⟫_ℝ=⟪x,y⟫_ℝ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      (((completedTensor μ ν).continuous.comp continuous_fst).inner
        ((completedTensor μ ν).continuous.comp continuous_snd))
      (continuous_fst.inner continuous_snd)
  · intro x y
    rw [completedTensor_coe,completedTensor_coe,Completion.inner_coe]
    exact tensorLinear_inner μ ν x y

/-- Canonical isometric representation of completed Hilbert tensors by L² kernels. -/
@[expose] def completedTensorIsometry : Completion (Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν)→ₗᵢ[ℝ]Lp ℝ 2 (μ.prod ν) :=
  (completedTensor μ ν).toLinearMap.isometryOfInner (completedTensor_inner μ ν)

@[simp] theorem completedTensor_pure (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    completedTensor μ ν ((f⊗ₜ[ℝ]g : Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν) : Completion _)=product μ ν f g := by
  rw [completedTensor_coe,tensorLinear_tmul]

/-- Its pure tensor kernel is the literal pointwise product almost everywhere. -/
theorem completedTensor_pure_coe (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    completedTensor μ ν ((f⊗ₜ[ℝ]g : Lp ℝ 2 μ⊗[ℝ]Lp ℝ 2 ν) : Completion _)=ᵐ[μ.prod ν]
      (fun z : α×β=>f z.1*g z.2) := by
  rw [completedTensor_pure]
  exact product_coe μ ν f g

end SphericalAging.HilbertL2ExternalProduct
