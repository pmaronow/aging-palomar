module

public import SphericalAging.CausalTreePositivity
public import SphericalAging.LpTensorSurjectivity

public section

/-! Exact complete L² identification of every ordered tree leaf fiber. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ENNReal TensorProduct Topology
open Set MeasureTheory Filter UniformSpace
namespace SphericalAging.CausalTreeLabelEquivalence
open CausalTree CausalTreePositivity

/-- The empty ordered tensor is exactly L² of its unit empty tuple. -/
theorem unitLabelIsometry_surjective : Function.Surjective unitLabelIsometry := by
  intro f
  refine ⟨f (), ?_⟩
  apply Lp.ext
  filter_upwards [unitLabelVector_coe (f ())] with u hu
  cases u
  exact hu

@[expose] def unitLabelEquiv : ℝ ≃ₗᵢ[ℝ] Lp ℝ 2 (Measure.dirac ()) :=
  LinearIsometryEquiv.ofSurjective unitLabelIsometry unitLabelIsometry_surjective

/-- The canonical complete product-label equivalence, for arbitrary complete factors. -/
@[expose] def tensorLabelEquiv (A B : HilbertDatum) (D E : LabelDatum)
    (f : A.Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 D.measure) (g : B.Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 E.measure) :
    (HilbertDatum.tensor A B).Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 (D.measure.prod E.measure) :=
  (HilbertDatum.tensorCongr A B D.hilbert E.hilbert f g).trans LpTensorSurjectivity.completedEquiv

@[simp] theorem tensorLabelEquiv_pure (A B : HilbertDatum) (D E : LabelDatum)
    (f : A.Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 D.measure) (g : B.Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 E.measure)
    (x : A.Carrier) (y : B.Carrier) :
    tensorLabelEquiv A B D E f g (HilbertDatum.pure A B x y) = LpProductTensor.product (f x) (g y) := by
  change LpTensorSurjectivity.completedEquiv
    (HilbertDatum.tensorCongr A B D.hilbert E.hilbert f g (HilbertDatum.pure A B x y)) = _
  rw [HilbertDatum.tensorCongr_pure]
  exact LpProductTensor.completedIsometry_tmul (f x) (g y)

/-- The complete equivalence is the same concrete function embedding used for positivity. -/
theorem tensorLabelEquiv_apply (A B : HilbertDatum) (D E : LabelDatum)
    (f : A.Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 D.measure) (g : B.Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 E.measure)
    (z : (HilbertDatum.tensor A B).Carrier) :
    tensorLabelEquiv A B D E f g z = tensorLabelIsometry A B D E f.toLinearIsometry g.toLinearIsometry z := by
  have he : (tensorLabelEquiv A B D E f g).toContinuousLinearEquiv.toContinuousLinearMap =
      (tensorLabelIsometry A B D E f.toLinearIsometry g.toLinearIsometry).toContinuousLinearMap := by
    apply HilbertDatum.tensor_ext A B (productLabels D E).hilbert
    intro x y
    change tensorLabelEquiv A B D E f g (HilbertDatum.pure A B x y) =
      tensorLabelIsometry A B D E f.toLinearIsometry g.toLinearIsometry (HilbertDatum.pure A B x y)
    rw [tensorLabelEquiv_pure, tensorLabelIsometry_pure]
    rfl
  exact DFunLike.congr_fun he z

/-- An actual ordered finite Hilbert tensor equals L² of its actual ordered label product. -/
@[expose] def finiteLabelEquiv : (n : ℕ) → (A : Fin n → HilbertDatum) → (D : Fin n → LabelDatum) →
    (∀ i, (A i).Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 (D i).measure) →
      (HilbertDatum.finiteTensor n A).Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 (finiteLabels n D).measure
  | 0, _, _, _ => unitLabelEquiv
  | n + 1, A, D, f => tensorLabelEquiv (A 0) (HilbertDatum.finiteTensor n (fun i => A i.succ))
      (D 0) (finiteLabels n (fun i => D i.succ)) (f 0)
      (finiteLabelEquiv n (fun i => A i.succ) (fun i => D i.succ) (fun i => f i.succ))

theorem finiteLabelEquiv_apply (n : ℕ) (A : Fin n → HilbertDatum) (D : Fin n → LabelDatum)
    (f : ∀ i, (A i).Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 (D i).measure)
    (z : (HilbertDatum.finiteTensor n A).Carrier) :
    finiteLabelEquiv n A D f z = finiteLabelIsometry n A D (fun i => (f i).toLinearIsometry) z := by
  have he : (finiteLabelEquiv n A D f).toContinuousLinearEquiv.toContinuousLinearMap =
      (finiteLabelIsometry n A D (fun i => (f i).toLinearIsometry)).toContinuousLinearMap := by
    apply HilbertDatum.finiteTensor_ext n A (finiteLabels n D).hilbert
    intro x
    induction n with
    | zero => rfl
    | succ n ih =>
      change tensorLabelEquiv (A 0) (HilbertDatum.finiteTensor n (fun i => A i.succ))
        (D 0) (finiteLabels n (fun i => D i.succ)) (f 0)
        (finiteLabelEquiv n (fun i => A i.succ) (fun i => D i.succ) (fun i => f i.succ))
          (HilbertDatum.pure _ _ (x 0) (HilbertDatum.finitePure n (fun i => A i.succ) (fun i => x i.succ))) =
        tensorLabelIsometry (A 0) (HilbertDatum.finiteTensor n (fun i => A i.succ))
        (D 0) (finiteLabels n (fun i => D i.succ)) (f 0).toLinearIsometry
        (finiteLabelIsometry n (fun i => A i.succ) (fun i => D i.succ) (fun i => (f i.succ).toLinearIsometry))
          (HilbertDatum.pure _ _ (x 0) (HilbertDatum.finitePure n (fun i => A i.succ) (fun i => x i.succ)))
      rw [tensorLabelEquiv_pure, tensorLabelIsometry_pure]
      exact congrArg (LpProductTensor.product (f 0 (x 0)))
        (ih (fun i => A i.succ) (fun i => D i.succ) (fun i => f i.succ) 0 (fun i => x i.succ))
  exact DFunLike.congr_fun he z

/-- Every actual ordered tree fiber equals the complete product-label L² space. -/
@[expose] def fiberLabelHilbertEquiv {m : ℕ} (τ : CausalTree.Tree m) :
    (fiber τ).Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 (fiberLabels τ).measure := by
  induction τ with
  | leaf => exact leafLabelEquiv
  | graft ts children => exact finiteLabelEquiv m (fun i => fiber (ts i)) (fun i => fiberLabels (ts i)) children

theorem fiberLabelHilbertEquiv_apply {m : ℕ} (τ : CausalTree.Tree m) (x : (fiber τ).Carrier) :
    fiberLabelHilbertEquiv τ x = fiberLabelIsometry τ x := by
  induction τ with
  | leaf => rfl
  | graft ts children =>
    rw [show fiberLabelHilbertEquiv (CausalTree.Tree.graft ts) =
      finiteLabelEquiv m (fun i => fiber (ts i)) (fun i => fiberLabels (ts i))
        (fun i => fiberLabelHilbertEquiv (ts i)) from rfl, finiteLabelEquiv_apply]
    have he : (fun i => (fiberLabelHilbertEquiv (ts i)).toLinearIsometry) =
        (fun i => fiberLabelIsometry (ts i)) := by
      funext i
      apply LinearIsometry.ext
      intro y
      exact children i y
    rw [he]
    rfl

/-- Relabeling by a measure-preserving equivalence gives an actual onto L² isometry. -/
@[expose] def relabelEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ e.symm he.symm) (by
    intro f
    refine ⟨Lp.compMeasurePreserving e he f, ?_⟩
    change Lp.compMeasurePreserving e.symm he.symm (Lp.compMeasurePreserving e he f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [e.self_comp_symm] using Lp.compMeasurePreserving_id_apply f)

/-- Exact source `E^⊗|τ| = L²(LeafLabel^|τ|)`, with its specified ordered leaves. -/
@[expose] def orderedLeafLabelEquiv {m : ℕ} (τ : CausalTree.Tree m) :
    (fiber τ).Carrier ≃ₗᵢ[ℝ] Lp ℝ 2 (tupleLabels τ.leafCount).measure :=
  (fiberLabelHilbertEquiv τ).trans (relabelEquiv (fiberLabelEquiv τ) (fiberLabelEquiv_measurePreserving τ))

theorem orderedLeafLabelEquiv_apply {m : ℕ} (τ : CausalTree.Tree m) (x : (fiber τ).Carrier) :
    orderedLeafLabelEquiv τ x = orderedLeafLabelIsometry τ x := by
  change (Lp.compMeasurePreservingₗᵢ ℝ (fiberLabelEquiv τ).symm (fiberLabelEquiv_measurePreserving τ).symm)
      (fiberLabelHilbertEquiv τ x) =
    (Lp.compMeasurePreservingₗᵢ ℝ (fiberLabelEquiv τ).symm (fiberLabelEquiv_measurePreserving τ).symm)
      (fiberLabelIsometry τ x)
  rw [fiberLabelHilbertEquiv_apply]


/-- The literal direct sum of the complete ordered leaf-label L² fibers. -/
@[expose] abbrev LabelTreeSpace (m : ℕ) :=
  lp (fun τ : CausalTree.Tree m => Lp ℝ 2 (tupleLabels τ.leafCount).measure) 2

/-- The tree space is exactly the direct sum of actual L² functions of its ordered leaf labels. -/
@[expose] def treeLeafFunctionEquiv (m : ℕ) : CausalTree.Space m ≃ₗᵢ[ℝ] LabelTreeSpace m :=
  lpFiberCongr (fun τ : CausalTree.Tree m => fiber τ) (fun τ => (tupleLabels τ.leafCount).hilbert)
    orderedLeafLabelEquiv

@[simp] theorem treeLeafFunctionEquiv_apply (m : ℕ) (v : CausalTree.Space m) (τ : CausalTree.Tree m) :
    treeLeafFunctionEquiv m v τ = orderedLeafLabelIsometry τ (v τ) :=
  orderedLeafLabelEquiv_apply τ (v τ)

end SphericalAging.CausalTreeLabelEquivalence
