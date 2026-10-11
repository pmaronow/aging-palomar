module

public import SphericalAging.ExampleFirstHeights
public import SphericalAging.HilbertL2ExternalProduct

public section

/-! The actual two-noise projection of the first cubic tree tensor into
literal L² of the product noise-label measure. -/
noncomputable section
open MeasureTheory UniformSpace Set
open scoped TensorProduct InnerProductSpace ENNReal
namespace SphericalAging.ExampleFirstForkNoiseProjection
open CausalTree CKSpecification CausalTreeRealization ExampleFirstHeights HilbertL2ExternalProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

@[expose] abbrev noiseMeasure : Measure ℝ := volume.restrict (Ioi (0:ℝ))

/-- Forget the initial-direction coordinate of a genuine Brownian leaf. -/
@[expose] def leafNoise : LeafSpace→L[ℝ]NoiseSpace :=
  (ContinuousLinearMap.snd ℝ ℝ NoiseSpace).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ NoiseSpace).toContinuousLinearMap

@[simp] theorem leafNoise_apply (x : LeafSpace) : leafNoise x=x.snd := rfl

/-- Remove the harmless terminal unit factor of the recursively completed binary tensor. -/
@[expose] def removeUnit : (fiber firstFork).Carrier ≃ₗᵢ[ℝ] Completion (LeafSpace⊗[ℝ]LeafSpace) :=
  HilbertDatum.tensorCongr leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real)
    leafDatum leafDatum (LinearIsometryEquiv.refl ℝ LeafSpace) (HilbertDatum.tensorRid leafDatum)

@[expose] def noiseTensorMap : Completion (LeafSpace⊗[ℝ]LeafSpace)→L[ℝ]
    Completion (NoiseSpace⊗[ℝ]NoiseSpace) :=
  (Completion.toComplL.comp (TensorProduct.mapL leafNoise leafNoise)).extend Completion.toComplL

/-- Canonical literal two-noise kernel of the actual completed first-fork tensor. -/
@[expose] def noiseProjection : (fiber firstFork).Carrier→L[ℝ]Lp ℝ 2 (noiseMeasure.prod noiseMeasure) :=
  (completedTensor noiseMeasure noiseMeasure).comp
    (noiseTensorMap.comp removeUnit.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem removeUnit_pairPure (x y : LeafSpace) :
    removeUnit (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y)=
      ((x⊗ₜ[ℝ]y : LeafSpace⊗[ℝ]LeafSpace) : Completion _) := by
  change HilbertDatum.tensorCongr leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real)
    leafDatum leafDatum (LinearIsometryEquiv.refl ℝ LeafSpace) (HilbertDatum.tensorRid leafDatum)
      (HilbertDatum.pure leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real) x
        (HilbertDatum.pure leafDatum HilbertDatum.real y 1))=_
  rw [HilbertDatum.tensorCongr_pure,HilbertDatum.tensorRid_pure,one_smul]
  rfl

@[simp] theorem noiseTensorMap_pure (x y : LeafSpace) :
    noiseTensorMap ((x⊗ₜ[ℝ]y : LeafSpace⊗[ℝ]LeafSpace) : Completion _)=
      ((x.snd⊗ₜ[ℝ]y.snd : NoiseSpace⊗[ℝ]NoiseSpace) : Completion _) := by
  have he := ContinuousLinearMap.extend_eq (e:=Completion.toComplL)
    (Completion.toComplL.comp (TensorProduct.mapL leafNoise leafNoise))
    Completion.denseRange_coe (Completion.isUniformInducing_coe _) (x⊗ₜ[ℝ]y)
  change noiseTensorMap ((x⊗ₜ[ℝ]y : LeafSpace⊗[ℝ]LeafSpace) : Completion _)=_ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,TensorProduct.mapL_tmul,leafNoise_apply]
  rfl

/-- Genuine completed tensor projection agrees with the literal product of leaf noise coefficients. -/
theorem noiseProjection_pairPure (x y : LeafSpace) :
    noiseProjection (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y)=
      product noiseMeasure noiseMeasure x.snd y.snd := by
  change completedTensor noiseMeasure noiseMeasure
    (noiseTensorMap (removeUnit (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y)))=_
  rw [removeUnit_pairPure,noiseTensorMap_pure,completedTensor_pure]

/-- The projected pure tensor has the literal pointwise product almost everywhere. -/
theorem noiseProjection_pairPure_coe (x y : LeafSpace) :
    noiseProjection (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y)=ᵐ[noiseMeasure.prod noiseMeasure]
      (fun z : ℝ×ℝ=>x.snd z.1*y.snd z.2) := by
  rw [noiseProjection_pairPure]
  exact product_coe noiseMeasure noiseMeasure x.snd y.snd

end SphericalAging.ExampleFirstForkNoiseProjection
