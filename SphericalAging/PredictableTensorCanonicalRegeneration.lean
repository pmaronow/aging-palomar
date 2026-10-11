module

public import SphericalAging.PredictableTensorProjectionIdentification

public section

/-! The genuine Householder tensor update leaves a canonical Gaussian
on the next literal tensor space. This holds under finite restricted past
laws and is usable on every rank branch of an adaptive history. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PredictableTensorCanonicalRegeneration
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open PredictableTensorDisclosureStep PredictableTensorProjectionIdentification

@[expose] def canonicalInclusion {N p : ℕ} (W : Submodule ℝ (Vector N)) (e : Vector N) :
    (freshBlock (p:=p) W e)ᗮ→ₗᵢ[ℝ]TensorSpace N p :=
  (residualTensorSpace W).subtypeₗᵢ.comp (freshBlock W e)ᗮ.subtypeₗᵢ

theorem canonicalInclusion_range {N p : ℕ} (W : Submodule ℝ (Vector N)) (e : Vector N) :
    LinearMap.range (canonicalInclusion (p:=p) W e).toLinearMap=
      residualTensorSpace (p:=p) (W⊔ℝ ∙ e) := by
  change LinearMap.range ((residualTensorSpace W).subtype.comp (freshBlock W e)ᗮ.subtype)=_
  rw [LinearMap.range_comp,Submodule.range_subtype]
  simpa only [freshBlock,Submodule.orthogonal_orthogonal] using
    newResidualSubspace_map_subtype (p:=p) W e

@[expose] def remainingIso {N p : ℕ} (W : Submodule ℝ (Vector N)) (e : Vector N) :
    (freshBlock (p:=p) W e)ᗮ≃ₗᵢ[ℝ]residualTensorSpace (p:=p) (W⊔ℝ ∙ e) :=
  (canonicalInclusion (p:=p) W e).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (canonicalInclusion_range (p:=p) W e))

theorem remainingIso_coe {N p : ℕ} (W : Submodule ℝ (Vector N)) (e : Vector N)
    (r : (freshBlock (p:=p) W e)ᗮ) : (remainingIso (p:=p) W e r).val=r.val.val := rfl

@[expose] def canonicalRemaining {N p : ℕ} {S : Type*} (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) (x : S→Vector N)
    (z : S×residualTensorSpace (p:=p) W) : residualTensorSpace (p:=p) (W⊔ℝ ∙ e) :=
  remainingIso (p:=p) W e (remainder (p:=p) W e he x z)

theorem canonical_step_preserves_product {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    {x : S→Vector N} (hx : Measurable x) :
    MeasurePreserving (fun z => (history (p:=p) W e he x z,canonicalRemaining (p:=p) W e he x z))
      (μ.prod (stdGaussian (residualTensorSpace (p:=p) W)))
      ((μ.prod (stdGaussian (freshBlock (p:=p) W e))).prod
        (stdGaussian (residualTensorSpace (p:=p) (W⊔ℝ ∙ e)))) := by
  have hi : MeasurePreserving (remainingIso (p:=p) W e)
      (stdGaussian (freshBlock (p:=p) W e)ᗮ)
      (stdGaussian (residualTensorSpace (p:=p) (W⊔ℝ ∙ e))) :=
    ⟨(remainingIso (p:=p) W e).continuous.measurable,stdGaussian_map (remainingIso (p:=p) W e)⟩
  have hp := (MeasurePreserving.id (μ.prod (stdGaussian (freshBlock (p:=p) W e)))).prod hi
  exact hp.comp (fresh_tensor_step_preserves_product (p:=p) μ W e he hx)

theorem canonical_remaining_independent {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) {x : S→Vector N} (hx : Measurable x) :
    IndepFun (history (p:=p) W e he x) (canonicalRemaining (p:=p) W e he x)
      (μ.prod (stdGaussian (residualTensorSpace (p:=p) W))) := by
  exact (remainder_independent_of_history (p:=p) μ W e he hx).comp measurable_id
    (remainingIso (p:=p) W e).continuous.measurable

end SphericalAging.PredictableTensorCanonicalRegeneration
