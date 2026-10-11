module

public import SphericalAging.TensorResidualRotation
public import SphericalAging.PredictableGramStep
public import SphericalAging.AdaptiveGaussianDisclosureStep

public section

/-! A fresh ordered tensor disclosure using an actual past-selected
Householder update restricted to the literal undisclosed tensor space.
No orthogonal-update or measurable-frame receipt is an input. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PredictableTensorDisclosureStep
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open PredictableGramStep TensorOrthogonalAction TensorResidualRotation
open scoped InnerProductSpace Topology

 theorem frameUpdate_rotatedSpace {N : ℕ} (W : Submodule ℝ (Vector N))
    {e : Vector N} (he : e∈Wᗮ) (x : Vector N) :
    rotatedSpace (frameUpdate W e x) W=W := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hz
    change frameUpdate W e x y∈W
    rw [frameUpdate_fixes W he hy]
    exact hy
  · intro z hz
    exact Submodule.mem_map.mpr ⟨z,hz,frameUpdate_fixes W he hz⟩

 theorem frameUpdate_tensorSpace {N p : ℕ} (W : Submodule ℝ (Vector N))
    {e : Vector N} (he : e∈Wᗮ) (x : Vector N) :
    (residualTensorSpace (p:=p) W).map (action (frameUpdate W e x)).toLinearEquiv.toLinearMap=
      residualTensorSpace W := by
  rw [residualTensorSpace_rotated,frameUpdate_rotatedSpace W he]

@[expose]  def tensorUpdate {N p : ℕ} (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) (x : Vector N) :
    residualTensorSpace (p:=p) W≃ₗᵢ[ℝ]residualTensorSpace (p:=p) W :=
  (LinearIsometryEquiv.submoduleMap (residualTensorSpace W) (action (frameUpdate W e x))).trans
    (LinearIsometryEquiv.ofEq _ _ (frameUpdate_tensorSpace W he x))

 theorem tensorUpdate_coe {N p : ℕ} (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) (x : Vector N) (J : residualTensorSpace (p:=p) W) :
    (tensorUpdate W e he x J:TensorSpace N p)=action (frameUpdate W e x) J := rfl

 theorem tensorUpdate_measurable {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    {x : S→Vector N} (hx : Measurable x) :
    Measurable (fun z : S×residualTensorSpace (p:=p) W => tensorUpdate W e he (x z.1) z.2) := by
  have hu : Measurable (fun z : S×Vector N => frameUpdate W e (x z.1) z.2) :=
    frameUpdate_measurable W measurable_const (hx.comp measurable_fst) measurable_snd
  have ha := (action_measurable (p:=p) (fun s => frameUpdate W e (x s)) hu).comp
    (measurable_fst.prodMk ((residualTensorSpace W).subtypeL.measurable.comp measurable_snd))
  have hh : Measurable (fun z : S×residualTensorSpace (p:=p) W =>
      (tensorUpdate W e he (x z.1) z.2:TensorSpace N p)) := ha
  exact hh.subtype_mk

@[expose]  def newResidualSubspace {N p : ℕ} (W : Submodule ℝ (Vector N)) (e : Vector N) :
    Submodule ℝ (residualTensorSpace (p:=p) W) :=
  (residualTensorSpace (p:=p) (W⊔ℝ ∙ e)).comap (residualTensorSpace W).subtype

@[expose]  def freshBlock {N p : ℕ} (W : Submodule ℝ (Vector N)) (e : Vector N) :
    Submodule ℝ (residualTensorSpace (p:=p) W) := (newResidualSubspace W e)ᗮ

@[expose]  def history {N p : ℕ} {S : Type*} (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    (x : S→Vector N) : S×residualTensorSpace (p:=p) W→S×freshBlock (p:=p) W e :=
  AdaptiveGaussianDisclosureStep.history (freshBlock W e) (fun s => tensorUpdate W e he (x s))

@[expose]  def remainder {N p : ℕ} {S : Type*} (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    (x : S→Vector N) : S×residualTensorSpace (p:=p) W→(freshBlock (p:=p) W e)ᗮ :=
  AdaptiveGaussianDisclosureStep.residual (freshBlock W e) (fun s => tensorUpdate W e he (x s))

 theorem fresh_tensor_step_preserves_product {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    {x : S→Vector N} (hx : Measurable x) :
    MeasurePreserving (fun z => (history W e he x z,remainder W e he x z))
      (μ.prod (stdGaussian (residualTensorSpace (p:=p) W)))
      ((μ.prod (stdGaussian (freshBlock (p:=p) W e))).prod (stdGaussian (freshBlock (p:=p) W e)ᗮ)) :=
  AdaptiveGaussianDisclosureStep.step_preserves_product μ (freshBlock W e)
    (fun s => tensorUpdate W e he (x s)) (tensorUpdate_measurable W e he hx)

 theorem remainder_hasLaw {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    {x : S→Vector N} (hx : Measurable x) :
    HasLaw (remainder (p:=p) W e he x) (stdGaussian (freshBlock (p:=p) W e)ᗮ)
      (μ.prod (stdGaussian (residualTensorSpace (p:=p) W))) :=
  AdaptiveGaussianDisclosureStep.residual_hasLaw μ (freshBlock W e)
    (fun s => tensorUpdate W e he (x s)) (tensorUpdate_measurable W e he hx)

 theorem remainder_independent_of_history {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    {x : S→Vector N} (hx : Measurable x) :
    IndepFun (history (p:=p) W e he x) (remainder (p:=p) W e he x)
      (μ.prod (stdGaussian (residualTensorSpace (p:=p) W))) :=
  AdaptiveGaussianDisclosureStep.residual_independent_of_history μ (freshBlock W e)
    (fun s => tensorUpdate W e he (x s)) (tensorUpdate_measurable W e he hx)

 theorem conditional_remainder_gaussian {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    {x : S→Vector N} (hx : Measurable x) (f : (freshBlock (p:=p) W e)ᗮ→ℝ) (hf : StronglyMeasurable f) :
    (μ.prod (stdGaussian (residualTensorSpace (p:=p) W)))[f∘remainder W e he x | MeasurableSpace.comap (history W e he x) inferInstance]=ᵐ[μ.prod (stdGaussian (residualTensorSpace (p:=p) W))]
          fun _ => ∫J,f J ∂stdGaussian (freshBlock (p:=p) W e)ᗮ :=
  AdaptiveGaussianDisclosureStep.conditional_residual_standardGaussian μ (freshBlock W e)
    (fun s => tensorUpdate W e he (x s)) (tensorUpdate_measurable W e he hx) f hf

end SphericalAging.PredictableTensorDisclosureStep
