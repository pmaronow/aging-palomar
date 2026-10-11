module

public import SphericalAging.FiniteDisclosureConditional
public import SphericalAging.FiniteDisclosureMeasurableState
public import SphericalAging.FiniteDisclosureGaussianProjection

public section

/-! The complete finite history starts from actual independent seed and
ambient Gaussian disorder. Neither an initial Gaussian regeneration law
nor a random frame is assumed. -/
noncomputable section
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureAmbient
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan TensorBoundarySpaces TensorOrthogonalAction TensorActionComposition
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureMeasurableState FiniteDisclosureConditional FiniteDisclosureGaussianProjection

@[expose] def initialIso (N p : ℕ) : TensorSpace N p≃ₗᵢ[ℝ]Residual N p 0 := by
  have h : (Residual N p 0 : Submodule ℝ (TensorSpace N p))=⊤ := by
    change residualTensorSpace (p:=p) (space N 0)=⊤
    rw [space_zero,residualTensorSpace_bot]
  exact (LinearIsometryEquiv.ofTop (TensorSpace N p) (Residual N p 0) h).symm

theorem initialIso_coe (N p : ℕ) (J : TensorSpace N p) : (initialIso N p J).val=J := rfl

@[expose] def initialState {N p : ℕ} {S : Type} (z : S×TensorSpace N p) : S×Residual N p 0 :=
  (z.1,initialIso N p z.2)

@[expose] def initialFrame (N : ℕ) (S : Type) : S→Frame N := fun _ => LinearIsometryEquiv.refl ℝ (Vector N)

@[expose] def actualHistory {N p n : ℕ} {S : Type} [MeasurableSpace S] (P : Plan N p n 0 S) :
    S×TensorSpace N p→Past N p n 0 S :=
  past N p n 0 S∘execute N p n 0 S P∘initialState

@[expose] def actualSpace {N p n : ℕ} {S : Type} [MeasurableSpace S] (P : Plan N p n 0 S)
    (z : S×TensorSpace N p) : Submodule ℝ (Vector N) :=
  physicalSpace N p n 0 S P (initialFrame N S) (actualHistory P z)

theorem initialState_law {N p : ℕ} {S : Type} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] :
    MeasurePreserving (initialState (N:=N) (p:=p)) (μ.prod (stdGaussian (TensorSpace N p)))
      (μ.prod (stdGaussian (Residual N p 0))) := by
  have hi : MeasurePreserving (initialIso N p) (stdGaussian (TensorSpace N p))
      (stdGaussian (Residual N p 0)) := ⟨(initialIso N p).continuous.measurable,stdGaussian_map (initialIso N p)⟩
  exact (MeasurePreserving.id μ).prod hi

theorem actual_original_projection {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (z : S×TensorSpace N p) :
    physicalResidual N p n 0 S P (initialFrame N S) (execute N p n 0 S P (initialState z))=
      (residualTensorSpace (actualSpace P z)).starProjection z.2 := by
  have hh := actual_original_disorder_projection N p n 0 S P (initialFrame N S) (fun _ => 0)
    (fun _ => Submodule.zero_mem _) (initialState z)
  simpa only [actualSpace,actualHistory,Function.comp_def,initialState,initialFrame,zero_add,
    initialIso_coe,action_refl] using hh

theorem actual_projected_conditional_gaussian {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (μ : Measure S) [IsFiniteMeasure μ]
    (φ : TensorSpace N p→ℝ) (hφ : StronglyMeasurable φ) (C : ℝ) (hC : ∀J,‖φ J‖≤C) :
    (μ.prod (stdGaussian (TensorSpace N p)))[(fun z => φ ((residualTensorSpace (actualSpace P z)).starProjection z.2)) |
      MeasurableSpace.comap (actualHistory P) inferInstance]=ᵐ[μ.prod (stdGaussian (TensorSpace N p))]
      fun z => ∫J,φ ((residualTensorSpace (actualSpace P z)).starProjection J) ∂stdGaussian (TensorSpace N p) := by
  let F := initialFrame N S
  let f := φ∘physicalResidual N p n 0 S P F
  have hF : Measurable (fun z : S×Vector N => F z.1 z.2) := measurable_snd
  have hfm : StronglyMeasurable f := hφ.comp_measurable (physicalResidual_measurable N p n 0 S P F hF)
  have hfc : ∀z,‖f z‖≤C := fun z => hC _
  have hc := actual_finite_conditional_gaussian_integral N p n 0 S P μ hfm C hfc
  have hp := actual_finite_tree_law N p n 0 S P μ
  let q := past N p n 0 S∘execute N p n 0 S P
  let g := FiniteDisclosurePast.average N p n 0 S f
  have hq : Measurable q := (past_measurable N p n 0 S).comp hp.measurable
  have hgm : StronglyMeasurable g := average_stronglyMeasurable N p n 0 S hfm
  have hgi : Integrable (g∘q) (μ.prod (stdGaussian (Residual N p 0))) :=
    Integrable.of_bound (hgm.comp_measurable hq).aestronglyMeasurable C
      (ae_of_all _ (fun z => average_norm_le N p n 0 S f C hfc (q z)))
  have hfi : Integrable (f∘execute N p n 0 S P) (μ.prod (stdGaussian (Residual N p 0))) :=
    Integrable.of_bound (hfm.comp_measurable hp.measurable).aestronglyMeasurable C
      (ae_of_all _ (fun z => hfc _))
  have hh := FiniteConditionalLawPullback.conditional_expectation_pullback _ _ initialState
    (initialState_law μ) q hq (hfm.comp_measurable hp.measurable) hfi hgm hgi hc
  have hfun : (f∘execute N p n 0 S P)∘initialState=(fun z : S×TensorSpace N p =>
      φ ((residualTensorSpace (actualSpace P z)).starProjection z.2)) := by
    funext z
    exact congrArg φ (actual_original_projection P z)
  rw [hfun] at hh
  refine hh.trans (ae_of_all _ (fun z => ?_))
  exact actual_average_projected_gaussian N p n 0 S P F φ hφ (actualHistory P z)

end SphericalAging.FiniteDisclosureAmbient
