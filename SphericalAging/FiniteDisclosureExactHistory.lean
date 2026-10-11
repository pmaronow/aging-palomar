module

public import SphericalAging.FiniteDisclosureReplay
public import SphericalAging.FiniteDisclosureDisclosed
public import SphericalAging.FiniteDisclosureSeedHistory

public section

/-! The constructed canonical history generates precisely the sigma
algebra of the original seed and literal disclosed original disorder.
The inverse is actual replay with the final residual removed. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureExactHistory
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open TensorOrthogonalAction TensorActionComposition
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureAmbient FiniteDisclosureDisclosed FiniteDisclosureSeedHistory FiniteDisclosureReplay

 theorem actualHistory_measurable {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) : Measurable (actualHistory P) := by
  have hp := FiniteDisclosureIntegral.actual_finite_past_law N p n 0 S P (0 : Measure S)
  have hh := hp.comp (initialState_law (N:=N) (p:=p) (0 : Measure S))
  exact hh.measurable

 theorem actual_history_replay_disclosed {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (z : S×TensorSpace N p) :
    actualHistory P (z.1,(residualTensorSpace (actualSpace P z))ᗮ.starProjection z.2)=
      actualHistory P z := by
  let V : Submodule ℝ (TensorSpace N p) := residualTensorSpace (actualSpace P z)
  let R : Residual N p 0 := initialIso N p (-(V.starProjection z.2))
  have hR : action (initialFrame N S (initialState z).1) R.val∈residualTensorSpace
      (physicalSpace N p n 0 S P (initialFrame N S)
        (past N p n 0 S (execute N p n 0 S P (initialState z)))) := by
    have hp : -(V.starProjection z.2)∈V := V.neg_mem (V.orthogonalProjectionOnto z.2).property
    simpa only [R,initialIso_coe,initialFrame,action_refl,V,actualSpace,actualHistory,
      Function.comp_def] using hp
  have hh := history_ignores_terminal_residual N p n 0 S P (initialFrame N S) (initialState z) R hR
  have he : initialState (z.1,Vᗮ.starProjection z.2)=((initialState z).1,(initialState z).2+R) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp only [initialState,initialIso_coe,Submodule.coe_add,R,Submodule.starProjection_orthogonal_val,sub_eq_add_neg]
  change past N p n 0 S (execute N p n 0 S P (initialState (z.1,Vᗮ.starProjection z.2)))=
    past N p n 0 S (execute N p n 0 S P (initialState z))
  rw [he]
  exact hh

@[expose]  def literalHistory {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (z : S×TensorSpace N p) : S×TensorSpace N p :=
  (z.1,(residualTensorSpace (actualSpace P z))ᗮ.starProjection z.2)

@[expose]  def encodePast {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (h : Past N p n 0 S) : S×TensorSpace N p :=
  (seed N p n 0 S h,physicalDisclosed N p n 0 S P (initialFrame N S) (fun _ => 0) h)

 theorem encodePast_measurable {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) : Measurable (encodePast P) := by
  have hF : Measurable (fun z : S×Vector N => initialFrame N S z.1 z.2) := measurable_snd
  exact (seed_measurable N p n 0 S).prodMk
    (physicalDisclosed_measurable N p n 0 S P (initialFrame N S) hF (D:=fun _=>0) measurable_const)

 theorem literalHistory_eq_encode {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) : literalHistory P=encodePast P∘actualHistory P := by
  funext z
  apply Prod.ext
  · exact (actual_original_seed N p n 0 S P (initialState z)).symm
  · exact (actual_original_disclosed_projection P z).symm

 theorem actualHistory_eq_replay {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) : actualHistory P=actualHistory P∘literalHistory P := by
  funext z
  exact (actual_history_replay_disclosed P z).symm

 theorem comap_actualHistory_eq_literal {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) :
    MeasurableSpace.comap (actualHistory P) inferInstance=
      MeasurableSpace.comap (literalHistory P) inferInstance := by
  apply le_antisymm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (actualHistory P)
      (actualHistory_measurable P) (actualHistory_eq_replay P)
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (encodePast P)
      (encodePast_measurable P) (literalHistory_eq_encode P)

 theorem actual_projected_conditional_gaussian_literal {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (μ : Measure S) [IsFiniteMeasure μ]
    (φ : TensorSpace N p→ℝ) (hφ : StronglyMeasurable φ) (C : ℝ) (hC : ∀J,‖φ J‖≤C) :
    (μ.prod (stdGaussian (TensorSpace N p)))[(fun z => φ ((residualTensorSpace (actualSpace P z)).starProjection z.2)) |
      MeasurableSpace.comap (literalHistory P) inferInstance]=ᵐ[μ.prod (stdGaussian (TensorSpace N p))]
      fun z => ∫J,φ ((residualTensorSpace (actualSpace P z)).starProjection J) ∂stdGaussian (TensorSpace N p) := by
  rw [←comap_actualHistory_eq_literal P]
  exact actual_projected_conditional_gaussian P μ φ hφ C hC

end SphericalAging.FiniteDisclosureExactHistory
