module

public import SphericalAging.FiniteDisclosureResidual

public section

/-! Measurability of the finite tree's constructed physical frames and
residual tensor evaluations, without a random-frame measurability premise. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureMeasurableState
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure TensorOrthogonalAction
open PredictableTensorFrameState FiniteDisclosureTree FiniteDisclosurePhysicalState FiniteDisclosureResidual

theorem freshFrame_joint_measurable {N p r : ℕ} {S : Type} [MeasurableSpace S]
    {x : S→Vector N} (hx : Measurable x) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (fun z : (S×Block N p r)×Vector N => freshFrame x F z.1 z.2) := by
  have hh := updated_frame_joint_measurable (N:=N) (S:=S) (CanonicalVectorSpan.space N r)
    (CanonicalGramSelector.direction N r) hx F hF
  exact hh.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem physicalResidual_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (physicalResidual N p n r S P F) := by
  induction n generalizing r S with
  | zero =>
    change Measurable (fun z : S×Residual N p r => action (F z.1) z.2.val)
    have ha : Measurable (fun z : S×Residual N p r => (z.1,z.2.val)) :=
      measurable_fst.prodMk ((Residual N p r).subtypeL.measurable.comp measurable_snd)
    have hm : Measurable (fun z : S×TensorSpace N p => action (F z.1) z.2) :=
      action_measurable (N:=N) (p:=p) (S:=S) F hF
    have hComp : Measurable ((fun z : S×TensorSpace N p => action (F z.1) z.2)∘
        (fun z : S×Residual N p r => (z.1,z.2.val))) := hm.comp ha
    simpa only [Function.comp_def] using hComp
  | succ n ih =>
    exact (ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F)
      (freshFrame_joint_measurable (p:=p) (r:=r) P.1.property F hF)).sumElim
      (ih r S P.2.2 F hF)

end SphericalAging.FiniteDisclosureMeasurableState
