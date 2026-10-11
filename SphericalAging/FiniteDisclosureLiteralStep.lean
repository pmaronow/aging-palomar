module

public import SphericalAging.FiniteDisclosureMeasurableState
public import SphericalAging.OrthogonalInverseMeasurability

public section

/-! The actual one-step canonical disclosure history generates exactly
the old past and the newly disclosed physical tensor block. The inverse
is constructed by orthogonal actions and fixed orthogonal projections. -/
noncomputable section
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureLiteralStep
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePhysicalState FiniteDisclosureMeasurableState
open CanonicalVectorSpan CanonicalGramSelector PredictableGramStep
open PredictableTensorDisclosureStep TensorOrthogonalAction TensorActionComposition
open OrthogonalInverseMeasurability BranchMeasurePreserving
variable {N p r : ℕ} {S : Type} [MeasurableSpace S]

@[expose] def physicalBlock (x : S→Vector N) (F : S→Frame N) (z : S×Block N p r) : TensorSpace N p :=
  action (F z.1) (action (frameUpdate (space N r) (direction N r) (x z.1)) z.2.val.val)

@[expose] def canonicalBlock (x : S→Vector N) (F : S→Frame N) (z : S×TensorSpace N p) : Block N p r :=
  (Block N p r).orthogonalProjectionOnto ((Residual N p r).orthogonalProjectionOnto
    (action (frameUpdate (space N r) (direction N r) (x z.1)) (action (F z.1).symm z.2)))

theorem canonicalBlock_physicalBlock (x : S→Vector N) (F : S→Frame N)
    (s : S) (b : Block N p r) : canonicalBlock x F (s,physicalBlock x F (s,b))=b := by
  have hInv (A : TensorSpace N p) : action (F s).symm (action (F s) A)=A := by
    rw [action_trans,LinearIsometryEquiv.self_trans_symm,action_refl]
  unfold canonicalBlock physicalBlock
  rw [hInv,frame_tensor_involution]
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem physicalBlock_measurable {x : S→Vector N} (hx : Measurable x)
    (F : S→Frame N) (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (physicalBlock (p:=p) (r:=r) x F) := by
  have hB : Measurable (fun z : S×Block N p r => (z,z.2.val.val)) :=
    measurable_id.prodMk (measurable_subtype_coe.comp
      (measurable_subtype_coe.comp measurable_snd))
  have hm : Measurable (fun z : (S×Block N p r)×TensorSpace N p =>
      action (freshFrame (p:=p) (r:=r) x F z.1) z.2) :=
    action_measurable (N:=N) (p:=p) (S:=S×Block N p r) (freshFrame (p:=p) (r:=r) x F)
      (freshFrame_joint_measurable (p:=p) (r:=r) hx F hF)
  have hComp : Measurable ((fun z : (S×Block N p r)×TensorSpace N p =>
      action (freshFrame (p:=p) (r:=r) x F z.1) z.2)∘
      (fun z : S×Block N p r => (z,z.2.val.val))) := hm.comp hB
  have he : physicalBlock (p:=p) (r:=r) x F=
      fun z : S×Block N p r => action (freshFrame (p:=p) (r:=r) x F z) z.2.val.val := by
    funext z
    dsimp only [physicalBlock,freshFrame]
    exact action_trans (F z.1) (frameUpdate (space N r) (direction N r) (x z.1)) z.2.val.val
  rw [he]
  simpa only [Function.comp_def] using hComp

theorem canonicalBlock_measurable {x : S→Vector N} (hx : Measurable x)
    (F : S→Frame N) (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (canonicalBlock (p:=p) (r:=r) x F) := by
  have hU : Measurable (fun z : S×Vector N => frameUpdate (space N r) (direction N r) (x z.1) z.2) :=
    frameUpdate_measurable _ measurable_const (hx.comp measurable_fst) measurable_snd
  have hInv := action_measurable (p:=p) (fun s => (F s).symm) (inverse_joint_measurable F hF)
  have hAct := (action_measurable (p:=p) (fun s => frameUpdate (space N r) (direction N r) (x s)) hU).comp
    (measurable_fst.prodMk hInv)
  exact (Block N p r).orthogonalProjectionOnto.measurable.comp
    ((Residual N p r).orthogonalProjectionOnto.measurable.comp hAct)

@[expose] def stepPast (x : S→Vector N) (z : S×Residual N p r) : (S×Block N p r)⊕S :=
  Sum.map Prod.fst Prod.fst (step x z)

theorem stepPast_measurable {x : S→Vector N} (hx : Measurable x) :
    Measurable (stepPast (p:=p) (r:=r) x) :=
  (measurable_fst.sumMap measurable_fst).comp (actual_step_law (p:=p) (r:=r) (0 : Measure S) hx).measurable

@[expose] def encode (x : S→Vector N) (F : S→Frame N) : (S×Block N p r)⊕S→S×TensorSpace N p :=
  Sum.elim (fun z => (z.1,physicalBlock x F z)) (fun s => (s,0))

theorem encode_fresh_component (x : S→Vector N) (F : S→Frame N) (s : S) (b : Block N p r) :
    encode x F (Sum.inl (s,b))=(s,physicalBlock x F (s,b)) := rfl

theorem encode_dependent_component (x : S→Vector N) (F : S→Frame N) (s : S) :
    encode (p:=p) (r:=r) x F (Sum.inr s)=(s,0) := rfl

@[expose] def decode (x : S→Vector N) (F : S→Frame N) (z : S×TensorSpace N p) : (S×Block N p r)⊕S := by
  classical
  exact if x z.1∉space N r then Sum.inl (z.1,canonicalBlock x F z) else Sum.inr z.1

theorem encode_measurable {x : S→Vector N} (hx : Measurable x)
    (F : S→Frame N) (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (encode (p:=p) (r:=r) x F) :=
  (measurable_fst.prodMk (physicalBlock_measurable hx F hF)).sumElim (measurable_id.prodMk measurable_const)

theorem decode_measurable {x : S→Vector N} (hx : Measurable x)
    (F : S→Frame N) (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (decode (p:=p) (r:=r) x F) := by
  have hA : MeasurableSet {z : S×TensorSpace N p | x z.1∉space N r} :=
    ((space N r).closed_of_finiteDimensional.measurableSet.preimage (hx.comp measurable_fst)).compl
  classical
  exact (measurable_inl.comp (measurable_fst.prodMk (canonicalBlock_measurable hx F hF))).ite hA
    (measurable_inr.comp measurable_fst)

theorem decode_encode_stepPast (x : S→Vector N) (F : S→Frame N) (z : S×Residual N p r) :
    decode x F (encode x F (stepPast x z))=stepPast x z := by
  classical
  by_cases hx : x z.1∈space N r
  · simp [stepPast,step,branchMap,hx,encode,decode]
  · simp only [stepPast,step,branchMap,mem_setOf_eq,hx,not_false_eq_true,ite_true,Sum.map_inl]
    change decode x F (encode x F (Sum.inl (history _ _ _ x z)))=Sum.inl (history _ _ _ x z)
    simp only [encode,Sum.elim_inl,decode,history,AdaptiveGaussianDisclosureStep.history,hx,
      not_false_eq_true,ite_true]
    rw [canonicalBlock_physicalBlock]

theorem comap_stepPast_eq_literal {x : S→Vector N} (hx : Measurable x)
    (F : S→Frame N) (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    MeasurableSpace.comap (stepPast (p:=p) (r:=r) x) inferInstance=
      MeasurableSpace.comap (encode x F∘stepPast x) inferInstance := by
  apply le_antisymm
  · apply MeasurableSpace.comap_le_comap_of_eq_comp (decode x F) (decode_measurable hx F hF)
    funext z
    exact (decode_encode_stepPast x F z).symm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (encode x F) (encode_measurable hx F hF) rfl

end SphericalAging.FiniteDisclosureLiteralStep
