module

public import SphericalAging.FiniteDisclosureGradientState
public import SphericalAging.FiniteDisclosureAmbient

public section

/-! The total disclosed tensor of the true finite history is measurable
in that history and equals the complementary projection of original disorder. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureDisclosed
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure TensorOrthogonalAction
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureMeasurableState FiniteDisclosureGradientState FiniteDisclosureAmbient

@[expose] def physicalDisclosed (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S→Frame N)→(S→TensorSpace N p)→Past N p n r S→TensorSpace N p
  | 0,_,_,_,_,F,D,s => action (F s) (D s)
  | n+1,r,S,_,P,F,D,s =>
    Sum.elim (physicalDisclosed N p n (r+1) (S×Block N p r) P.2.1
      (freshFrame P.1.val F) (freshDisclosed P.1.val D))
      (physicalDisclosed N p n r S P.2.2 F D) s

theorem actual_disorder_decomposition (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (D : S→TensorSpace N p) (z : Leaves N p n r S) :
    decode N p n r S P F D z=physicalDisclosed N p n r S P F D (past N p n r S z)+
      physicalResidual N p n r S P F z := by
  induction n generalizing r S with
  | zero => exact map_add _ _ _
  | succ n ih =>
    cases z with
    | inl z => exact ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F) (freshDisclosed P.1.val D) z
    | inr z => exact ih r S P.2.2 F D z

theorem actual_disclosed_is_projection (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (D : S→TensorSpace N p)
    (hD : ∀s,D s∈(Residual N p r)ᗮ) (z : Leaves N p n r S) :
    physicalDisclosed N p n r S P F D (past N p n r S z)=
      (residualTensorSpace (physicalSpace N p n r S P F (past N p n r S z)))ᗮ.starProjection
        (decode N p n r S P F D z) := by
  rw [Submodule.starProjection_orthogonal_val,←actual_residual_is_projection N p n r S P F D hD z,
    actual_disorder_decomposition,add_sub_cancel_right]

theorem physicalDisclosed_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2))
    {D : S→TensorSpace N p} (hD : Measurable D) :
    Measurable (physicalDisclosed N p n r S P F D) := by
  induction n generalizing r S with
  | zero =>
    have harg : Measurable (fun s => (s,D s)) := measurable_id.prodMk hD
    have hh : Measurable ((fun z : S×TensorSpace N p => action (F z.1) z.2)∘(fun s => (s,D s))) :=
      (action_measurable (p:=p) F hF).comp harg
    have hEq : physicalDisclosed N p 0 r S P F D=(fun s => action (F s) (D s)) := rfl
    rw [hEq]
    simpa only [Function.comp_def] using hh
  | succ n ih =>
    exact (ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F)
      (freshFrame_joint_measurable (p:=p) (r:=r) P.1.property F hF)
      (freshDisclosed_measurable P.1.property hD)).sumElim
      (ih r S P.2.2 F hF hD)

theorem actual_original_disclosed_projection {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (z : S×TensorSpace N p) :
    physicalDisclosed N p n 0 S P (initialFrame N S) (fun _ => 0) (actualHistory P z)=
      (residualTensorSpace (actualSpace P z))ᗮ.starProjection z.2 := by
  have hh := actual_disclosed_is_projection N p n 0 S P (initialFrame N S) (fun _ => 0)
    (fun _ => Submodule.zero_mem _) (execute N p n 0 S P (initialState z))
  rw [actual_disorder_preserved] at hh
  simpa only [actualHistory,actualSpace,Function.comp_def,initialState,initialFrame,zero_add,
    initialIso_coe,TensorActionComposition.action_refl] using hh

theorem actual_disclosed_measurable_history {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) :
    Measurable[MeasurableSpace.comap (actualHistory P) inferInstance]
      (fun z : S×TensorSpace N p => (residualTensorSpace (actualSpace P z))ᗮ.starProjection z.2) := by
  have hF : Measurable (fun z : S×Vector N => initialFrame N S z.1 z.2) := measurable_snd
  have hD := physicalDisclosed_measurable N p n 0 S P (initialFrame N S) hF (D:=fun _ => 0) measurable_const
  have hh := hD.comp (Measurable.of_comap_le le_rfl :
    Measurable[MeasurableSpace.comap (actualHistory P) inferInstance] (actualHistory P))
  convert hh using 1
  funext z
  exact (actual_original_disclosed_projection P z).symm

end SphericalAging.FiniteDisclosureDisclosed
