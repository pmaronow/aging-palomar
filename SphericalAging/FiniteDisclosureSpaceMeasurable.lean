module

public import SphericalAging.FiniteDisclosureAmbient
public import SphericalAging.OrthogonalInverseMeasurability

public section

/-! The physical vector-space projection of every constructed finite
history is measurable, including variable ranks and dependent queries. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureSpaceMeasurable
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure TensorResidualRotation
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureMeasurableState FiniteDisclosureAmbient OrthogonalInverseMeasurability

 theorem rotated_projection {N : ℕ} (W : Submodule ℝ (Vector N)) (F : Frame N) (x : Vector N) :
    (rotatedSpace F W).starProjection x=F (W.starProjection (F.symm x)) := by
  have hh := F.toLinearIsometry.map_starProjection W (F.symm x)
  change F (W.starProjection (F.symm x))=(rotatedSpace F W).starProjection (F (F.symm x)) at hh
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  exact hh.symm

 theorem rotated_projection_measurable {N : ℕ} {S : Type} [MeasurableSpace S]
    (W : Submodule ℝ (Vector N)) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (fun z : S×Vector N => (rotatedSpace (F z.1) W).starProjection z.2) := by
  have hi := inverse_joint_measurable F hF
  have hp : Measurable (fun z : S×Vector N => W.starProjection ((F z.1).symm z.2)) :=
    W.starProjection.continuous.measurable.comp hi
  have ha : Measurable (fun z : S×Vector N => (z.1,W.starProjection ((F z.1).symm z.2))) :=
    measurable_fst.prodMk hp
  have hc : Measurable ((fun z : S×Vector N => F z.1 z.2)∘
      (fun z : S×Vector N => (z.1,W.starProjection ((F z.1).symm z.2)))) := hF.comp ha
  convert hc using 1
  funext z
  exact rotated_projection W (F z.1) z.2

 theorem physicalSpace_projection_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (fun z : Past N p n r S×Vector N => (physicalSpace N p n r S P F z.1).starProjection z.2) := by
  induction n generalizing r S with
  | zero => exact rotated_projection_measurable (CanonicalVectorSpan.space N r) F hF
  | succ n ih =>
    have hL := ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F)
      (freshFrame_joint_measurable (p:=p) (r:=r) P.1.property F hF)
    have hR := ih r S P.2.2 F hF
    have hh := (hL.sumElim hR).comp
      (MeasurableEquiv.sumProdDistrib (Past N p n (r+1) (S×Block N p r))
        (Past N p n r S) (Vector N)).measurable
    convert hh using 1
    funext z
    rcases z with ⟨h,v⟩
    cases h <;> rfl

 theorem actual_vector_projection_measurable {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) {y : S×TensorSpace N p→Vector N}
    (hy : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance] y) :
    Measurable[MeasurableSpace.comap (actualHistory P) inferInstance]
      (fun z => (actualSpace P z).starProjection (y z)) := by
  have hm : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance] (actualHistory P) :=
    Measurable.of_comap_le le_rfl
  have ha : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance]
      (fun z => (actualHistory P z,y z)) := hm.prodMk hy
  have hc : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance]
      ((fun z : Past N p n 0 S×Vector N =>
        (physicalSpace N p n 0 S P (initialFrame N S) z.1).starProjection z.2)∘
        (fun z => (actualHistory P z,y z))) :=
    (physicalSpace_projection_measurable N p n 0 S P (initialFrame N S) measurable_snd).comp ha
  simpa only [Function.comp_def,actualSpace] using hc

end SphericalAging.FiniteDisclosureSpaceMeasurable
