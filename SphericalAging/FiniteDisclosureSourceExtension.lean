module

public import SphericalAging.FiniteDisclosureQueryFactorization
public import SphericalAging.FiniteDisclosureAppend
public import SphericalAging.NestedProjectionDifference

public section

/-! Arbitrary directions measurable in the literal source history extend
the genuine finite adaptive Plan. Its new disclosed block is precisely
the projection onto the orthogonal difference of the two residual spaces. -/
noncomputable section
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureSourceExtension
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure
open PredictableTensorProjectionIdentification
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureAmbient FiniteDisclosureExactHistory FiniteDisclosureQueryFactorization
open FiniteDisclosureAppend

@[expose]  def pastQuery {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u) :
    Past N p n 0 S→Vector N :=
  Classical.choose (exists_past_vector_query P u hu)

 theorem pastQuery_measurable {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u) :
    Measurable (pastQuery P u hu) :=
  (Classical.choose_spec (exists_past_vector_query P u hu)).1

 theorem actual_pastQuery {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u)
    (z : S×TensorSpace N p) : pastQuery P u hu (actualHistory P z)=u z :=
  (congrFun (Classical.choose_spec (exists_past_vector_query P u hu)).2 z).symm

@[expose]  def extend {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u) : Plan N p (n+1) 0 S :=
  appendPhysicalQuery N p n 0 S P (initialFrame N S) measurable_snd
    (pastQuery P u hu) (pastQuery_measurable P u hu)

 theorem actual_extended_space {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u)
    (z : S×TensorSpace N p) : actualSpace (extend P u hu) z=actualSpace P z⊔ℝ ∙ u z := by
  have hh := appendPhysicalQuery_terminal_span N p n 0 S P (initialFrame N S) measurable_snd
    (pastQuery P u hu) (pastQuery_measurable P u hu) (initialState z)
  change actualSpace (extend P u hu) z=actualSpace P z⊔ℝ ∙ pastQuery P u hu (actualHistory P z) at hh
  rw [actual_pastQuery] at hh
  exact hh

@[expose]  def newBlock {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u)
    (z : S×TensorSpace N p) : TensorSpace N p :=
  (residualTensorSpace (actualSpace P z)⊓
    (residualTensorSpace (actualSpace (extend P u hu) z))ᗮ).starProjection z.2

 theorem actual_newBlock_disclosed_difference {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u)
    (z : S×TensorSpace N p) : newBlock P u hu z=(literalHistory (extend P u hu) z).2-(literalHistory P z).2 := by
  have hs : actualSpace P z≤actualSpace (extend P u hu) z := by
    rw [actual_extended_space]
    exact le_sup_left
  rw [newBlock,NestedProjectionDifference.projection_difference _ _ (residualTensorSpace_antitone hs)]
  simp only [literalHistory,Submodule.starProjection_orthogonal_val]
  abel

 theorem actual_oldHistory_measurable_new {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u) :
    Measurable[MeasurableSpace.comap (actualHistory (extend P u hu)) inferInstance] (actualHistory P) := by
  have hm : Measurable[MeasurableSpace.comap (actualHistory (extend P u hu)) inferInstance]
      (actualHistory (extend P u hu)) := Measurable.of_comap_le le_rfl
  have hd := (dropLastPast_measurable N p n 0 S).comp hm
  have he : dropLastPast N p n 0 S∘actualHistory (extend P u hu)=actualHistory P := by
    funext z
    exact appendQuery_preserves_past N p n 0 S P
      (canonicalQuery N p n 0 S P (initialFrame N S) (pastQuery P u hu))
      (canonicalQuery_measurable N p n 0 S P (initialFrame N S) measurable_snd
        (pastQuery P u hu) (pastQuery_measurable P u hu)) (initialState z)
  rw [he] at hd
  exact hd

@[expose]  def stepHistory {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u)
    (z : S×TensorSpace N p) : (S×TensorSpace N p)×TensorSpace N p :=
  (literalHistory P z,newBlock P u hu z)

 theorem comap_extendedHistory_eq_step {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u) :
    MeasurableSpace.comap (literalHistory (extend P u hu)) inferInstance=
      MeasurableSpace.comap (stepHistory P u hu) inferInstance := by
  have hOld : Measurable[MeasurableSpace.comap (actualHistory (extend P u hu)) inferInstance]
      (literalHistory P) := by
    rw [literalHistory_eq_encode P]
    exact (encodePast_measurable P).comp (actual_oldHistory_measurable_new P u hu)
  have hOld' : Measurable[MeasurableSpace.comap (literalHistory (extend P u hu)) inferInstance]
      (literalHistory P) := by
    rw [comap_actualHistory_eq_literal] at hOld
    exact hOld
  have hNew : Measurable[MeasurableSpace.comap (literalHistory (extend P u hu)) inferInstance]
      (literalHistory (extend P u hu)) := Measurable.of_comap_le le_rfl
  have hBlock : Measurable[MeasurableSpace.comap (literalHistory (extend P u hu)) inferInstance]
      (newBlock P u hu) := by
    have he : newBlock P u hu=(fun z => (literalHistory (extend P u hu) z).2-(literalHistory P z).2) := by
      funext z;exact actual_newBlock_disclosed_difference P u hu z
    rw [he]
    exact hNew.snd.sub hOld'.snd
  apply le_antisymm
  · let f : (S×TensorSpace N p)×TensorSpace N p→S×TensorSpace N p := fun h => (h.1.1,h.1.2+h.2)
    have hf : Measurable f := (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).add measurable_snd)
    apply MeasurableSpace.comap_le_comap_of_eq_comp f hf
    funext z
    apply Prod.ext
    · rfl
    · change (literalHistory (extend P u hu) z).2=(literalHistory P z).2+newBlock P u hu z
      rw [actual_newBlock_disclosed_difference]
      abel
  · exact (hOld'.prodMk hBlock).comap_le

end SphericalAging.FiniteDisclosureSourceExtension
