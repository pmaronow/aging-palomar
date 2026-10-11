module

public import SphericalAging.PredictableTensorCanonicalRegeneration

public section

/-! Exact canonical disorder bookkeeping for a constructed Householder
history. Old disclosed disorder and the newly read tensor block combine
into the next disclosed tensor; the actual total disorder is preserved. -/
noncomputable section
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PredictableTensorFrameState
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure TensorOrthogonalAction
open PredictableGramStep PredictableTensorDisclosureStep PredictableTensorProjectionIdentification
open PredictableTensorCanonicalRegeneration TensorActionComposition
open scoped InnerProductSpace

@[expose] def newDisclosed {N p : ℕ} {S : Type*} (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) (x : S→Vector N) (D : S→TensorSpace N p)
    (z : S×residualTensorSpace (p:=p) W) : TensorSpace N p :=
  action (frameUpdate W e (x z.1)) (D z.1)+(history (p:=p) W e he x z).2.val.val

theorem updated_total_disorder {N p : ℕ} {S : Type*} (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) (x : S→Vector N) (D : S→TensorSpace N p)
    (z : S×residualTensorSpace (p:=p) W) :
    action (frameUpdate W e (x z.1)) (D z.1+z.2.val)=
      newDisclosed (p:=p) W e he x D z+(canonicalRemaining (p:=p) W e he x z).val := by
  have hh : tensorUpdate (p:=p) W e he (x z.1) z.2=
      (history (p:=p) W e he x z).2.val+(remainder (p:=p) W e he x z).val := by
    change tensorUpdate (p:=p) W e he (x z.1) z.2=
      (freshBlock (p:=p) W e).starProjection (tensorUpdate W e he (x z.1) z.2)+
      (freshBlock (p:=p) W e)ᗮ.starProjection (tensorUpdate W e he (x z.1) z.2)
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hc := congrArg (fun J : residualTensorSpace (p:=p) W => J.val) hh
  simp only [tensorUpdate_coe,Submodule.coe_add] at hc
  simp only [newDisclosed,canonicalRemaining,remainingIso_coe,map_add,hc]
  abel

theorem physical_disorder_preserved {N p : ℕ} {S : Type*} (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) (x : S→Vector N) (D : S→TensorSpace N p)
    (F : S→Vector N≃ₗᵢ[ℝ]Vector N) (z : S×residualTensorSpace (p:=p) W) :
    action (F z.1) (D z.1+z.2.val)=
      action ((frameUpdate W e (x z.1)).trans (F z.1))
        (newDisclosed (p:=p) W e he x D z+(canonicalRemaining (p:=p) W e he x z).val) := by
  rw [←updated_total_disorder W e he x D z,←action_trans,frame_tensor_involution]

theorem newDisclosed_mem_orthogonal {N p : ℕ} {S : Type*} (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) (x : S→Vector N) (D : S→TensorSpace N p)
    (hD : ∀s,D s∈(residualTensorSpace (p:=p) W)ᗮ)
    (z : S×residualTensorSpace (p:=p) W) :
    newDisclosed (p:=p) W e he x D z∈(residualTensorSpace (p:=p) (W⊔ℝ ∙ e))ᗮ := by
  have hLe := residualTensorSpace_antitone (p:=p) (show W≤W⊔ℝ ∙ e from le_sup_left)
  apply Submodule.add_mem
  · intro R hR
    have hRO : action (frameUpdate W e (x z.1)) R∈residualTensorSpace (p:=p) W := by
      have hh : action (frameUpdate W e (x z.1)) R∈(residualTensorSpace (p:=p) W).map
          (action (frameUpdate W e (x z.1))).toLinearEquiv.toLinearMap :=
        Submodule.mem_map.mpr ⟨R,hLe hR,rfl⟩
      simpa only [frameUpdate_tensorSpace W he] using hh
    have hi := (action (p:=p) (frameUpdate W e (x z.1))).inner_map_map R
      (action (frameUpdate W e (x z.1)) (D z.1))
    rw [frame_tensor_involution] at hi
    exact hi.symm.trans ((hD z.1) _ hRO)
  · intro R hR
    let Rold : residualTensorSpace (p:=p) W := ⟨R,hLe hR⟩
    have hRn : Rold∈newResidualSubspace (p:=p) W e := hR
    exact (history (p:=p) W e he x z).2.property Rold hRn


theorem newDisclosed_measurable_history {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (W : Submodule ℝ (Vector N)) (e : Vector N) (he : e∈Wᗮ)
    {x : S→Vector N} (hx : Measurable x) {D : S→TensorSpace N p} (hD : Measurable D) :
    Measurable[MeasurableSpace.comap (history (p:=p) W e he x) inferInstance]
      (newDisclosed (p:=p) W e he x D) := by
  let g : S×freshBlock (p:=p) W e→TensorSpace N p :=
    fun h => action (frameUpdate W e (x h.1)) (D h.1)+h.2.val.val
  have hu : Measurable (fun z : S×Vector N => frameUpdate W e (x z.1) z.2) :=
    frameUpdate_measurable W measurable_const (hx.comp measurable_fst) measurable_snd
  have harg : Measurable (fun h : S×freshBlock (p:=p) W e => (h.1,D h.1)) :=
    measurable_fst.prodMk (hD.comp measurable_fst)
  have hact := (action_measurable (p:=p) (fun s => frameUpdate W e (x s)) hu).comp harg
  have hb : Measurable (fun h : S×freshBlock (p:=p) W e => h.2.val.val) :=
    (((residualTensorSpace (p:=p) W).subtypeL.comp (freshBlock (p:=p) W e).subtypeL).measurable).comp
      measurable_snd
  have hg : Measurable g := hact.add hb
  have hEq : newDisclosed (p:=p) W e he x D=g∘history W e he x := rfl
  rw [hEq]
  exact hg.comp (Measurable.of_comap_le le_rfl)

theorem updated_frame_joint_measurable {N : ℕ} {S : Type*} [MeasurableSpace S]
    (W : Submodule ℝ (Vector N)) (e : Vector N) {x : S→Vector N} (hx : Measurable x)
    (F : S→Vector N≃ₗᵢ[ℝ]Vector N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (fun z : S×Vector N => ((frameUpdate W e (x z.1)).trans (F z.1)) z.2) := by
  have hu : Measurable (fun z : S×Vector N => frameUpdate W e (x z.1) z.2) :=
    frameUpdate_measurable W measurable_const (hx.comp measurable_fst) measurable_snd
  exact hF.comp (measurable_fst.prodMk hu)

end SphericalAging.PredictableTensorFrameState
