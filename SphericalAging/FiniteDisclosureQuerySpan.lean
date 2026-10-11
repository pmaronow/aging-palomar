module

public import SphericalAging.FiniteDisclosureResidual

public section

/-! The constructed terminal vector span is precisely the span generated
by the actual adaptive queries, including dependent and zero queries. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureQuerySpan
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan CanonicalGramSelector PredictableGramStep TensorResidualRotation
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open BranchMeasurePreserving PredictableTensorDisclosureStep

@[expose] def vectorListSpan {N : ℕ} (L : List (Vector N)) : Submodule ℝ (Vector N) :=
  Submodule.span ℝ {v | v∈L}

theorem vectorListSpan_nil (N : ℕ) : vectorListSpan ([] : List (Vector N))=⊥ := by
  simp [vectorListSpan]

theorem vectorListSpan_cons {N : ℕ} (x : Vector N) (L : List (Vector N)) :
    vectorListSpan (x::L)=ℝ ∙ x⊔vectorListSpan L := by
  have hh : {v | v∈x::L}=({x} : Set (Vector N))∪{v | v∈L} := by ext v;simp
  rw [vectorListSpan,hh,Submodule.span_union]
  rfl

theorem rotatedSpace_trans {N : ℕ} (U F : Frame N) (W : Submodule ℝ (Vector N)) :
    rotatedSpace (U.trans F) W=rotatedSpace F (rotatedSpace U W) := by
  have h : (U.trans F).toLinearEquiv.toLinearMap=F.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap := by
    ext x; rfl
  simp only [rotatedSpace,h,Submodule.map_comp]

theorem rotatedSpace_sup {N : ℕ} (F : Frame N) (W V : Submodule ℝ (Vector N)) :
    rotatedSpace F (W⊔V)=rotatedSpace F W⊔rotatedSpace F V :=
  Submodule.map_sup _ _ _

theorem rotatedSpace_singleton {N : ℕ} (F : Frame N) (x : Vector N) :
    rotatedSpace F (ℝ ∙ x)=ℝ ∙ F x := by
  simp only [rotatedSpace,Submodule.map_span,Set.image_singleton]
  rfl

theorem freshFrame_span {N p r : ℕ} {S : Type} (x : S→Vector N) (F : S→Frame N)
    (h : S×Block N p r) (hx : x h.1∉space N r) :
    rotatedSpace (freshFrame x F h) (space N (r+1))=
      rotatedSpace (F h.1) (space N r)⊔ℝ ∙ F h.1 (x h.1) := by
  have hh : rotatedSpace (frameUpdate (space N r) (direction N r) (x h.1)) (space N (r+1))=
      space N r⊔ℝ ∙ x h.1 := by
    simpa only [nextRank,if_neg hx] using updated_span r (x h.1)
  rw [freshFrame,rotatedSpace_trans,hh,rotatedSpace_sup,rotatedSpace_singleton]

@[expose] def queries (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S→Frame N)→S×Residual N p r→List (Vector N)
  | 0,_,_,_,_,_,_ => []
  | n+1,r,S,_,P,F,z => F z.1 (P.1.val z.1)::
    Sum.elim (queries N p n (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F))
      (queries N p n r S P.2.2 F) (step P.1.val z)

theorem actual_terminal_query_span (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (z : S×Residual N p r) :
    physicalSpace N p n r S P F (past N p n r S (execute N p n r S P z))=
      rotatedSpace (F z.1) (space N r)⊔vectorListSpan (queries N p n r S P F z) := by
  induction n generalizing r S with
  | zero => simp only [execute,past,physicalSpace,queries,vectorListSpan_nil,sup_bot_eq]
  | succ n ih =>
    classical
    by_cases hx : P.1.val z.1∈space N r
    · have hq : F z.1 (P.1.val z.1)∈rotatedSpace (F z.1) (space N r) :=
        Submodule.mem_map.mpr ⟨P.1.val z.1,hx,rfl⟩
      have hs : ℝ ∙ F z.1 (P.1.val z.1)≤rotatedSpace (F z.1) (space N r) :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr hq
      simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_true_eq_false,if_false,id_eq,
        Sum.map_inr,past,physicalSpace,queries,Sum.elim_inr,vectorListSpan_cons,←sup_assoc,
        sup_eq_left.mpr hs] using ih r S P.2.2 F z
    · have hi := ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F)
        (history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) P.1.val z,
          nextResidual P.1.val z)
      have hSpan := freshFrame_span P.1.val F
        (history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) P.1.val z) hx
      rw [hSpan] at hi
      simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_false_eq_true,if_true,
        Sum.map_inl,past,physicalSpace,queries,Sum.elim_inl,vectorListSpan_cons,
        history,AdaptiveGaussianDisclosureStep.history,sup_assoc] using hi

end SphericalAging.FiniteDisclosureQuerySpan
