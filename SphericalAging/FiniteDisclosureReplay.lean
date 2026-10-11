module

public import SphericalAging.FiniteDisclosureResidualShift

public section

/-! A complete finite adaptive history is unchanged when a tensor lying
in its final undisclosed space is added to the original disorder. -/
noncomputable section
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureReplay
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan CanonicalGramSelector PredictableGramStep
open PredictableTensorDisclosureStep PredictableTensorProjectionIdentification
open TensorOrthogonalAction TensorResidualRotation
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState
open FiniteDisclosureResidual FiniteDisclosureQuerySpan FiniteDisclosureResidualShift
open BranchMeasurePreserving

 theorem initial_physical_space_le (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (z : S×Residual N p r) :
    rotatedSpace (F z.1) (space N r)≤
      physicalSpace N p n r S P F (past N p n r S (execute N p n r S P z)) := by
  rw [actual_terminal_query_span]
  exact le_sup_left

 theorem history_ignores_terminal_residual (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (z : S×Residual N p r)
    (R : Residual N p r)
    (hR : action (F z.1) R.val∈residualTensorSpace
      (physicalSpace N p n r S P F (past N p n r S (execute N p n r S P z)))) :
    past N p n r S (execute N p n r S P (z.1,z.2+R))=
      past N p n r S (execute N p n r S P z) := by
  induction n generalizing r S with
  | zero => rfl
  | succ n ih =>
    classical
    by_cases hx : P.1.val z.1∈space N r
    · have hRd : action (F z.1) R.val∈residualTensorSpace
          (physicalSpace N p n r S P.2.2 F (past N p n r S (execute N p n r S P.2.2 z))) := by
        simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_true_eq_false,if_false,id_eq,
          Sum.map_inr,past,physicalSpace,Sum.elim_inr] using hR
      have hi := ih r S P.2.2 F z R hRd
      simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_true_eq_false,if_false,id_eq,
        Sum.map_inr,past] using congrArg Sum.inr hi
    · let h : S×Block N p r := history (p:=p) (space N r) (direction N r)
        (direction_mem_orthogonal N r) P.1.val z
      let w : (S×Block N p r)×Residual N p (r+1) := (h,nextResidual P.1.val z)
      let F' : S×Block N p r→Frame N := freshFrame P.1.val F
      have hRf : action (F z.1) R.val∈residualTensorSpace
          (physicalSpace N p n (r+1) (S×Block N p r) P.2.1 F'
            (past N p n (r+1) (S×Block N p r)
              (execute N p n (r+1) (S×Block N p r) P.2.1 w))) := by
        simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_false_eq_true,if_true,
          Sum.map_inl,past,physicalSpace,Sum.elim_inl,F',w,h] using hR
      have hRinitial : action (F z.1) R.val∈residualTensorSpace
          (rotatedSpace (F' h) (space N (r+1))) :=
        residualTensorSpace_antitone
          (initial_physical_space_le N p n (r+1) (S×Block N p r) P.2.1 F' w) hRf
      have hRnew : action (frameUpdate (space N r) (direction N r) (P.1.val z.1)) R.val∈Residual N p (r+1) := by
        apply (action_mem_residual_iff (F' h) (space N (r+1)) _).mp
        have he : action (F' h) (action (frameUpdate (space N r) (direction N r) (P.1.val z.1)) R.val)=
            action (F z.1) R.val := by
          exact updated_physical_residual P.1.val F z.1 R.val h.2
        rw [he]
        exact hRinitial
      let R' : Residual N p (r+1) := ⟨action (frameUpdate (space N r) (direction N r) (P.1.val z.1)) R.val,hRnew⟩
      have hR' : action (F' w.1) R'.val∈residualTensorSpace
          (physicalSpace N p n (r+1) (S×Block N p r) P.2.1 F'
            (past N p n (r+1) (S×Block N p r)
              (execute N p n (r+1) (S×Block N p r) P.2.1 w))) := by
        have he : action (F' w.1) R'.val=action (F z.1) R.val :=
          updated_physical_residual P.1.val F z.1 R.val h.2
        rw [he]
        exact hRf
      have hh := fresh_history_shift P.1.val z R hRnew
      have hr : nextResidual P.1.val (z.1,z.2+R)=nextResidual P.1.val z+R' := by
        apply Subtype.ext
        exact fresh_residual_shift P.1.val z R hRnew
      have hi := ih (r+1) (S×Block N p r) P.2.1 F' w R' hR'
      have he : (history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r)
          P.1.val (z.1,z.2+R),nextResidual P.1.val (z.1,z.2+R))=(w.1,w.2+R') := by
        exact Prod.ext hh hr
      simp only [execute,step,branchMap,mem_setOf_eq,hx,not_false_eq_true,if_true,
        Sum.map_inl,past]
      rw [he]
      exact congrArg Sum.inl hi

end SphericalAging.FiniteDisclosureReplay
