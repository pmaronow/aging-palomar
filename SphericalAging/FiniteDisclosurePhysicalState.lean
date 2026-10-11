module

public import SphericalAging.FiniteDisclosureTree
public import SphericalAging.PredictableTensorFrameState

public section

/-! The entire original ambient disorder survives a finite adaptive
history. Frames and disclosed tensors are constructed from its actual
Householder blocks, and dependent queries preserve the old state. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosurePhysicalState
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan CanonicalGramSelector CanonicalGramFlag PredictableGramStep
open PredictableTensorDisclosureStep PredictableTensorCanonicalRegeneration
open PredictableTensorProjectionIdentification PredictableTensorSpanIdentification
open TensorActionComposition
open TensorOrthogonalAction PredictableTensorFrameState BranchMeasurePreserving FiniteDisclosureTree

@[expose] abbrev Frame (N : ℕ) := Vector N≃ₗᵢ[ℝ]Vector N

@[expose] def freshFrame {N p r : ℕ} {S : Type} (x : S→Vector N) (F : S→Frame N)
    (h : S×Block N p r) : Frame N :=
  (frameUpdate (space N r) (direction N r) (x h.1)).trans (F h.1)

@[expose] def freshDisclosed {N p r : ℕ} {S : Type} (x : S→Vector N) (D : S→TensorSpace N p)
    (h : S×Block N p r) : TensorSpace N p :=
  action (frameUpdate (space N r) (direction N r) (x h.1)) (D h.1)+h.2.val.val

@[expose] def decode (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S→Frame N)→(S→TensorSpace N p)→Leaves N p n r S→TensorSpace N p
  | 0,_,_,_,_,F,D,z => action (F z.1) (D z.1+z.2.val)
  | n+1,r,S,_,P,F,D,z =>
    Sum.elim (decode N p n (r+1) (S×Block N p r) P.2.1
      (freshFrame P.1.val F) (freshDisclosed P.1.val D))
      (decode N p n r S P.2.2 F D) z

theorem actual_disorder_preserved (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (D : S→TensorSpace N p)
    (z : S×Residual N p r) :
    decode N p n r S P F D (execute N p n r S P z)=action (F z.1) (D z.1+z.2.val) := by
  induction n generalizing r S with
  | zero => rfl
  | succ n ih =>
    classical
    by_cases hx : P.1.val z.1∈space N r
    · simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_true_eq_false,if_false,id_eq,Sum.map_inr,decode,Sum.elim_inr] using
        ih r S P.2.2 F D z
    · simp only [execute,step,branchMap,mem_setOf_eq,hx,not_false_eq_true,if_true,Sum.map_inl,decode,Sum.elim_inl]
      rw [ih]
      exact (physical_disorder_preserved (space N r) (direction N r)
        (direction_mem_orthogonal N r) P.1.val D F z).symm

theorem freshDisclosed_mem {N p r : ℕ} {S : Type} (x : S→Vector N)
    (D : S→TensorSpace N p) (hD : ∀s,D s∈(Residual N p r)ᗮ)
    (h : S×Block N p r) : freshDisclosed x D h∈(Residual N p (r+1))ᗮ := by
  have hLe := residualTensorSpace_antitone (p:=p)
    (show space N r≤space N r⊔ℝ ∙ direction N r from le_sup_left)
  change action (frameUpdate (space N r) (direction N r) (x h.1)) (D h.1)+h.2.val.val∈_
  rw [Residual,space_next]
  apply Submodule.add_mem
  · intro R hR
    have hRO : action (frameUpdate (space N r) (direction N r) (x h.1)) R∈Residual N p r := by
      have hh : action (frameUpdate (space N r) (direction N r) (x h.1)) R∈
          (Residual N p r).map (action (frameUpdate (space N r) (direction N r) (x h.1))).toLinearEquiv.toLinearMap :=
        Submodule.mem_map.mpr ⟨R,hLe hR,rfl⟩
      simpa only [Residual,frameUpdate_tensorSpace _ (direction_mem_orthogonal N r)] using hh
    have hi := (action (p:=p) (frameUpdate (space N r) (direction N r) (x h.1))).inner_map_map R
      (action (frameUpdate (space N r) (direction N r) (x h.1)) (D h.1))
    rw [frame_tensor_involution] at hi
    exact hi.symm.trans ((hD h.1) _ hRO)
  · intro R hR
    let Rold : Residual N p r := ⟨R,hLe hR⟩
    have hRn : Rold∈newResidualSubspace (p:=p) (space N r) (direction N r) := hR
    exact h.2.property Rold hRn

end SphericalAging.FiniteDisclosurePhysicalState
