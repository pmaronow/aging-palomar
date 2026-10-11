module

public import SphericalAging.FiniteDisclosurePast

public section

/-! The original seed remains explicitly present and measurable in every
finite adaptive history, through both rank branches. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureSeedHistory
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure BranchMeasurePreserving
open FiniteDisclosureTree FiniteDisclosurePast PredictableTensorDisclosureStep CanonicalGramSelector

@[expose] def seed (N p : ℕ) : ∀(n r : ℕ) (S : Type), Past N p n r S→S
  | 0,_,_,s => s
  | n+1,r,S,s => Sum.elim (fun h => (seed N p n (r+1) (S×Block N p r) h).1)
      (seed N p n r S) s

theorem seed_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S] :
    Measurable (seed N p n r S) := by
  induction n generalizing r S with
  | zero => exact measurable_id
  | succ n ih =>
    have hf := measurable_fst.comp (ih (r+1) (S×Block N p r))
    exact hf.sumElim (ih r S)

theorem actual_original_seed (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (z : S×Residual N p r) :
    seed N p n r S (past N p n r S (execute N p n r S P z))=z.1 := by
  induction n generalizing r S with
  | zero => rfl
  | succ n ih =>
    classical
    by_cases hx : P.1.val z.1∈CanonicalVectorSpan.space N r
    · simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_true_eq_false,if_false,id_eq,
        Sum.map_inr,past,seed,Sum.elim_inr] using ih r S P.2.2 z
    · have hh := congrArg Prod.fst (ih (r+1) (S×Block N p r) P.2.1
        (history (p:=p) (CanonicalVectorSpan.space N r) (direction N r) (direction_mem_orthogonal N r) P.1.val z,
          nextResidual P.1.val z))
      simpa only [execute,step,branchMap,mem_setOf_eq,hx,not_false_eq_true,if_true,
        Sum.map_inl,past,seed,Sum.elim_inl,history,AdaptiveGaussianDisclosureStep.history] using hh

end SphericalAging.FiniteDisclosureSeedHistory
