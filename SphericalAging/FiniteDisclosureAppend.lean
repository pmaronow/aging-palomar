module

public import SphericalAging.FiniteDisclosureLiteralStep
public import SphericalAging.FiniteDisclosureQuerySpan

public section

/-! A finite disclosure plan can be extended by any measurable terminal-past
query. Physical queries are pulled back through the actual terminal frame. -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureAppend
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan CanonicalGramSelector PredictableGramStep TensorResidualRotation
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureMeasurableState FiniteDisclosureQuerySpan OrthogonalInverseMeasurability
open BranchMeasurePreserving PredictableTensorDisclosureStep

/-- Actual terminal frame, expressed as a function of the terminal past. -/
@[expose] def terminalFrame (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S→Frame N)→Past N p n r S→Frame N
  | 0,_,_,_,_,F,s => F s
  | n+1,r,S,_,P,F,s =>
    Sum.elim (terminalFrame N p n (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F))
      (terminalFrame N p n r S P.2.2 F) s

theorem terminalFrame_joint_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2)) :
    Measurable (fun z : Past N p n r S×Vector N => terminalFrame N p n r S P F z.1 z.2) := by
  induction n generalizing r S with
  | zero => exact hF
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

theorem physicalSpace_eq_terminalFrame (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (h : Past N p n r S) :
    ∃k : ℕ, physicalSpace N p n r S P F h=
      rotatedSpace (terminalFrame N p n r S P F h) (space N k) := by
  induction n generalizing r S with
  | zero => exact ⟨r,rfl⟩
  | succ n ih =>
    cases h with
    | inl h => exact ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F) h
    | inr h => exact ih r S P.2.2 F h

/-- Append a canonical-coordinate query measurable in the entire existing past. -/
@[expose] def appendQuery (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    (P : Plan N p n r S)→(q : Past N p n r S→Vector N)→Measurable q→Plan N p (n+1) r S
  | 0,_,_,_,_,q,hq => (⟨q,hq⟩,(),())
  | n+1,r,S,_,P,q,hq =>
    (P.1,appendQuery N p n (r+1) (S×Block N p r) P.2.1 (q∘Sum.inl) (hq.comp measurable_inl),
      appendQuery N p n r S P.2.2 (q∘Sum.inr) (hq.comp measurable_inr))

/-- Discard the final disclosed block from an extended terminal past. -/
@[expose] def dropLastPast (N p : ℕ) : (n r : ℕ)→(S : Type)→Past N p (n+1) r S→Past N p n r S
  | 0,_,_,h => Sum.elim Prod.fst id h
  | n+1,r,S,h => Sum.map (dropLastPast N p n (r+1) (S×Block N p r))
      (dropLastPast N p n r S) h

theorem dropLastPast_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S] :
    Measurable (dropLastPast N p n r S) := by
  induction n generalizing r S with
  | zero => exact measurable_fst.sumElim measurable_id
  | succ n ih => exact (ih (r+1) (S×Block N p r)).sumMap (ih r S)

theorem appendQuery_preserves_past (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (q : Past N p n r S→Vector N) (hq : Measurable q)
    (z : S×Residual N p r) :
    dropLastPast N p n r S (past N p (n+1) r S (execute N p (n+1) r S (appendQuery N p n r S P q hq) z))=
      past N p n r S (execute N p n r S P z) := by
  induction n generalizing r S with
  | zero =>
    classical
    by_cases hx : q z.1∈space N r <;>
      simp [appendQuery,execute,past,dropLastPast,step,branchMap,hx,history,
        AdaptiveGaussianDisclosureStep.history]
  | succ n ih =>
    classical
    by_cases hx : P.1.val z.1∈space N r
    · simpa only [appendQuery,execute,step,branchMap,mem_ofPred_eq,hx,not_true_eq_false,
        if_false,id_eq,Sum.map_inr,past,dropLastPast] using
        congrArg Sum.inr (ih r S P.2.2 (q∘Sum.inr) (hq.comp measurable_inr) z)
    · simpa only [appendQuery,execute,step,branchMap,mem_ofPred_eq,hx,not_false_eq_true,
        if_true,Sum.map_inl,past,dropLastPast] using
        congrArg Sum.inl (ih (r+1) (S×Block N p r) P.2.1 (q∘Sum.inl) (hq.comp measurable_inl)
          (history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) P.1.val z,
            nextResidual P.1.val z))

theorem appendQuery_terminal_span (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (q : Past N p n r S→Vector N) (hq : Measurable q)
    (z : S×Residual N p r) :
    physicalSpace N p (n+1) r S (appendQuery N p n r S P q hq) F
      (past N p (n+1) r S (execute N p (n+1) r S (appendQuery N p n r S P q hq) z))=
    physicalSpace N p n r S P F (past N p n r S (execute N p n r S P z))⊔
      ℝ ∙ terminalFrame N p n r S P F (past N p n r S (execute N p n r S P z))
        (q (past N p n r S (execute N p n r S P z))) := by
  induction n generalizing r S with
  | zero =>
    classical
    by_cases hx : q z.1∈space N r
    · have hmem : F z.1 (q z.1)∈rotatedSpace (F z.1) (space N r) :=
        Submodule.mem_map.mpr ⟨q z.1,hx,rfl⟩
      have hs : ℝ ∙ F z.1 (q z.1)≤rotatedSpace (F z.1) (space N r) :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
      simp only [appendQuery,execute,step,branchMap,mem_ofPred_eq,hx,not_true_eq_false,
        if_false,id_eq,Sum.map_inr,past,physicalSpace,terminalFrame,Sum.elim_inr,sup_eq_left.mpr hs]
    · simpa only [appendQuery,execute,step,branchMap,mem_ofPred_eq,hx,not_false_eq_true,
        if_true,Sum.map_inl,past,physicalSpace,terminalFrame,Sum.elim_inl,history,AdaptiveGaussianDisclosureStep.history] using
        freshFrame_span q F
          (history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) q z) hx
  | succ n ih =>
    classical
    by_cases hx : P.1.val z.1∈space N r
    · simpa only [appendQuery,execute,step,branchMap,mem_ofPred_eq,hx,not_true_eq_false,
        if_false,id_eq,Sum.map_inr,past,physicalSpace,terminalFrame,Sum.elim_inr,Function.comp_def] using
        ih r S P.2.2 F (q∘Sum.inr) (hq.comp measurable_inr) z
    · simpa only [appendQuery,execute,step,branchMap,mem_ofPred_eq,hx,not_false_eq_true,
        if_true,Sum.map_inl,past,physicalSpace,terminalFrame,Sum.elim_inl,Function.comp_def] using
        ih (r+1) (S×Block N p r) P.2.1 (freshFrame P.1.val F) (q∘Sum.inl) (hq.comp measurable_inl)
          (history (p:=p) (space N r) (direction N r) (direction_mem_orthogonal N r) P.1.val z,
            nextResidual P.1.val z)

/-- Canonical coordinates of a measurable physical query at the terminal past. -/
@[expose] def canonicalQuery (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (u : Past N p n r S→Vector N)
    (h : Past N p n r S) : Vector N := (terminalFrame N p n r S P F h).symm (u h)

theorem canonicalQuery_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2))
    (u : Past N p n r S→Vector N) (hu : Measurable u) :
    Measurable (canonicalQuery N p n r S P F u) :=
  (inverse_joint_measurable (terminalFrame N p n r S P F)
    (terminalFrame_joint_measurable N p n r S P F hF)).comp (measurable_id.prodMk hu)

/-- Extend a plan by one physical query using the actual terminal frame. -/
@[expose] def appendPhysicalQuery (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2))
    (u : Past N p n r S→Vector N) (hu : Measurable u) : Plan N p (n+1) r S :=
  appendQuery N p n r S P (canonicalQuery N p n r S P F u)
    (canonicalQuery_measurable N p n r S P F hF u hu)

theorem appendPhysicalQuery_terminal_span (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2))
    (u : Past N p n r S→Vector N) (hu : Measurable u) (z : S×Residual N p r) :
    physicalSpace N p (n+1) r S (appendPhysicalQuery N p n r S P F hF u hu) F
      (past N p (n+1) r S (execute N p (n+1) r S (appendPhysicalQuery N p n r S P F hF u hu) z))=
      physicalSpace N p n r S P F (past N p n r S (execute N p n r S P z))⊔
        ℝ ∙ u (past N p n r S (execute N p n r S P z)) := by
  simpa only [appendPhysicalQuery,canonicalQuery,LinearIsometryEquiv.apply_symm_apply] using
    appendQuery_terminal_span N p n r S P F (canonicalQuery N p n r S P F u)
      (canonicalQuery_measurable N p n r S P F hF u hu) z

theorem appendQuery_history_comap_le (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (q : Past N p n r S→Vector N) (hq : Measurable q) :
    MeasurableSpace.comap (fun z : S×Residual N p r => past N p n r S (execute N p n r S P z)) inferInstance≤
      MeasurableSpace.comap (fun z : S×Residual N p r => past N p (n+1) r S
        (execute N p (n+1) r S (appendQuery N p n r S P q hq) z)) inferInstance := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp (dropLastPast N p n r S)
    (dropLastPast_measurable N p n r S)
  funext z
  exact (appendQuery_preserves_past N p n r S P q hq z).symm

end SphericalAging.FiniteDisclosureAppend
