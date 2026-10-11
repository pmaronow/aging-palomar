module

public import SphericalAging.GenericEulerDisclosureMemory
public import SphericalAging.FiniteDisclosureAmbient
public import SphericalAging.FiniteDisclosureQuerySpan

public section

/-! A finite list of seed-measurable physical vectors initializes a literal
random-rank Gaussian disclosure, without choosing a measurable frame in
advance. The actual terminal space is exactly their span. -/
noncomputable section
namespace SphericalAging.VectorSeedDisclosurePlan
open Set MeasureTheory FiniteModel HardSphereDynamics AdaptiveGradientDisclosure
open TensorOrthogonalAction TensorResidualRotation CanonicalVectorSpan
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState
open FiniteDisclosureQuerySpan GenericEulerDisclosureMemory FrameInverseMeasurable
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

@[expose] def query {N p r : ℕ} {S : Type} [MeasurableSpace S] (m : Memory N p r S)
    (u : S→Vector N) (s : S) : Vector N := (m.frame s).symm (u s)

theorem query_measurable {N p r : ℕ} {S : Type} [MeasurableSpace S]
    (m : Memory N p r S) {u : S→Vector N} (hu : Measurable u) : Measurable (query m u) :=
  (inverse_joint_measurable m.frame m.frame_measurable).comp (measurable_id.prodMk hu)

@[expose] def plan {N p : ℕ} (i : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    (m : Memory N p r S)→(u : ℕ→S→Vector N)→(∀j,Measurable (u j))→Plan N p n r S
  | 0,_,_,_,_,_,_ => ()
  | n+1,r,S,_,m,u,hu =>
    (⟨query m (u i),query_measurable m (hu i)⟩,
      plan (i+1) n (r+1) (S×Block N p r)
        (fresh m (query m (u i)) (query_measurable m (hu i)) m.state m.state_measurable)
        (fun j => u j∘Prod.fst) (fun j => (hu j).comp measurable_fst),
      plan (i+1) n r S m u hu)

@[expose] def vectors {N : ℕ} {S : Type} (u : ℕ→S→Vector N) (i : ℕ) : ℕ→S→List (Vector N)
  | 0,_ => []
  | n+1,s => u i s::vectors u (i+1) n s

theorem vectors_lift {N : ℕ} {S B : Type} (u : ℕ→S→Vector N) (i n : ℕ) (s : S×B) :
    vectors (fun j => u j∘Prod.fst) i n s=vectors u i n s.1 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [vectors,Function.comp_apply,ih]

theorem actual_queries {N p : ℕ} (i n r : ℕ) (S : Type) [MeasurableSpace S]
    (m : Memory N p r S) (u : ℕ→S→Vector N) (hu : ∀j,Measurable (u j))
    (z : S×Residual N p r) :
    queries N p n r S (plan i n r S m u hu) m.frame z=vectors u i n z.1 := by
  induction n generalizing i r S with
  | zero => rfl
  | succ n ih =>
    classical
    have hq : m.frame z.1 (query m (u i) z.1)=u i z.1 :=
      (m.frame z.1).apply_symm_apply _
    by_cases hx : query m (u i) z.1∈space N r
    · simpa only [plan,queries,step,BranchMeasurePreserving.branchMap,mem_setOf_eq,hx,
        not_true_eq_false,if_false,id_eq,Sum.elim_inr,hq,vectors]
        using congrArg (fun L => u i z.1::L) (ih (i+1) r S m u hu z)
    · have hh := ih (i+1) (r+1) (S×Block N p r)
        (fresh m (query m (u i)) (query_measurable m (hu i)) m.state m.state_measurable)
        (fun j => u j∘Prod.fst) (fun j => (hu j).comp measurable_fst)
        (PredictableTensorDisclosureStep.history (p:=p) (space N r) (CanonicalGramSelector.direction N r)
          (CanonicalGramSelector.direction_mem_orthogonal N r) (query m (u i)) z,
          nextResidual (query m (u i)) z)
      rw [vectors_lift] at hh
      simpa only [plan,queries,step,BranchMeasurePreserving.branchMap,mem_setOf_eq,hx,
        not_false_eq_true,if_true,Sum.elim_inl,hq,
        fresh,PredictableTensorDisclosureStep.history,AdaptiveGaussianDisclosureStep.history,vectors]
        using congrArg (fun L => u i z.1::L) hh

theorem actual_terminal_span {N p : ℕ} (i n r : ℕ) (S : Type) [MeasurableSpace S]
    (m : Memory N p r S) (u : ℕ→S→Vector N) (hu : ∀j,Measurable (u j))
    (z : S×Residual N p r) :
    FiniteDisclosureResidual.physicalSpace N p n r S (plan i n r S m u hu) m.frame
      (past N p n r S (execute N p n r S (plan i n r S m u hu) z))=
      rotatedSpace (m.frame z.1) (space N r)⊔vectorListSpan (vectors u i n z.1) := by
  rw [actual_terminal_query_span,actual_queries]

end SphericalAging.VectorSeedDisclosurePlan
