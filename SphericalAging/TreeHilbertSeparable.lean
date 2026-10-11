module

public import SphericalAging.CausalTree
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Bases

public section

/-! Genuine separability of the completed causal-tree Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter UniformSpace TopologicalSpace
open scoped ENNReal TensorProduct Topology InnerProductSpace
namespace SphericalAging.TreeHilbertSeparable
open CausalTree CausalTree.HilbertDatum
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩

theorem tensor_separable (A B : HilbertDatum)
    [TopologicalSpace.SeparableSpace A.Carrier] [TopologicalSpace.SeparableSpace B.Carrier] :
    TopologicalSpace.SeparableSpace (tensor A B).Carrier := by
  let f := fun p : A.Carrier × B.Carrier => pure A B p.1 p.2
  have hf : Continuous f := (Completion.continuous_coe _).comp TensorProduct.continuous_tmul
  let S := Submodule.span ℝ (Set.range f)
  let K := S.topologicalClosure
  have hs : TopologicalSpace.IsSeparable (K : Set (tensor A B).Carrier) :=
    (isSeparable_range hf).span.closure
  have hall (u : (tensor A B).Carrier) : u∈K := by
    refine Completion.induction_on u (Submodule.isClosed_topologicalClosure S) ?_
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      exact Submodule.le_topologicalClosure S (Submodule.subset_span ⟨(x,y),rfl⟩)
    | add t t' ht ht' =>
      simpa only [Completion.coe_add] using K.add_mem ht ht'
  have ht : (K : Set (tensor A B).Carrier)=univ := eq_univ_of_forall hall
  exact isSeparable_univ_iff.mp (ht ▸ hs)

theorem finiteTensor_separable (n : ℕ) (A : Fin n → HilbertDatum)
    (hA : ∀ i, TopologicalSpace.SeparableSpace (A i).Carrier) :
    TopologicalSpace.SeparableSpace (finiteTensor n A).Carrier := by
  induction n with
  | zero => change TopologicalSpace.SeparableSpace ℝ; infer_instance
  | succ n ih =>
    letI := hA 0
    letI := ih (fun i => A i.succ) (fun i => hA i.succ)
    exact tensor_separable (A 0) (finiteTensor n (fun i => A i.succ))

theorem boundedTrees_finite (m n : ℕ) : {t : Tree m | t.height≤n}.Finite := by
  induction n with
  | zero =>
    have he : {t : Tree m | t.height≤0}={Tree.leaf} := by
      ext t
      simp [Tree.height_eq_zero_iff]
    rw [he]
    exact finite_singleton _
  | succ n ih =>
    letI : Fintype {t : Tree m // t.height≤n} := ih.fintype
    let f := fun ts : Fin m → {t : Tree m // t.height≤n} => Tree.graft (fun i => (ts i).val)
    apply ((finite_singleton (Tree.leaf : Tree m)).union (Set.finite_range f)).subset
    intro t ht
    cases t with
    | leaf => exact Or.inl (by simp)
    | graft ts =>
      right
      refine ⟨fun i => ⟨ts i,(Tree.graft_height_le_iff ts n).mp ht i⟩,rfl⟩

theorem tree_countable (m : ℕ) : Countable (Tree m) := by
  have h : (⋃ n : ℕ, {t : Tree m | t.height≤n})=univ := by
    apply eq_univ_of_forall
    intro t
    exact mem_iUnion.mpr ⟨t.height,by change t.height ≤ t.height; exact le_rfl⟩
  exact countable_univ_iff.mp (h ▸ Set.countable_iUnion (fun n => (boundedTrees_finite m n).countable))

theorem fiber_separable {m : ℕ} (t : Tree m) :
    TopologicalSpace.SeparableSpace (fiber t).Carrier := by
  induction t with
  | leaf =>
    change TopologicalSpace.SeparableSpace LeafSpace
    infer_instance
  | graft ts ih =>
    exact finiteTensor_separable m (fun i => fiber (ts i)) ih

theorem lp_separable {ι : Type*} [Countable ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (lp E 2) := by
  let C : Set (lp E 2) := ⋃ i, Set.range (fun x : E i => lp.single 2 i x)
  have hc : TopologicalSpace.IsSeparable C := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro i
    exact isSeparable_range ((lp.isometry_single (p:=2) i).continuous)
  let S := Submodule.span ℝ C
  let K := S.topologicalClosure
  have hs : TopologicalSpace.IsSeparable (K : Set (lp E 2)) := hc.span.closure
  have hall (f : lp E 2) : f∈K := by
    apply (Submodule.isClosed_topologicalClosure S).mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠∞) f)
    apply Eventually.of_forall
    intro s
    apply K.sum_mem
    intro i hi
    apply Submodule.le_topologicalClosure S
    exact Submodule.subset_span (mem_iUnion.mpr ⟨i,⟨f i,rfl⟩⟩)
  have ht : (K : Set (lp E 2))=univ := eq_univ_of_forall hall
  exact isSeparable_univ_iff.mp (ht ▸ hs)

theorem space_separable (m : ℕ) : TopologicalSpace.SeparableSpace (Space m) := by
  letI := tree_countable m
  letI := fun t : Tree m => fiber_separable t
  exact lp_separable (fun t : Tree m => (fiber t).Carrier)

end SphericalAging.TreeHilbertSeparable
