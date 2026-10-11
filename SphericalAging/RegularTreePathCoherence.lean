module

public import SphericalAging.RegularTreePathGeometry
public import SphericalAging.RegularTreeEdgeList

public section

/-! Actual path edge lists inherit the constructed full-tree Gram bounds;
edges after a genuine first divergence have the required cross bounds. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreePathCoherence
open FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal
open ApproximateForkProjectionSelection GreedyForkSpanStep RegularTreeEdgeList
open RegularTreePathGeometry
open scoped InnerProductSpace List
variable {N K : ℕ}

theorem child_edges_sublist (d : ℕ) (z : TreeData (Vector N) K (d+1)) (i : Fin K) :
    edges d (z.2 i)<+edges (d+1) z := by
  change edges d (z.2 i)<+incrementList z.1 (fun j => root d (z.2 j))++
    (List.ofFn (fun j => edges d (z.2 j))).flatten
  have hf : edges d (z.2 i)<+(List.ofFn (fun j => edges d (z.2 j))).flatten :=
    List.sublist_flatten_of_mem (List.mem_ofFn.mpr ⟨i,rfl⟩)
  exact hf.trans (List.sublist_append_right _ _)

theorem pathEdges_sublist (d : ℕ) (z : TreeData (Vector N) K d) (a : Fin d→Fin K) :
    pathEdges d z a<+edges d z := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change [normalizedIncrement z.1 (root d (z.2 (a 0)))]++
      pathEdges d (z.2 (a 0)) (fun i => a i.succ)<+
        incrementList z.1 (fun i => root d (z.2 i))++
        (List.ofFn (fun i => edges d (z.2 i))).flatten
    apply List.Sublist.append
    · exact List.singleton_sublist.mpr (List.mem_ofFn.mpr ⟨a 0,rfl⟩)
    · exact (ih (z.2 (a 0)) (fun i => a i.succ)).trans
        (List.sublist_flatten_of_mem (List.mem_ofFn.mpr ⟨a 0,rfl⟩))

theorem path_coherent (d : ℕ) (z : TreeData (Vector N) K d) (a : Fin d→Fin K)
    (E : ℝ) (h : Coherent E (edges d z)) : Coherent E (pathEdges d z a) :=
  List.Pairwise.sublist (pathEdges_sublist d z a) h

theorem root_path_cross (d : ℕ) (z : TreeData (Vector N) K d) (a : Fin d→Fin K)
    (E : ℝ) (h : Coherent E (normalizedVertex (root d z)::edges d z)) :
    ∀v∈pathEdges d z a,|⟪normalizedVertex (root d z),v⟫_ℝ|≤E := by
  have hh := (List.pairwise_cons.mp h).1
  exact fun v hv => hh v ((pathEdges_sublist d z a).subset hv)

theorem child_path_cross (d : ℕ) (z : TreeData (Vector N) K (d+1))
    (a b : Fin (d+1)→Fin K) (hab : a 0≠b 0) (E : ℝ)
    (h : Coherent E (edges (d+1) z)) :
    ∀u∈pathEdges (d+1) z a,∀v∈pathEdges (d+1) z b,|⟪u,v⟫_ℝ|≤E := by
  have hh := List.pairwise_append.mp h
  have hheads := List.pairwise_ofFn.mp hh.1
  have htrees := List.pairwise_ofFn.mp (List.pairwise_flatten.mp hh.2.1).2
  have hheadtail : ∀i : Fin K,∀j : Fin K,∀v∈edges d (z.2 j),
      |⟪normalizedIncrement z.1 (root d (z.2 i)),v⟫_ℝ|≤E := by
    intro i j v hv
    apply hh.2.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩) v
    exact List.mem_flatten.mpr ⟨edges d (z.2 j),List.mem_ofFn.mpr ⟨j,rfl⟩,hv⟩
  have hcross : ∀u∈edges d (z.2 (a 0)),∀v∈edges d (z.2 (b 0)),|⟪u,v⟫_ℝ|≤E := by
    intro u hu v hv
    rcases lt_or_gt_of_ne hab with hlt|hgt
    · exact htrees (i:=a 0) (j:=b 0) hlt u hu v hv
    · rw [real_inner_comm]
      exact htrees (i:=b 0) (j:=a 0) hgt v hv u hu
  have hhead : |⟪normalizedIncrement z.1 (root d (z.2 (a 0))),
      normalizedIncrement z.1 (root d (z.2 (b 0)))⟫_ℝ|≤E := by
    rcases lt_or_gt_of_ne hab with hlt|hgt
    · exact hheads (i:=a 0) (j:=b 0) hlt
    · rw [real_inner_comm]
      exact hheads (i:=b 0) (j:=a 0) hgt
  intro u hu v hv
  simp only [pathEdges,List.mem_cons] at hu hv
  rcases hu with rfl|hu <;> rcases hv with rfl|hv
  · exact hhead
  · exact hheadtail (a 0) (b 0) v ((pathEdges_sublist d _ _).subset hv)
  · rw [real_inner_comm]
    exact hheadtail (b 0) (a 0) u ((pathEdges_sublist d _ _).subset hu)
  · exact hcross u ((pathEdges_sublist d _ _).subset hu) v ((pathEdges_sublist d _ _).subset hv)

theorem suffix_cross_coherent (d : ℕ) (z : TreeData (Vector N) K d)
    (a b : Fin d→Fin K) (j : Fin d) (hab : a j≠b j)
    (hbefore : ∀i : Fin d,i<j→a i=b i) (E : ℝ)
    (h : Coherent E (edges d z)) :
    ∀u∈(pathEdges d z a).drop j.val,∀v∈(pathEdges d z b).drop j.val,|⟪u,v⟫_ℝ|≤E := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    cases j using Fin.cases with
    | zero => simpa only [Fin.val_zero,List.drop_zero] using child_path_cross d z a b hab E h
    | succ i =>
      have h0 : a 0=b 0 := hbefore 0 (by simp)
      have hchild : Coherent E (edges d (z.2 (b 0))) :=
        List.Pairwise.sublist (child_edges_sublist d z (b 0)) h
      simp only [pathEdges,Fin.val_succ,List.drop_succ_cons,h0]
      apply ih (z.2 (b 0)) (fun l => a l.succ) (fun l => b l.succ) i hab _ hchild
      intro l hl
      exact hbefore l.succ (Fin.succ_lt_succ_iff.mpr hl)

end SphericalAging.RegularTreePathCoherence
