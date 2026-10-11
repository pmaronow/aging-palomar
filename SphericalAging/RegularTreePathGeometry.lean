module

public import SphericalAging.RegularTreeGlobalToLocal
public import SphericalAging.ApproximateForkProjectionSelection

public section

/-! Actual root-to-leaf normalized increments and shared-prefix geometry
on the literal finite tree, prior to any coherence estimates. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreePathGeometry
open FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal
open ApproximateForkProjectionSelection
open scoped BigOperators
variable {N K : ℕ}

@[expose] def normalizedVertex (x : Vector N) : Vector N := (Real.sqrt N)⁻¹ • x

@[expose] def pathEdges : (d : ℕ)→TreeData (Vector N) K d→(Fin d→Fin K)→List (Vector N)
  | 0,_,_ => []
  | d+1,z,a => normalizedIncrement z.1 (root d (z.2 (a 0)))::
      pathEdges d (z.2 (a 0)) (fun i => a i.succ)

@[expose] def pathNode : (d : ℕ)→TreeData (Vector N) K d→(Fin d→Fin K)→ℕ→Vector N
  | d,z,_,0 => root d z
  | 0,z,_,_+1 => z
  | d+1,z,a,l+1 => pathNode d (z.2 (a 0)) (fun i => a i.succ) l

theorem normalizedIncrement_eq (x y : Vector N) :
    normalizedIncrement x y=normalizedVertex y-normalizedVertex x := by
  simp only [normalizedIncrement,normalizedVertex,smul_sub]

theorem pathEdges_length (d : ℕ) (z : TreeData (Vector N) K d) (a : Fin d→Fin K) :
    (pathEdges d z a).length=d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [pathEdges,List.length_cons,ih]

theorem pathNode_depth (d : ℕ) (z : TreeData (Vector N) K d) (a : Fin d→Fin K) :
    pathNode d z a d=leafAt d z a := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih (z.2 (a 0)) (fun i => a i.succ)

theorem path_telescope (d : ℕ) (z : TreeData (Vector N) K d) (a : Fin d→Fin K) :
    normalizedVertex (leafAt d z a)=normalizedVertex (root d z)+(pathEdges d z a).sum := by
  induction d with
  | zero => simp [leafAt,root,pathEdges]
  | succ d ih =>
    rw [leafAt,ih]
    simp only [root,pathEdges,List.sum_cons,normalizedIncrement_eq]
    abel

theorem shared_prefix_nodes (d : ℕ) (z : TreeData (Vector N) K d)
    (a b : Fin d→Fin K) (l : ℕ) (hl : l≤d)
    (hab : ∀i : Fin d,i.val<l→a i=b i) : pathNode d z a l=pathNode d z b l := by
  induction d generalizing l with
  | zero =>
    have h : l=0 := by omega
    subst l
    rfl
  | succ d ih =>
    cases l with
    | zero => rfl
    | succ l =>
      have h0 : a 0=b 0 := hab 0 (by simp)
      simp only [pathNode,h0]
      apply ih _ _ _ l (by omega)
      intro i hi
      exact hab i.succ (by simp only [Fin.val_succ];omega)

theorem shared_prefix_edges (d : ℕ) (z : TreeData (Vector N) K d)
    (a b : Fin d→Fin K) (l : ℕ) (hl : l≤d)
    (hab : ∀i : Fin d,i.val<l→a i=b i) :
    (pathEdges d z a).take l=(pathEdges d z b).take l := by
  induction d generalizing l with
  | zero =>
    have h : l=0 := by omega
    subst l
    rfl
  | succ d ih =>
    cases l with
    | zero => simp
    | succ l =>
      have h0 : a 0=b 0 := hab 0 (by simp)
      simp only [pathEdges,List.take_succ_cons,h0]
      congr 1
      apply ih _ _ _ l (by omega)
      intro i hi
      exact hab i.succ (by simp only [Fin.val_succ];omega)

theorem suffix_telescope (d : ℕ) (z : TreeData (Vector N) K d)
    (a : Fin d→Fin K) (l : ℕ) (hl : l≤d) :
    normalizedVertex (leafAt d z a)=normalizedVertex (pathNode d z a l)+((pathEdges d z a).drop l).sum := by
  induction d generalizing l with
  | zero =>
    have h : l=0 := by omega
    subst l
    simp [leafAt,pathNode,pathEdges,root]
  | succ d ih =>
    cases l with
    | zero => simpa only [pathNode,List.drop_zero] using path_telescope (d+1) z a
    | succ l =>
      simpa only [leafAt,pathNode,pathEdges,List.drop_succ_cons] using
        ih (z.2 (a 0)) (fun i => a i.succ) l (by omega)

theorem first_divergence {d : ℕ} (a b : Fin d→Fin K) (hab : a≠b) :
    ∃j : Fin d,a j≠b j ∧ ∀i : Fin d,i<j→a i=b i := by
  classical
  let S := Finset.univ.filter (fun i : Fin d => a i≠b i)
  have hS : S.Nonempty := by
    by_contra hn
    apply hab
    funext i
    by_contra hi
    exact hn ⟨i,by simp [S,hi]⟩
  let j := S.min' hS
  refine ⟨j,(Finset.mem_filter.mp (Finset.min'_mem S hS)).2,?_⟩
  intro i hi
  by_contra hne
  have hm : i∈S := by simp [S,hne]
  have hj : j ≤ i := Finset.min'_le S i hm
  exact not_lt_of_ge hj hi

theorem leaf_pair_shared_prefix_decomposition {d : ℕ} (z : TreeData (Vector N) K d)
    (a b : Fin d→Fin K) (hab : a≠b) :
    ∃j : Fin d,a j≠b j ∧
      (pathEdges d z a).take j.val=(pathEdges d z b).take j.val ∧
      normalizedVertex (leafAt d z a)=normalizedVertex (pathNode d z a j.val)+
        ((pathEdges d z a).drop j.val).sum ∧
      normalizedVertex (leafAt d z b)=normalizedVertex (pathNode d z a j.val)+
        ((pathEdges d z b).drop j.val).sum := by
  obtain ⟨j,hj,hbefore⟩ := first_divergence a b hab
  have hh : ∀i : Fin d,i.val<j.val→a i=b i := fun i hi => hbefore i hi
  have he := shared_prefix_nodes d z a b j.val j.isLt.le hh
  refine ⟨j,hj,shared_prefix_edges d z a b j.val j.isLt.le hh,
    suffix_telescope d z a j.val j.isLt.le,?_⟩
  rw [he]
  exact suffix_telescope d z b j.val j.isLt.le

end SphericalAging.RegularTreePathGeometry
