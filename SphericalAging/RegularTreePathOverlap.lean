module

public import SphericalAging.RegularTreePathCoherence
public import SphericalAging.FinitePathListExpansion

public section

/-! Literal leaf overlap constraints derived from local tree constraints
and the internally constructible full edge Gram bounds. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreePathOverlap
open FiniteModel CentroidOverlapEstimates RegularTreeEnergyTelescoping RegularTreeGlobalToLocal
open RegularTreePathGeometry RegularTreePathCoherence GreedyForkSpanStep RegularTreeEdgeList
open FinitePathListExpansion
open scoped BigOperators InnerProductSpace List
variable {N K : ℕ}

theorem normalizedVertex_inner (hN : 0<N) (x y : Vector N) :
    ⟪normalizedVertex x,normalizedVertex y⟫_ℝ=overlap x y := by
  have he : (Real.sqrt (N:ℝ))⁻¹*(Real.sqrt (N:ℝ))⁻¹=(N:ℝ)⁻¹ := by
    rw [←mul_inv,←pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]
  simp only [normalizedVertex,real_inner_smul_left,real_inner_smul_right,overlap,div_eq_mul_inv]
  rw [←mul_assoc,he,mul_comm]

theorem prefix_telescope (d : ℕ) (z : TreeData (Vector N) K d)
    (a : Fin d→Fin K) (l : ℕ) (hl : l≤d) :
    normalizedVertex (pathNode d z a l)=normalizedVertex (root d z)+((pathEdges d z a).take l).sum := by
  have ht := path_telescope d z a
  have hs := suffix_telescope d z a l hl
  have hsplit : ((pathEdges d z a).take l).sum+((pathEdges d z a).drop l).sum=(pathEdges d z a).sum := by
    rw [←List.sum_append,List.take_append_drop]
  calc
    _=normalizedVertex (leafAt d z a)-((pathEdges d z a).drop l).sum := by rw [hs];abel
    _=_ := by rw [ht,←hsplit];abel

theorem local_pathNode_self (d : ℕ) (z : TreeData (Vector N) K d)
    (q : ℕ→ℝ) (η : ℝ) (h : LocalOverlapTree q η d z)
    (a : Fin d→Fin K) (l : ℕ) (hl : l≤d) :
    |overlap (pathNode d z a l) (pathNode d z a l)-q l|≤η := by
  induction d generalizing q l with
  | zero =>
    have he : l=0 := by omega
    subst l
    exact h.2
  | succ d ih =>
    cases l with
    | zero => exact h.2.1
    | succ l =>
      exact ih (z.2 (a 0)) (fun m => q (m+1)) (h.2.2.2.2 (a 0))
        (fun i => a i.succ) l (by omega)

theorem local_leaf_ball (d : ℕ) (z : TreeData (Vector N) K d)
    (q : ℕ→ℝ) (η : ℝ) (h : LocalOverlapTree q η d z) (a : Fin d→Fin K) :
    ‖leafAt d z a‖≤Real.sqrt N := by
  induction d generalizing q with
  | zero => exact h.1
  | succ d ih => exact ih (z.2 (a 0)) (fun m => q (m+1)) (h.2.2.2.2 (a 0)) (fun i => a i.succ)

theorem local_leaf_self (d : ℕ) (z : TreeData (Vector N) K d)
    (q : ℕ→ℝ) (η : ℝ) (h : LocalOverlapTree q η d z) (a : Fin d→Fin K) :
    |overlap (leafAt d z a) (leafAt d z a)-q d|≤η := by
  simpa only [pathNode_depth] using local_pathNode_self d z q η h a d le_rfl

theorem actual_leaf_pair_overlap (hN : 0<N) (d : ℕ) (hd : 1≤d)
    (z : TreeData (Vector N) K d) (q : ℕ→ℝ) (η E : ℝ) (hE : 0≤E)
    (hlocal : LocalOverlapTree q η d z)
    (hcoherent : Coherent E (normalizedVertex (root d z)::edges d z))
    (a b : Fin d→Fin K) (j : Fin d) (hab : a j≠b j)
    (hbefore : ∀i : Fin d,i<j→a i=b i) :
    |overlap (leafAt d z a) (leafAt d z b)-q j.val|≤η+5*(d:ℝ)^2*E := by
  let V := pathEdges d z a
  let W := pathEdges d z b
  have htree : Coherent E (edges d z) := (List.pairwise_cons.mp hcoherent).2
  have hva := path_coherent d z a E htree
  have hvb := path_coherent d z b E htree
  have hpre : V.take j.val=W.take j.val :=
    shared_prefix_edges d z a b j.val j.isLt.le (fun i hi => hbefore i hi)
  have hsplitA : Coherent E (V.take j.val++V.drop j.val) := by rwa [List.take_append_drop]
  have hsplitB : Coherent E (W.take j.val++W.drop j.val) := by rwa [List.take_append_drop]
  have hrootA := root_path_cross d z a E hcoherent
  have hrootB := root_path_cross d z b E hcoherent
  have hprefix := prefix_telescope d z a j.val j.isLt.le
  have hprefixSelf : |⟪normalizedVertex (root d z)+(V.take j.val).sum,
      normalizedVertex (root d z)+(V.take j.val).sum⟫_ℝ-q j.val|≤η := by
    rw [←hprefix,normalizedVertex_inner hN]
    exact local_pathNode_self d z q η hlocal a j.val j.isLt.le
  have hbound := list_path_inner_bound (normalizedVertex (root d z)) (V.take j.val)
    (V.drop j.val) (W.drop j.val) (q j.val) η E hE d hd
    (by dsimp [V];simp only [List.length_drop,pathEdges_length];omega)
    (by dsimp [W];simp only [List.length_drop,pathEdges_length];omega)
    (by simp only [List.length_take,pathEdges_length];omega) hprefixSelf
    (fun v hv => hrootA v (List.mem_of_mem_drop hv))
    (fun v hv => hrootB v (List.mem_of_mem_drop hv))
    ((List.pairwise_append.mp hsplitA).2.2)
    (by rw [hpre];exact (List.pairwise_append.mp hsplitB).2.2)
    (suffix_cross_coherent d z a b j hab hbefore E htree)
  have hsumA : normalizedVertex (root d z)+(V.take j.val).sum+(V.drop j.val).sum=
      normalizedVertex (leafAt d z a) := by
    rw [add_assoc,←List.sum_append,List.take_append_drop]
    exact (path_telescope d z a).symm
  have hsumB : normalizedVertex (root d z)+(V.take j.val).sum+(W.drop j.val).sum=
      normalizedVertex (leafAt d z b) := by
    rw [hpre,add_assoc,←List.sum_append,List.take_append_drop]
    exact (path_telescope d z b).symm
  rwa [hsumA,hsumB,normalizedVertex_inner hN] at hbound

end SphericalAging.RegularTreePathOverlap
