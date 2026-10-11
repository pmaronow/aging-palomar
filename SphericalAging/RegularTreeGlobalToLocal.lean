module

public import SphericalAging.CentroidOverlapEstimates

public section

/-! HS Appendix A Lemma A.5 in the single-species model. Starting with
actual globally constrained leaves, construct each internal vertex as the
uniform centroid of its descendant leaves and derive every local constraint. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreeGlobalToLocal
open FiniteModel RegularTreeEnergyTelescoping RegularTreeCentroidGeometry
open OrthogonalForkCentroid CentroidOverlapEstimates
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

@[expose] def AllLeaves (P : Vector N→Prop) : (d : ℕ)→TreeData (Vector N) K d→Prop
  | 0,z => P z
  | d+1,z => ∀i,AllLeaves P d (z.2 i)

@[expose] def CrossLeaves (R : Vector N→Vector N→Prop) :
    (d : ℕ)→TreeData (Vector N) K d→TreeData (Vector N) K d→Prop
  | 0,z,w => R z w
  | d+1,z,w => ∀i j,CrossLeaves R d (z.2 i) (w.2 j)

@[expose] def GlobalOverlapTree (q : ℕ→ℝ) (η : ℝ) :
    (d : ℕ)→TreeData (Vector N) K d→Prop
  | 0,z => ‖(show Vector N from z)‖≤Real.sqrt N ∧ |overlap z z-q 0|≤η
  | d+1,z => (∀i,GlobalOverlapTree (fun l => q (l+1)) η d (z.2 i)) ∧
      ∀i j,i≠j→CrossLeaves (fun x y => |overlap x y-q 0|≤η) d (z.2 i) (z.2 j)

@[expose] def LocalOverlapTree (q : ℕ→ℝ) (η : ℝ) :
    (d : ℕ)→TreeData (Vector N) K d→Prop
  | 0,z => ‖(show Vector N from z)‖≤Real.sqrt N ∧ |overlap z z-q 0|≤η
  | d+1,z => ‖z.1‖≤Real.sqrt N ∧ |overlap z.1 z.1-q 0|≤η ∧
      (∀i,|overlap (root d (z.2 i)) z.1-q 0|≤η) ∧
      (∀i j,i≠j→|overlap (root d (z.2 i)) (root d (z.2 j))-q 0|≤η) ∧
      ∀i,LocalOverlapTree (fun l => q (l+1)) η d (z.2 i)

@[expose] def barycenterTree : (d : ℕ)→TreeData (Vector N) K d→TreeData (Vector N) K d
  | 0,z => z
  | d+1,z => (leafCentroid (d+1) z,fun i => barycenterTree d (z.2 i))

theorem root_barycenterTree (d : ℕ) (z : TreeData (Vector N) K d) :
    root d (barycenterTree d z)=leafCentroid d z := by cases d <;> rfl

@[expose] def leafAt : (d : ℕ)→TreeData (Vector N) K d→(Fin d→Fin K)→Vector N
  | 0,z,_ => z
  | d+1,z,a => leafAt d (z.2 (a 0)) (fun j => a j.succ)

theorem leafAt_barycenterTree (d : ℕ) (z : TreeData (Vector N) K d)
    (a : Fin d→Fin K) : leafAt d (barycenterTree d z) a=leafAt d z a := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih (z.2 (a 0)) (fun j => a j.succ)

theorem global_allLeaves_ball (q : ℕ→ℝ) (η : ℝ) (d : ℕ)
    (z : TreeData (Vector N) K d) (h : GlobalOverlapTree q η d z) :
    AllLeaves (fun x => ‖x‖≤Real.sqrt N) d z := by
  induction d generalizing q with
  | zero => exact h.1
  | succ d ih => intro i; exact ih _ (z.2 i) (h.1 i)

theorem leafCentroid_ball (hK : 0<K) (d : ℕ) (z : TreeData (Vector N) K d)
    (h : AllLeaves (fun x => ‖x‖≤Real.sqrt N) d z) :
    ‖leafCentroid d z‖≤Real.sqrt N := by
  induction d with
  | zero => exact h
  | succ d ih => exact centroid_norm_le hK _ _ (fun i => ih (z.2 i) (h i))

theorem cross_leafCentroids_bound (hK : 0<K) (r η : ℝ) (d : ℕ)
    (z w : TreeData (Vector N) K d)
    (h : CrossLeaves (fun x y => |overlap x y-r|≤η) d z w) :
    |overlap (leafCentroid d z) (leafCentroid d w)-r|≤η := by
  induction d with
  | zero => exact h
  | succ d ih =>
    exact overlap_centroids_bound hK _ _ r η
      (fun i j => ih (z.2 i) (w.2 j) (h i j))

/-- The genuine global-to-local inclusion Q(η) ⊆ Qloc(η+2/K). -/
theorem actual_source_HS_A_5 (hN : 0<N) (hK : 0<K) (q : ℕ→ℝ)
    (hq : ∀l,q l∈Set.Icc (0:ℝ) 1) (η : ℝ) (hη : 0≤η)
    (d : ℕ) (z : TreeData (Vector N) K d) (h : GlobalOverlapTree q η d z) :
    LocalOverlapTree q (η+2/(K:ℝ)) d (barycenterTree d z) := by
  have he : η≤η+2/(K:ℝ) := by
    have hh : 0≤(2:ℝ)/(K:ℝ) := by positivity
    linarith
  induction d generalizing q with
  | zero => exact ⟨h.1,h.2.trans he⟩
  | succ d ih =>
    have hball (i : Fin K) : ‖leafCentroid d (z.2 i)‖≤Real.sqrt N :=
      leafCentroid_ball hK d _ (global_allLeaves_ball _ η d _ (h.1 i))
    have hcross (i j : Fin K) (hij : i≠j) :
        |overlap (leafCentroid d (z.2 i)) (leafCentroid d (z.2 j))-q 0|≤η :=
      cross_leafCentroids_bound hK (q 0) η d _ _ (h.2 i j hij)
    simp only [barycenterTree,LocalOverlapTree,leafCentroid]
    refine ⟨centroid_norm_le hK _ _ hball,?_,?_,?_,?_⟩
    · exact parent_self_overlap_bound hN hK _ hball (q 0) η (hq 0).1 (hq 0).2 hη hcross
    · intro i
      rw [root_barycenterTree]
      exact child_parent_overlap_bound hN hK _ hball (q 0) η (hq 0).1 (hq 0).2 hη hcross i
    · intro i j hij
      rw [root_barycenterTree,root_barycenterTree]
      exact (hcross i j hij).trans he
    · intro i
      exact ih (fun l => q (l+1)) (fun l => hq (l+1)) (z.2 i) (h.1 i)

end SphericalAging.RegularTreeGlobalToLocal
