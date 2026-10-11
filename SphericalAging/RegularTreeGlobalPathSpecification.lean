module

public import SphericalAging.RegularTreePathOverlap

public section

/-! Exact equivalence between recursive global leaf constraints and the
actual path first-divergence formulation. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreeGlobalPathSpecification
open FiniteModel CentroidOverlapEstimates RegularTreeEnergyTelescoping RegularTreeGlobalToLocal
open RegularTreePathOverlap RegularTreePathGeometry RegularTreePathCoherence GreedyForkSpanStep RegularTreeEdgeList
open scoped InnerProductSpace
variable {N K : ℕ}

theorem crossLeaves_of_paths (d : ℕ) (z w : TreeData (Vector N) K d)
    (R : Vector N→Vector N→Prop)
    (h : ∀a b : Fin d→Fin K,R (leafAt d z a) (leafAt d w b)) : CrossLeaves R d z w := by
  induction d with
  | zero => exact h (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ d ih =>
    intro i j
    exact ih (z.2 i) (w.2 j) (fun a b => h (Fin.cons i a) (Fin.cons j b))

theorem globalOverlapTree_of_paths (d : ℕ) (z : TreeData (Vector N) K d)
    (q : ℕ→ℝ) (η : ℝ)
    (hball : ∀a : Fin d→Fin K,‖leafAt d z a‖≤Real.sqrt N)
    (hself : ∀a : Fin d→Fin K,|overlap (leafAt d z a) (leafAt d z a)-q d|≤η)
    (hcross : ∀a b : Fin d→Fin K,∀j : Fin d,a j≠b j→
      (∀i : Fin d,i<j→a i=b i)→|overlap (leafAt d z a) (leafAt d z b)-q j.val|≤η) :
    GlobalOverlapTree q η d z := by
  induction d generalizing q with
  | zero => exact ⟨hball (fun i => Fin.elim0 i),hself (fun i => Fin.elim0 i)⟩
  | succ d ih =>
    constructor
    · intro k
      apply ih (z.2 k) (fun l => q (l+1))
      · exact fun a => hball (Fin.cons k a)
      · exact fun a => hself (Fin.cons k a)
      · intro a b j hab hbefore
        apply hcross (Fin.cons k a) (Fin.cons k b) j.succ
        · simpa using hab
        · intro i hi
          cases i using Fin.cases with
          | zero => rfl
          | succ i => exact hbefore i (Fin.succ_lt_succ_iff.mp hi)
    · intro i j hij
      apply crossLeaves_of_paths
      intro a b
      exact hcross (Fin.cons i a) (Fin.cons j b) 0 (by simpa using hij)
        (fun l hl => (Fin.not_lt_zero l hl).elim)

theorem actual_local_coherent_global (hN : 0<N) (d : ℕ)
    (z : TreeData (Vector N) K d) (q : ℕ→ℝ) (η E : ℝ) (hE : 0≤E)
    (hlocal : LocalOverlapTree q η d z)
    (hcoherent : Coherent E (normalizedVertex (root d z)::edges d z)) :
    GlobalOverlapTree q (η+5*(d:ℝ)^2*E) d z := by
  apply globalOverlapTree_of_paths
  · exact local_leaf_ball d z q η hlocal
  · intro a
    exact (local_leaf_self d z q η hlocal a).trans (by
      have he : 0≤5*(d:ℝ)^2*E := by positivity
      linarith)
  · intro a b j hab hbefore
    exact actual_leaf_pair_overlap hN d (by have hj:=j.isLt;omega) z q η E hE
      hlocal hcoherent a b j hab hbefore

end SphericalAging.RegularTreeGlobalPathSpecification
