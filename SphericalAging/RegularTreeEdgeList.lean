module

public import SphericalAging.GreedyForkSpanStep
public import SphericalAging.RegularTreeGlobalToLocal
public import SphericalAging.RegularTreeHighEnergyPruning

public section

/-! Literal normalized edge lists and their exact finite sizes. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreeEdgeList
open FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal
open GreedyForkSpanStep ApproximateForkProjectionSelection
open RegularTreeHighEnergyPruning
variable {N K k t : ℕ}

@[expose] def edgeCount (K : ℕ) : ℕ→ℕ
  | 0 => 0
  | d+1 => K+K*edgeCount K d

@[expose] def edges : (d : ℕ)→TreeData (Vector N) K d→List (Vector N)
  | 0,_ => []
  | d+1,z => incrementList z.1 (fun i => root d (z.2 i))++
      (List.ofFn (fun i => edges d (z.2 i))).flatten

@[expose] def forestEdges (d : ℕ) (z : Fin t→TreeData (Vector N) K d) : List (Vector N) :=
  (List.ofFn (fun i => edges d (z i))).flatten

theorem edges_length (d : ℕ) (z : TreeData (Vector N) K d) :
    (edges d z).length=edgeCount K d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [edges,List.length_append,List.length_flatten]
    simp only [incrementList,List.length_ofFn,List.map_ofFn]
    change K+(List.ofFn (fun i : Fin K => (edges d (z.2 i)).length)).sum=edgeCount K (d+1)
    simp_rw [ih]
    rw [List.ofFn_const]
    simp [edgeCount]

theorem forestEdges_length (d : ℕ) (z : Fin t→TreeData (Vector N) K d) :
    (forestEdges d z).length=t*edgeCount K d := by
  rw [forestEdges,List.length_flatten]
  rw [List.map_ofFn]
  change (List.ofFn (fun i : Fin t => (edges d (z i)).length)).sum=t*edgeCount K d
  simp_rw [edges_length]
  rw [List.ofFn_const]
  simp

theorem forestEdges_zero (d : ℕ) (z : Fin 0→TreeData (Vector N) K d) :
    forestEdges d z=[] := by simp [forestEdges]

theorem forestEdges_cons (d : ℕ) (z : TreeData (Vector N) K d)
    (zs : Fin t→TreeData (Vector N) K d) :
    forestEdges d (Fin.cons z zs)=edges d z++forestEdges d zs := by
  unfold forestEdges
  have heq : (fun i : Fin (t+1) => edges (K := K) d (Fin.cons (α := fun _ : Fin (t+1) => TreeData (Vector N) K d) z zs i))=Fin.cons (edges d z) (fun i : Fin t => edges d (zs i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [heq,List.ofFn_cons,List.flatten_cons]

theorem local_root_ball (q : ℕ→ℝ) (η : ℝ) (d : ℕ)
    (z : TreeData (Vector N) K d) (hz : LocalOverlapTree q η d z) :
    ‖root d z‖≤Real.sqrt N := by cases d <;> exact hz.1

theorem local_prune (q : ℕ→ℝ) (η : ℝ) (d : ℕ)
    (σ : Selection K k d) (z : TreeData (Vector N) K d)
    (hz : LocalOverlapTree q η d z) : LocalOverlapTree q η d (prune d σ z) := by
  induction d generalizing q with
  | zero => exact hz
  | succ d ih =>
    obtain ⟨hb,hs,hp,hc,hch⟩ := hz
    simp only [prune,LocalOverlapTree]
    refine ⟨hb,hs,?_,?_,?_⟩
    · intro i
      simpa only [root_prune] using hp (σ.1 i)
    · intro i j hij
      simpa only [root_prune] using hc (σ.1 i) (σ.1 j) (fun h => hij (σ.1.injective h))
    · intro i
      exact ih (fun l => q (l+1)) (σ.2 i) (z.2 (σ.1 i)) (hch (σ.1 i))

end SphericalAging.RegularTreeEdgeList
