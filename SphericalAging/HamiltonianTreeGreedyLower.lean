module

public import SphericalAging.HamiltonianTreeEnergy
public import SphericalAging.OrthogonalForkMaximizer
public import SphericalAging.RegularTreeEnergyLowerBound

public section

/-! A genuine recursive maximizing spatial tree. Each fork maximum exists
by compactness, and its energy lower bound follows from the actual
simultaneous Gaussian fork event and exact telescoping. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeGreedyLower
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open BranchingNodeLaw IndependentBranchingSuccess GaussianForkUniformEvents
open GaussianOrthogonalForkCovariance HamiltonianBranchingNodeLaw
open BranchingTreeLocalEvents PartialVarianceBranchingCoefficients
open RegularTreeEnergyTelescoping HamiltonianForkNodeEnergy HamiltonianTreeLocalEvents HamiltonianTreeEnergy
open RegularTreeEnergyLowerBound OrthogonalForkMaximizer
open scoped BigOperators
variable {N p K : ℕ}

@[expose] def Greedy (V Q : ℕ→ℝ) : (d : ℕ)→TreeData (Vector N) K d→TensorSpace N p→
    TreeSample (TensorSpace N p) K d→Prop
  | 0,_,_,_ => True
  | d+1,c,s,z =>
      averagedIncrement (V (d+1)) (V d) c.1 (fun i => root d (c.2 i))
          (forkDecode (optionBlock (s,childNoises d z)))=
        GaussianFixedBaseForkConcentration.supremum (V (d+1)) (V d) (Q (d+1)) (Q d) c.1
          (forkDecode (optionBlock (s,childNoises d z))) ∧
      ∀i,Greedy V Q d (c.2 i)
        (GaussianBranchingSuccess.update (parentCoefficient V) (freshCoefficient V) d s (z i).1) (z i).2

theorem exists_actual_greedy_tree (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (d : ℕ) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*Q d)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d) :
    ∃c : TreeData (Vector N) K d,root d c=x ∧ TreeForkGeometry Q d c ∧ Greedy V Q d c s z := by
  have hN : 0<N := by omega
  induction d generalizing x s with
  | zero => exact ⟨x,rfl,True.intro,True.intro⟩
  | succ d ih =>
    obtain ⟨y,hy,hmax⟩ := actual_fork_maximizer hN hp hK hKN (V (d+1)) (V d)
      (Q (d+1)) (Q d) (hV _).1 (hVm _) (hV _).2 (hQ _).1 (hQm _) (hQ _).2
      x hx (forkDecode (optionBlock (s,childNoises d z)))
    have hi i := ih (y i) (hy.leaf_norm i)
      (GaussianBranchingSuccess.update (parentCoefficient V) (freshCoefficient V) d s (z i).1) (z i).2
    choose c hcroot hcgeom hcgreedy using hi
    refine ⟨(x,c),rfl,?_,?_⟩
    · refine ⟨?_,hcgeom⟩
      simpa only [hcroot] using hy
    · refine ⟨?_,hcgreedy⟩
      simpa only [hcroot] using hmax

theorem actual_greedy_local_lower (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (c : TreeData (Vector N) K d) (hc : TreeForkGeometry Q d c)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d) (hg : Greedy V Q d c s z)
    (hz : (s,z)∈treeEvent V Q ε d) :
    AllLocalLower (fun j => expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j-ε) d
      (energyTree V d c s z) := by
  have hN : 0<N := by omega
  induction d generalizing s with
  | zero => trivial
  | succ d ih =>
    obtain ⟨hc0,hci⟩ := hc
    obtain ⟨hg0,hgi⟩ := hg
    obtain ⟨hz0,hzi⟩ := hz
    refine ⟨?_,fun i => ih _ (hci i) _ _ (hgi i) (hzi i)⟩
    rw [localEdge_eq_actual_fork hN hK V (fun j => (hV j).1) hVm d c s z,hg0]
    have hdev := hz0 c.1 hc0.base_norm
    have hm := GaussianForkBasepointExpectation.expectation_equal_norm hp hK hKN
      (V (d+1)) (V d) (Q (d+1)) (Q d) (hV _).1 (hVm _) (hV _).2
      (hQ _).1 (hQm _) (hQ _).2 c.1 (referenceBase N hN (Q (d+1))) hc0.base_norm
      ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (hc0.base_norm.trans (referenceBase_norm hN _ (hQ _).1).symm))
    rw [hm] at hdev
    have hl := (neg_le_abs _).trans hdev
    change (∫J,GaussianFixedBaseForkConcentration.supremum (V (d+1)) (V d) (Q (d+1)) (Q d)
      (referenceBase N hN (Q (d+1))) J ∂forkLaw N p K)-ε≤_
    linarith

theorem actual_greedy_leaf_energy_lower (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*Q d)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈treeEvent V Q ε d) :
    ∃c : TreeData (Vector N) K d,root d c=x ∧ TreeForkGeometry Q d c ∧
      Hamiltonian N p (partialDisorder V d s) x/(N:ℝ)+
        (∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j)-(d:ℝ)*ε≤
      leafMean d (energyTree V d c s z) := by
  obtain ⟨c,hcx,hc,hg⟩ := exists_actual_greedy_tree hp hK hKN V Q hV hVm hQ hQm d x hx s z
  have hh := leafMean_lower hK _ d _
    (actual_greedy_local_lower hp hK hKN V Q hV hVm hQ hQm ε d c hc s z hg hz)
  rw [energyTree_root,hcx,Finset.sum_sub_distrib] at hh
  refine ⟨c,hcx,hc,?_⟩
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,←add_sub_assoc] using hh

end SphericalAging.HamiltonianTreeGreedyLower
