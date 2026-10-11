module

public import SphericalAging.HamiltonianTreeLocalEvents
public import SphericalAging.GaussianForkBasepointExpectation

public section

/-! Literal partial-variance Hamiltonian energies on a correlated Gaussian
tree. The local edges and complete leaf-energy telescope are identified
with the actual orthogonal fork increments. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeEnergy
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open BranchingNodeLaw IndependentBranchingSuccess GaussianForkUniformEvents
open GaussianOrthogonalForkCovariance HamiltonianBranchingNodeLaw
open BranchingTreeLocalEvents PartialVarianceBranchingCoefficients
open RegularTreeEnergyTelescoping HamiltonianForkNodeEnergy HamiltonianTreeLocalEvents
open scoped BigOperators
variable {N p K : ℕ}

@[expose] def partialDisorder (V : ℕ→ℝ) (d : ℕ) (s : TensorSpace N p) : Disorder N p :=
  Real.sqrt (V d)•tensorDecode s

theorem partialDisorder_update (V : ℕ→ℝ) (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j)
    (d : ℕ) (s g : TensorSpace N p) :
    partialDisorder V d (GaussianBranchingSuccess.update (parentCoefficient V) (freshCoefficient V) d s g)=
      Real.sqrt (V (d+1))•tensorDecode s+Real.sqrt (V d-V (d+1))•tensorDecode g := by
  change Real.sqrt (V d)•tensorDecode
    (parentRatio (V (d+1)) (V d)•s+freshRatio (V (d+1)) (V d)•g)=_
  rw [←map_smul,actual_scaled_update _ _ (hV _) (hVm _) s g,map_add,map_smul,map_smul]

@[expose] def energyTree (V : ℕ→ℝ) : (d : ℕ)→TreeData (Vector N) K d→TensorSpace N p→
    TreeSample (TensorSpace N p) K d→TreeData ℝ K d
  | 0,c,s,_ => Hamiltonian N p (partialDisorder V 0 s) c/(N:ℝ)
  | d+1,c,s,z => (Hamiltonian N p (partialDisorder V (d+1) s) c.1/(N:ℝ),
      fun i => energyTree V d (c.2 i)
        (GaussianBranchingSuccess.update (parentCoefficient V) (freshCoefficient V) d s (z i).1) (z i).2)

theorem energyTree_root (V : ℕ→ℝ) (d : ℕ) (c : TreeData (Vector N) K d)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d) :
    root d (energyTree V d c s z)=Hamiltonian N p (partialDisorder V d s) (root d c)/(N:ℝ) := by
  cases d <;> rfl

theorem localEdge_eq_actual_fork (hN : 0<N) (hK : 0<K) (V : ℕ→ℝ)
    (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j) (d : ℕ)
    (c : TreeData (Vector N) K (d+1)) (s : TensorSpace N p)
    (z : TreeSample (TensorSpace N p) K (d+1)) :
    localEdge (d+1) (energyTree V (d+1) c s z)=
      averagedIncrement (V (d+1)) (V d) c.1 (fun i => root d (c.2 i))
        (forkDecode (optionBlock (s,childNoises d z))) := by
  simp only [energyTree,localEdge,energyTree_root]
  simp_rw [partialDisorder_update V hV hVm]
  have heq := node_localEdge_eq_actual_increment hN hK (V (d+1)) (V d) c.1
    (fun i => root d (c.2 i)) (forkDecode (optionBlock (s,childNoises d z)))
  exact heq

@[expose] def TreeForkGeometry (Q : ℕ→ℝ) : (d : ℕ)→TreeData (Vector N) K d→Prop
  | 0,_ => True
  | d+1,c => OrthogonalFork c.1 (fun i => root d (c.2 i)) (Q (d+1)) (Q d) ∧
      ∀i,TreeForkGeometry Q d (c.2 i)

@[expose] def referenceBase (N : ℕ) (hN : 0<N) (r : ℝ) : Vector N :=
  Real.sqrt ((N:ℝ)*r)•EuclideanSpace.basisFun (Fin N) ℝ ⟨0,hN⟩

theorem referenceBase_norm (hN : 0<N) (r : ℝ) (hr : 0≤r) :
    ‖referenceBase N hN r‖^2=(N:ℝ)*r := by
  simp only [referenceBase,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    (EuclideanSpace.basisFun (Fin N) ℝ).norm_eq_one,mul_one]
  exact Real.sq_sqrt (by positivity)

@[expose] def expectedEdge (hN : 0<N) (V Q : ℕ→ℝ) (d : ℕ) : ℝ :=
  ∫J,GaussianFixedBaseForkConcentration.supremum (V (d+1)) (V d) (Q (d+1)) (Q d)
    (referenceBase N hN (Q (d+1))) J ∂forkLaw N p K

theorem actual_tree_local_bounds (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (c : TreeData (Vector N) K d) (hc : TreeForkGeometry Q d c)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈treeEvent V Q ε d) :
    AllLocalBounds (fun j => expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j+ε) d
      (energyTree V d c s z) := by
  have hN : 0<N := by omega
  induction d generalizing s with
  | zero => trivial
  | succ d ih =>
    obtain ⟨hc0,hci⟩ := hc
    obtain ⟨hz0,hzi⟩ := hz
    refine ⟨?_,fun i => ih _ (hci i) _ _ (hzi i)⟩
    have hh := actual_node_energy_upper_on_goodEvent hp hK hKN (V (d+1)) (V d)
      (Q (d+1)) (Q d) ε (hV _).1 (hVm _) (hV _).2 (hQ _).1 (hQm _) (hQ _).2
      c.1 (fun i => root d (c.2 i)) hc0 (forkDecode (optionBlock (s,childNoises d z))) hz0
    have hm := GaussianForkBasepointExpectation.expectation_equal_norm hp hK hKN
      (V (d+1)) (V d) (Q (d+1)) (Q d) (hV _).1 (hVm _) (hV _).2
      (hQ _).1 (hQm _) (hQ _).2 c.1 (referenceBase N hN (Q (d+1))) hc0.base_norm
      ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (hc0.base_norm.trans (referenceBase_norm hN _ (hQ _).1).symm))
    rw [hm] at hh
    rw [localEdge_eq_actual_fork hN hK V (fun j => (hV j).1) hVm d c s z]
    rw [node_localEdge_eq_actual_increment hN hK] at hh
    exact hh

theorem actual_leaf_energy_upper_bound (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (c : TreeData (Vector N) K d) (hc : TreeForkGeometry Q d c)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈treeEvent V Q ε d) :
    leafMean d (energyTree V d c s z)≤
      Hamiltonian N p (partialDisorder V d s) (root d c)/(N:ℝ)+
        ∑j∈Finset.range d,(expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j+ε) := by
  have hh := leafMean_upper_bound hK _ d _
    (actual_tree_local_bounds hp hK hKN V Q hV hVm hQ hQm ε d c hc s z hz)
  rwa [energyTree_root] at hh

end SphericalAging.HamiltonianTreeEnergy
