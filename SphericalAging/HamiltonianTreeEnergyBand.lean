module

public import SphericalAging.HamiltonianTreeGreedyLower
public import SphericalAging.HamiltonianTreeEnergyProbability

public section

/-! The actual two-sided finite-tree energy band, the Hamiltonian part of
Huang--Sellke Proposition 3.3 in the ordered pure-p model. Both the common
event and the lower-bound configuration are constructed internally. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeEnergyBand
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess RegularTreeEnergyTelescoping BranchingTreeLocalEvents
open HamiltonianTreeLocalEvents HamiltonianTreeEnergy HamiltonianTreeGreedyLower
open HamiltonianTreeEnergyProbability HamiltonianForkNodeEnergy
open scoped BigOperators
variable {N p K : ℕ}

theorem actual_zeroRoot_leaf_energy_lower (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (hroot : V d=0) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*Q d)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈treeEvent V Q ε d) :
    ∃c : TreeData (Vector N) K d,root d c=x ∧ TreeForkGeometry Q d c ∧
      (∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j)-(d:ℝ)*ε≤
        leafMean d (energyTree V d c s z) := by
  obtain ⟨c,hcx,hc,hb⟩ := actual_greedy_leaf_energy_lower hp hK hKN V Q hV hVm hQ hQm ε d x hx s z hz
  have hzero : Hamiltonian N p (partialDisorder V d s) x=0 := by
    simp only [partialDisorder,hroot,Real.sqrt_zero,Hamiltonian_disorder_smul,zero_mul]
  exact ⟨c,hcx,hc,by simpa only [hzero,zero_div,zero_add] using hb⟩

theorem actual_finite_tree_energy_band (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (δ : ℝ) (hδ : 0<δ) (hQ : ∀j,δ≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (ε : ℝ) (hε : 0<ε) (d : ℕ) (hroot : V d=0) :
    ∃E : Set (TensorSpace N p×TreeSample (TensorSpace N p) K d),MeasurableSet E ∧
      1-failureBudget K (fun _ => localFailure N p K δ ε) d≤
        ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real E ∧
      ∀z∈E,
        (∀c : TreeData (Vector N) K d,TreeForkGeometry Q d c→
          leafMean d (energyTree V d c z.1 z.2)≤
            (∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j)+(d:ℝ)*ε) ∧
        (∀x : Vector N,‖x‖^2=(N:ℝ)*Q d→
          ∃c : TreeData (Vector N) K d,root d c=x ∧ TreeForkGeometry Q d c ∧
            (∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j)-(d:ℝ)*ε≤
              leafMean d (energyTree V d c z.1 z.2)) := by
  have hQ0 : ∀j,0≤Q j ∧ Q j≤1 := fun j => ⟨hδ.le.trans (hQ j).1,(hQ j).2⟩
  refine ⟨treeEvent V Q ε d,treeEvent_measurable hp hK hKN V Q hV hVm hQ0 hQm ε d,
    actual_simultaneous_tree_success_probability hp hK hKN V Q hV hVm δ hδ hQ hQm ε hε d,?_⟩
  intro z hz
  exact ⟨fun c hc => actual_zeroRoot_leaf_energy_upper hp hK hKN V Q hV hVm hQ0 hQm ε d hroot c hc z.1 z.2 hz,
    fun x hx => actual_zeroRoot_leaf_energy_lower hp hK hKN V Q hV hVm hQ0 hQm ε d hroot x hx z.1 z.2 hz⟩

end SphericalAging.HamiltonianTreeEnergyBand
