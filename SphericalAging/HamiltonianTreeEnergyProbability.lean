module

public import SphericalAging.HamiltonianTreeEnergy

public section

/-! Actual finite-N simultaneous tree energy upper estimates. The event,
its measurability and its quantitative probability are constructed, and
the energy inequality holds for every admissible spatial tree on that event. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeEnergyProbability
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open BranchingNodeLaw IndependentBranchingSuccess GaussianForkUniformEvents
open GaussianOrthogonalForkCovariance HamiltonianBranchingNodeLaw
open BranchingTreeLocalEvents PartialVarianceBranchingCoefficients
open RegularTreeEnergyTelescoping HamiltonianForkNodeEnergy HamiltonianTreeLocalEvents HamiltonianTreeEnergy
open scoped BigOperators
variable {N p K : ℕ}

theorem treeEvent_measurable (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ) (d : ℕ) :
    MeasurableSet (treeEvent (N:=N) (p:=p) (K:=K) V Q ε d) := by
  exact AllGood_measurable (stdGaussian (TensorSpace N p)) (stdGaussian (TensorSpace N p))
    (GaussianBranchingSuccess.update (parentCoefficient V) (freshCoefficient V))
    (fun j => GaussianLinearMixtureLaw.mixture_measurePreserving _ _
      (coefficients_unit V (fun j => (hV j).1) hVm j)) (localEvent V Q ε)
    (localEvent_measurable hp hK hKN V Q hV hVm hQ hQm ε) d

theorem actual_zeroRoot_leaf_energy_upper (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (hroot : V d=0) (c : TreeData (Vector N) K d) (hc : TreeForkGeometry Q d c)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈treeEvent V Q ε d) :
    leafMean d (energyTree V d c s z)≤
      ∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j+(d:ℝ)*ε := by
  have hh := actual_leaf_energy_upper_bound hp hK hKN V Q hV hVm hQ hQm ε d c hc s z hz
  have hzero : Hamiltonian N p (partialDisorder V d s) (root d c)=0 := by
    simp only [partialDisorder,hroot,Real.sqrt_zero,Hamiltonian_disorder_smul,zero_mul]
  rw [hzero,zero_div,zero_add,Finset.sum_add_distrib] at hh
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh

theorem actual_tree_energy_upper_event (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (δ : ℝ) (hδ : 0<δ) (hQ : ∀j,δ≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (ε : ℝ) (hε : 0<ε) (d : ℕ) (hroot : V d=0) :
    ∃E : Set (TensorSpace N p×TreeSample (TensorSpace N p) K d),MeasurableSet E ∧
      1-failureBudget K (fun _ => localFailure N p K δ ε) d≤
        ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real E ∧
      ∀z∈E,∀c : TreeData (Vector N) K d,TreeForkGeometry Q d c→
        leafMean d (energyTree V d c z.1 z.2)≤
          ∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j+(d:ℝ)*ε := by
  refine ⟨treeEvent V Q ε d,treeEvent_measurable hp hK hKN V Q hV hVm
    (fun j => ⟨hδ.le.trans (hQ j).1,(hQ j).2⟩) hQm ε d,
    actual_simultaneous_tree_success_probability hp hK hKN V Q hV hVm δ hδ hQ hQm ε hε d,?_⟩
  intro z hz c hc
  exact actual_zeroRoot_leaf_energy_upper hp hK hKN V Q hV hVm
    (fun j => ⟨hδ.le.trans (hQ j).1,(hQ j).2⟩) hQm ε d hroot c hc z.1 z.2 hz

end SphericalAging.HamiltonianTreeEnergyProbability
