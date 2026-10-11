module

public import SphericalAging.GaussianTreeStaticPruneLaw
public import SphericalAging.ActualTreeLandscapeEvent
public import SphericalAging.GlobalAlgorithmTreeExactification

public section

/-! Every static subtree retains the literal terminal success and landscape
bounds from the original complete Gaussian tree. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualAlgorithmTreePrunedSuccess
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess IndependentBranchingSuccessEvent GaussianBranchingSuccess
open GaussianTreeStaticPruneLaw RegularTreeHighEnergyPruning RegularTreeEnergyTelescoping
open ActualAlgorithmTree ActualAlgorithmTreeEnergy ActualTreeEnergyPerturbation
open PartialVarianceBranchingCoefficients HamiltonianTreeFieldBand
variable {N p K k : ℕ}

theorem event_prune {E : Type} [MeasurableSpace E]
    (u : ℕ→E→E→E) (B : Set E) (d : ℕ) (σ : Selection K k d)
    (s : E) (z : TreeSample E K d) (hz : (s,z)∈event K u B d) :
    (s,pruneSample d σ z)∈event k u B d := by
  induction d generalizing s with
  | zero => exact hz
  | succ d ih => intro i;exact ih (σ.2 i) _ _ (hz (σ.1 i))

theorem actual_pruned_success_energy (hk : 0<k) (V : ℕ→ℝ) (hV0 : V 0=1)
    (A : TensorSpace N p→Vector N) (h : Vector N) (E : ℝ) (d : ℕ)
    (σ : Selection K k d) (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈event K (update (parentCoefficient V) (freshCoefficient V)) (fieldSuccess A h E) d) :
    E≤totalLeafEnergy V d h
      (prune d σ (outputTree A (update (parentCoefficient V) (freshCoefficient V)) d s z))
      (samplePrune d σ (s,z)) := by
  rw [prune_outputTree]
  exact actual_success_energy_lower hk V hV0 A h E d s (pruneSample d σ z)
    (event_prune _ _ d σ s z hz)

theorem actual_pruned_landscape (V : ℕ→ℝ) (C : ℝ) (d : ℕ) (σ : Selection K k d)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : LeafLandscapeBound V C d s z) :
    LeafLandscapeBound V C d s (pruneSample d σ z) := by
  induction d generalizing s with
  | zero => exact hz
  | succ d ih => intro i;exact ih (σ.2 i) _ _ (hz (σ.1 i))

theorem forkTree_of_reverse (q Q : ℕ→ℝ) (d : ℕ) (z : TreeData (Vector N) k d)
    (hrel : ∀l,l≤d→q l=Q (d-l))
    (hz : RegularTreeCentroidGeometry.ForkTree q d z) :
    HamiltonianTreeEnergy.TreeForkGeometry Q d z := by
  induction d generalizing q with
  | zero => trivial
  | succ d ih =>
    refine ⟨?_,?_⟩
    · simpa only [hrel 0 (by omega),hrel 1 (by omega),Nat.sub_zero,Nat.succ_sub_one] using hz.1
    · intro i
      exact ih (fun l => q (l+1)) (z.2 i)
        (fun l hl => by rw [hrel (l+1) (by omega),Nat.add_sub_add_right]) (hz.2 i)

end SphericalAging.ActualAlgorithmTreePrunedSuccess
