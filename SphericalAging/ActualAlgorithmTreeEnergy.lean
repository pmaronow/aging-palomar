module

public import SphericalAging.ActualAlgorithmTree
public import SphericalAging.HamiltonianTreeFieldBand
public import SphericalAging.ExternalFieldUniformCost

public section

/-! Actual field-energy success gives the literal branching algorithm tree
an actual leaf-mean energy lower bound, under the genuine tree Gaussian law. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualAlgorithmTreeEnergy
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure SphereGibbsEntropy
open ActualAlgorithmTree IndependentBranchingSuccess IndependentBranchingSuccessEvent GaussianBranchingSuccess
open RegularTreeEnergyTelescoping HamiltonianTreeEnergy HamiltonianTreeFieldBand
open PartialVarianceBranchingCoefficients HamiltonianBranchingNodeLaw
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def fieldSuccess (A : TensorSpace N p→Vector N) (h : Vector N) (E : ℝ) : Set (TensorSpace N p) :=
  {s | E≤Hamiltonian N p (tensorDecode s) (A s)/(N:ℝ)+⟪h,A s⟫_ℝ/(N:ℝ)}

theorem fieldSuccess_measurable (A : TensorSpace N p→Vector N) (hA : Measurable A)
    (h : Vector N) (E : ℝ) : MeasurableSet (fieldSuccess A h E) := by
  have hf : Measurable (fun s : TensorSpace N p => Hamiltonian N p (tensorDecode s) (A s)/(N:ℝ)+⟪h,A s⟫_ℝ/(N:ℝ)) :=
    (((Hamiltonian_joint_continuous N p).measurable.comp (tensorDecode.continuous.measurable.prodMk hA)).div_const _).add
      ((((continuous_const.inner continuous_id).measurable).comp hA).div_const _)
  exact measurableSet_le measurable_const hf

theorem totalLeafEnergy_succ (V : ℕ→ℝ) (d : ℕ) (h : Vector N)
    (c : TreeData (Vector N) K (d+1)) (s : TensorSpace N p)
    (z : TreeSample (TensorSpace N p) K (d+1)) :
    totalLeafEnergy V (d+1) h c (s,z)=
      (∑i,totalLeafEnergy V d h (c.2 i)
        (update (parentCoefficient V) (freshCoefficient V) d s (z i).1,(z i).2))/(K:ℝ) := by
  simp only [totalLeafEnergy,energyTree,leafMean,map]
  rw [Finset.sum_add_distrib,add_div]
  congr 1
  rw [←Finset.sum_div]
  ring

theorem actual_success_energy_lower (hK : 0<K) (V : ℕ→ℝ) (hV0 : V 0=1)
    (A : TensorSpace N p→Vector N) (h : Vector N) (E : ℝ) (d : ℕ)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈event K (update (parentCoefficient V) (freshCoefficient V)) (fieldSuccess A h E) d) :
    E≤totalLeafEnergy V d h (outputTree A (update (parentCoefficient V) (freshCoefficient V)) d s z) (s,z) := by
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  induction d generalizing s with
  | zero =>
    simpa only [totalLeafEnergy,energyTree,leafMean,map,outputTree,partialDisorder,hV0,
      Real.sqrt_one,one_smul,event,fieldSuccess,mem_setOf_eq] using hz
  | succ d ih =>
    rw [totalLeafEnergy_succ]
    change E≤(∑i,totalLeafEnergy V d h
      (outputTree A (update (parentCoefficient V) (freshCoefficient V)) d
        (update (parentCoefficient V) (freshCoefficient V) d s (z i).1) (z i).2)
      (update (parentCoefficient V) (freshCoefficient V) d s (z i).1,(z i).2))/(K:ℝ)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ih _ _ (hz i))
    have hc : (∑_i : Fin K,E)=(K:ℝ)*E := by simp [mul_comm]
    rw [hc] at hh
    exact (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hh)

theorem actual_algorithm_high_energy_tree (hK : 0<K) (V : ℕ→ℝ)
    (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j) (hV0 : V 0=1)
    (A : TensorSpace N p→Vector N) (hA : Measurable A) (h : Vector N) (E : ℝ) (d : ℕ) :
    let B := fieldSuccess A h E
    let Z := event K (update (parentCoefficient V) (freshCoefficient V)) B d
    MeasurableSet Z ∧ ((stdGaussian (TensorSpace N p)).real B)^(K^d)≤
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real Z ∧
    ∀z∈Z,E≤totalLeafEnergy V d h
      (outputTree A (update (parentCoefficient V) (freshCoefficient V)) d z.1 z.2) z := by
  have hB := fieldSuccess_measurable A hA h E
  refine ⟨event_measurable K _ (update_measurable _ _) _ hB d,?_,?_⟩
  · exact actual_gaussian_tree_success_lower K _ _ (coefficients_unit V hV hVm) _ hB d
  · intro z hz;exact actual_success_energy_lower hK V hV0 A h E d z.1 z.2 hz

end SphericalAging.ActualAlgorithmTreeEnergy
