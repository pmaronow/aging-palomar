module

public import SphericalAging.BranchingNodeLaw
public import SphericalAging.HamiltonianForkNodeEnergy
public import SphericalAging.GaussianBranchingSuccess

public section

/-! Actual independent-disorder fork marginals inside the correlated
Hamiltonian tree. The local uniform fork event therefore has the proved
probability at every fixed node, including nodes with shared ancestors. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianBranchingNodeLaw
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open BranchingNodeLaw IndependentBranchingSuccess GaussianForkUniformEvents
open GaussianOrthogonalForkCovariance OrthogonalGaussianDisclosure
open scoped BigOperators
variable {N p K : ℕ}

@[expose] def tensorDecode : TensorSpace N p≃L[ℝ]Disorder N p :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)

theorem tensorDecode_measurePreserving :
    MeasurePreserving (tensorDecode (N:=N) (p:=p)) (stdGaussian (TensorSpace N p)) (disorderLaw N p) := by
  refine ⟨tensorDecode.continuous.measurable,?_⟩
  rw [←(ordered_tensor_hasLaw N p).map_eq,Measure.map_map tensorDecode.continuous.measurable
    (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable]
  change (disorderLaw N p).map id=disorderLaw N p
  exact Measure.map_id

@[expose] def forkDecode (z : Option (Fin K)→TensorSpace N p) : ForkDisorder N p K :=
  fun i => tensorDecode (z i)

theorem forkDecode_measurePreserving :
    MeasurePreserving (forkDecode (N:=N) (p:=p) (K:=K))
      (Measure.pi (fun _ : Option (Fin K) => stdGaussian (TensorSpace N p))) (forkLaw N p K) := by
  refine ⟨Measurable.of_eval (fun i => tensorDecode.continuous.measurable.comp (measurable_pi_apply i)),?_⟩
  unfold forkDecode
  rw [Measure.pi_map_pi (fun _ => (tensorDecode_measurePreserving (N:=N) (p:=p)).aemeasurable)]
  simp only [(tensorDecode_measurePreserving (N:=N) (p:=p)).map_eq]
  rfl

@[expose] def localFork (a b : ℕ→ℝ) (m l : ℕ) (w : Address K l)
    (z : TensorSpace N p×TreeSample (TensorSpace N p) K (m+1+l)) : ForkDisorder N p K :=
  forkDecode (optionBlock (nodeBlock (GaussianBranchingSuccess.update a b) m l w z))

theorem localFork_measurePreserving (a b : ℕ→ℝ) (hunit : ∀j,(a j)^2+(b j)^2=1)
    (m l : ℕ) (w : Address K l) :
    MeasurePreserving (localFork (N:=N) (p:=p) a b m l w)
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K (m+1+l)))
      (forkLaw N p K) :=
  forkDecode_measurePreserving.comp ((optionBlock_measurePreserving _ K).comp
    (nodeBlock_measurePreserving _ _ (GaussianBranchingSuccess.update a b)
      (fun j => GaussianLinearMixtureLaw.mixture_measurePreserving (a j) (b j) (hunit j)) m l w))

theorem actual_node_uniform_fork_success_probability (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b : ℕ→ℝ) (hunit : ∀j,(a j)^2+(b j)^2=1) (m l : ℕ) (w : Address K l)
    (v v' δ r q ε : ℝ) (hv : 0≤v) (hvv' : v≤v') (hv' : v'≤1)
    (hδ : 0<δ) (hδr : δ≤r) (hrq : r≤q) (hq1 : q≤1) (hε : 0<ε) :
    1-2*(1+2/GaussianForkUniformConcentration.mesh p δ ε)^N*
      Real.exp (-((K:ℝ)*N)*ε^2/(8*(Real.pi/2)^2))-((K:ℝ)+1)*Real.exp (-(N:ℝ))≤
      ((stdGaussian (TensorSpace N p)).prod
        (treeLaw (stdGaussian (TensorSpace N p)) K (m+1+l))).real
        {z | localFork a b m l w z∈goodEvent N p K v v' r q ε} := by
  have hmeas := (goodEvent_isClosed hp hK hKN v v' r q ε hv hvv' hv'
    (hδ.le.trans hδr) hrq hq1).measurableSet
  have heq := (localFork_measurePreserving a b hunit m l w).hasLaw.measureReal_eq hmeas
  change ((stdGaussian (TensorSpace N p)).prod
    (treeLaw (stdGaussian (TensorSpace N p)) K (m+1+l))).real
      {z | localFork a b m l w z∈goodEvent N p K v v' r q ε}=
      (forkLaw N p K).real (goodEvent N p K v v' r q ε) at heq
  rw [heq]
  exact actual_uniform_fork_success_probability hp hK hKN v v' δ r q ε
    hv hvv' hv' hδ hδr hrq hq1 hε

end SphericalAging.HamiltonianBranchingNodeLaw
