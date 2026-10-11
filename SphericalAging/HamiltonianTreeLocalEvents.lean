module

public import SphericalAging.HamiltonianBranchingNodeLaw
public import SphericalAging.BranchingTreeLocalEvents
public import SphericalAging.PartialVarianceBranchingCoefficients

public section

/-! The actual simultaneous uniform fork concentration event on a finite
Hamiltonian tree. Every local marginal and the weighted tree union bound
are proved from the independent Gaussian tree construction. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeLocalEvents
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open BranchingNodeLaw IndependentBranchingSuccess GaussianForkUniformEvents
open GaussianOrthogonalForkCovariance HamiltonianBranchingNodeLaw
open BranchingTreeLocalEvents PartialVarianceBranchingCoefficients
variable {N p K : ℕ}

@[expose] def localEvent (V Q : ℕ→ℝ) (ε : ℝ) (d : ℕ) :
    Set (TensorSpace N p×(Fin K→TensorSpace N p)) :=
  {z | forkDecode (optionBlock z)∈goodEvent N p K (V (d+1)) (V d) (Q (d+1)) (Q d) ε}

@[expose] def treeEvent (V Q : ℕ→ℝ) (ε : ℝ) (d : ℕ) :
    Set (TensorSpace N p×TreeSample (TensorSpace N p) K d) :=
  AllGood (GaussianBranchingSuccess.update (parentCoefficient V) (freshCoefficient V)) (localEvent V Q ε) d

@[expose] def localFailure (N p K : ℕ) (δ ε : ℝ) : ℝ :=
  2*(1+2/GaussianForkUniformConcentration.mesh p δ ε)^N*
    Real.exp (-((K:ℝ)*N)*ε^2/(8*(Real.pi/2)^2))+((K:ℝ)+1)*Real.exp (-(N:ℝ))

theorem localEvent_measurable (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ) (d : ℕ) :
    MeasurableSet (localEvent (N:=N) (p:=p) (K:=K) V Q ε d) := by
  have hm := forkDecode_measurePreserving.measurable.comp
    (optionBlock_measurePreserving (stdGaussian (TensorSpace N p)) K).measurable
  exact ((goodEvent_isClosed hp hK hKN _ _ _ _ ε (hV _).1 (hVm _) (hV _).2
    (hQ _).1 (hQm _) (hQ _).2).measurableSet).preimage hm

theorem actual_local_failure_bound (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (δ : ℝ) (hδ : 0<δ) (hQ : ∀j,δ≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (ε : ℝ) (hε : 0<ε) (d : ℕ) :
    ((stdGaussian (TensorSpace N p)).prod (Measure.pi (fun _ : Fin K => stdGaussian (TensorSpace N p)))).real
      (localEvent (N:=N) (p:=p) (K:=K) V Q ε d)ᶜ≤localFailure N p K δ ε := by
  have hmeas := (goodEvent_isClosed hp hK hKN (V (d+1)) (V d) (Q (d+1)) (Q d) ε
    (hV (d+1)).1 (hVm d) (hV d).2
    (hδ.le.trans (hQ (d+1)).1) (hQm d) (hQ d).2).measurableSet
  have heq := (forkDecode_measurePreserving.comp
    (optionBlock_measurePreserving (stdGaussian (TensorSpace N p)) K)).hasLaw.measureReal_eq hmeas.compl
  change ((stdGaussian (TensorSpace N p)).prod
    (Measure.pi (fun _ : Fin K => stdGaussian (TensorSpace N p)))).real (localEvent V Q ε d)ᶜ=
    (forkLaw N p K).real (goodEvent N p K (V (d+1)) (V d) (Q (d+1)) (Q d) ε)ᶜ at heq
  rw [heq]
  have hs := actual_uniform_fork_success_probability hp hK hKN (V (d+1)) (V d) δ (Q (d+1)) (Q d) ε
    (hV (d+1)).1 (hVm d) (hV d).2 hδ (hQ (d+1)).1 (hQm d) (hQ d).2 hε
  have hc := measureReal_add_measureReal_compl (μ:=forkLaw N p K) hmeas
  rw [probReal_univ] at hc
  unfold localFailure
  linarith

theorem actual_simultaneous_tree_success_probability (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (δ : ℝ) (hδ : 0<δ) (hQ : ∀j,δ≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (ε : ℝ) (hε : 0<ε) (d : ℕ) :
    1-failureBudget K (fun _ => localFailure N p K δ ε) d≤
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real
        (treeEvent V Q ε d) := by
  have hu j := GaussianLinearMixtureLaw.mixture_measurePreserving (E:=TensorSpace N p)
    (parentCoefficient V j) (freshCoefficient V j)
    (coefficients_unit V (fun j => (hV j).1) hVm j)
  have hb := actual_tree_success_bound (stdGaussian (TensorSpace N p)) (stdGaussian (TensorSpace N p))
    (GaussianBranchingSuccess.update (parentCoefficient V) (freshCoefficient V)) hu
    (localEvent V Q ε)
    (localEvent_measurable hp hK hKN V Q hV hVm (fun j => ⟨hδ.le.trans (hQ j).1,(hQ j).2⟩) hQm ε) d
  have hm := failureBudget_mono (K:=K) _ (fun _ => localFailure N p K δ ε)
    (actual_local_failure_bound hp hK hKN V Q hV hVm δ hδ hQ hQm ε hε) d
  exact (sub_le_sub_left hm 1).trans hb

end SphericalAging.HamiltonianTreeLocalEvents
