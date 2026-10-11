module

public import SphericalAging.ActualPhysicalBrownianPairing

public section

/-! The complete finite-N Brownian force-response lemma from source 3.4:
actual quenched and annealed normalized Brownian pairing identities and
the actual physical finite-N diagonal. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SourceBrownianForceResponse
open HardSphereDynamics ActualSphereTransition ActualPhysicalBrownianPairing
open AnnealedHamiltonianEnergyStein ActualResponseKernel TwoTimeResponseTimeParameter
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- All finite-dimensional printed clauses of source 3.4, for the actual
Hamiltonian SDE and actual physical force-response trace. No pairing,
restart, response identity, regularity, or moment bound is a hypothesis. -/
theorem source3_4 (hN : 2≤N) (hp : 3≤p) (β : ℝ≥0) (H s : ℝ≥0) (hs : s≤H) :
    ((∫ r in (0 : ℝ)..(s : ℝ),annealedPhysicalResponseRow (p := p)
      (by omega : N≠0) β (N+1) (modelRadius_pos N) (modelRadius_sq N) H r.toNNReal)=
      ∫ ω,⟪modelProcess N p β H ω,
        WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω.2)⟫_ℝ/
          (Real.sqrt 2*(N : ℝ)) ∂AnnealedModelLaw.law N p) ∧
    (∀ q : FiniteModel.Disorder N p × State N,OnSphere q.2→
      ((∫ r in (0 : ℝ)..(s : ℝ),physicalResponseRow (by omega : N≠0) β (N+1)
        (modelRadius_pos N) (modelRadius_sq N) H r.toNNReal q)=
        (∫ ω,⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
          (modelRadius_pos N) q H ω,
          WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω)⟫_ℝ ∂VectorBrownian.law N)/
            (Real.sqrt 2*(N : ℝ))) ∧
      physicalResponseRow (by omega : N≠0) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
        H H q=((N : ℝ)-1)/(N : ℝ)) ∧
    annealedPhysicalResponseRow (p := p) (by omega : N≠0) β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) H H=((N : ℝ)-1)/(N : ℝ) := by
  have hNpos : 0<N := by omega
  have hp2 : 2≤p := by omega
  refine ⟨?_,?_,annealedPhysicalResponseRow_diagonal hNpos β H⟩
  · simpa only [WeightedBrownianTheorem.brownianPrimitive,VectorBrownian.coordinate] using
      annealed_brownian_prefix_interval hNpos hp2 β H s hs
  · intro q hq
    refine ⟨quenched_brownian_prefix_interval (Nat.ne_of_gt hNpos) β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) H s hs q hq,?_⟩
    simpa only [physicalResponseRow,min_self,HardSphereDynamics.kappa] using
      quenchedResponse_diagonal (Nat.ne_of_gt hNpos) β (N+1)
        (modelRadius_pos N) (modelRadius_sq N) H q hq

end SphericalAging.SourceBrownianForceResponse
