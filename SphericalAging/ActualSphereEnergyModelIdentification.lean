module

public import SphericalAging.ActualSphereEnergyLimitTransfer
public import SphericalAging.ActualSphereDensityResponse
public import SphericalAging.ActualCKEnergyLimit

public section

/-! The actual forward-density energy agrees with the canonical full
model energy. All waiting-law and full-product Fubini inputs are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereEnergyModelIdentification
open FiniteModel HardSphereDynamics SphereInitialLaw ActualSphereTransition
open ActualForwardEnergyMeasurability ActualSphereEnergyLimitTransfer
open ActualSphereDensityResponse ActualSphereMarkovRestart
open AnnealedHamiltonianEnergyStein ActualCKMultiplierResidual
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Literal density energy and literal canonical stochastic-model energy
have the same annealed expectation. -/
theorem annealedEnergy_eq_meanEnergy (hN : 0<N) (hp : 1≤p) (β : ℝ≥0) (H : ℝ≥0) :
    annealedEnergy (N:=N) (p:=p) β (N+1) (modelRadius_pos N) H=meanEnergy N p β H := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let R : ℝ≥0 := N+1
  let hR := modelRadius_pos N
  have he := annealedGlobal_eq_joint (ρ:=AnnealedModelLaw.parameterLaw N p) D β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p) H
  have heH : (fun q : (Disorder N p×State N)×VectorBrownian.Space N =>
      Hamiltonian N p q.1.1 (modelProcess N p β H q))=ᵐ[AnnealedModelLaw.law N p]
      (fun q => Hamiltonian N p q.1.1 (jointProcess D β R hR q.1 H q.2)) :=
    he.mono (fun q hq => congrArg (Hamiltonian N p q.1.1) hq)
  have hi : Integrable (fun q : (Disorder N p×State N)×VectorBrownian.Space N =>
      Hamiltonian N p q.1.1 (jointProcess D β R hR q.1 H q.2)) (AnnealedModelLaw.law N p) :=
    (energy_integrable hN (by omega) (VectorBrownian.driver N) β R hR (modelRadius_sq N) H).congr heH
  calc
    _=(∫J : Disorder N p,(∫x : State N,∫ω : VectorBrownian.Space N,
      Hamiltonian N p J (jointProcess D β R hR (J,x) H ω) ∂VectorBrownian.law N ∂sphereLaw N)/(N:ℝ)
      ∂disorderLaw N p) := by
      unfold annealedEnergy
      apply integral_congr_ae
      exact .of_forall (fun J => by
        change forwardEnergy β R hR J H = _
        rw [forwardEnergy_eq_uniform_initial hN hp β R hR (modelRadius_sq N) J H,
          integral_prod _ (uniformWaiting_continuous_test_integrable hN β R hR (modelRadius_sq N) J H
            (Hamiltonian_contDiff J).continuous)])
    _=(∫q : Disorder N p×State N,∫ω : VectorBrownian.Space N,
      Hamiltonian N p q.1 (jointProcess D β R hR q H ω) ∂VectorBrownian.law N
      ∂AnnealedModelLaw.parameterLaw N p)/(N:ℝ) := by
      rw [integral_div]
      exact congrArg (fun z : ℝ => z/(N:ℝ)) (integral_prod _ hi.integral_prod_left).symm
    _=meanEnergy N p β H := by
      unfold meanEnergy
      rw [integral_congr_ae heH]
      exact congrArg (fun z : ℝ => z/(N:ℝ)) (integral_prod _ hi).symm

end SphericalAging.ActualSphereEnergyModelIdentification
