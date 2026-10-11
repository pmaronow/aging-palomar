module

public import SphericalAging.ActualQuenchedBrownianPairing
public import SphericalAging.WeightedBrownianTheorem

public section

/-! The literal annealed model Brownian primitive is the background
average of the actual finite-dimensional backward tangent trace integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedBackwardPairing
open HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart
open AnnealedHamiltonianEnergyStein ActualQuenchedBrownianPairing
open WienerPairingFunctional WienerVectorGaussian
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Honest integrability of the literal actual-model terminal/Brownian
pairing under the full independent model law. -/
theorem model_brownian_pairing_integrable (β : ℝ) (T s : ℝ≥0) :
    Integrable (fun ω => ⟪modelProcess N p β T ω,
      WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω.2)⟫_ℝ) (AnnealedModelLaw.law N p) := by
  let μ := AnnealedModelLaw.parameterLaw N p
  let A := ActualWeightedWiener.modelLp N p β T
  let B := vectorIntegralL2 (N := N) μ (intervalIndicator s)
  have hA : (A : AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N → State N)
      =ᵐ[μ.prod (VectorBrownian.law N)] modelProcess N p β T :=
    (ActualWeightedWiener.model_memLp N p β T).coeFn_toLp
  have hB : (B : AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N → State N)
      =ᵐ[μ.prod (VectorBrownian.law N)]
      (fun ω => WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω.2)) :=
    (vectorIntegralL2_coe μ (intervalIndicator s)).trans (vectorIntegral_prefix μ s)
  exact (L2.integrable_inner (𝕜 := ℝ) A B).congr (by
    filter_upwards [hA,hB] with ω ha hb
    rw [ha,hb])

/-- The actual annealed process equals the actual jointly measurable
quenched family at the physical terminal time. -/
theorem modelProcess_ae_jointProcess (β : ℝ) (T : ℝ≥0) :
    modelProcess N p β T=ᵐ[AnnealedModelLaw.law N p]
      (fun ω => jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
        (modelRadius_pos N) ω.1 T ω.2) :=
  annealedGlobal_eq_joint (ρ := AnnealedModelLaw.parameterLaw N p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
    (AnnealedModelLaw.parameter_disorder_memLp N p) T

/-- Genuine annealed backward primitive, with no law, regularity,
response, or integration-by-parts identity supplied as a premise. -/
theorem annealed_backward_primitive (hN : 0<N) (β : ℝ) (T s : ℝ≥0) (hs : s≤T) :
    WeightedBrownianTheorem.brownianPrimitive N p β T s=
    ∫ q,∫ r in Ioc (0 : ℝ≥0) s,
      backwardMeanKernel β (N+1) (modelRadius_pos N) q.1 q.2 T r
        ∂nonnegativeLebesgueMeasure ∂AnnealedModelLaw.parameterLaw N p := by
  let C : ℝ := Real.sqrt 2*(N : ℝ)
  let g : AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N → ℝ := fun ω =>
    ⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
      (modelRadius_pos N) ω.1 T ω.2,
      WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω.2)⟫_ℝ
  have he : (fun ω => ⟪modelProcess N p β T ω,
      WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω.2)⟫_ℝ)=ᵐ[AnnealedModelLaw.law N p] g :=
    (modelProcess_ae_jointProcess β T).mono (fun ω h => congrArg
      (fun y : State N => ⟪y,WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω.2)⟫_ℝ) h)
  have hi : Integrable g (AnnealedModelLaw.law N p) := (model_brownian_pairing_integrable β T s).congr he
  calc
    _ = (∫ ω,g ω ∂AnnealedModelLaw.law N p)/C := by
      unfold WeightedBrownianTheorem.brownianPrimitive
      rw [integral_div]
      change (∫ ω,⟪modelProcess N p β T ω,
        WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω.2)⟫_ℝ
          ∂AnnealedModelLaw.law N p)/C=_
      congr 1
      exact integral_congr_ae he
    _ = (∫ q,∫ ω,g (q,ω) ∂VectorBrownian.law N ∂AnnealedModelLaw.parameterLaw N p)/C := by
      congr 1
      exact integral_prod g hi
    _ = ∫ q,(∫ ω,g (q,ω) ∂VectorBrownian.law N)/C ∂AnnealedModelLaw.parameterLaw N p :=
      (integral_div C _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [AnnealedModelLaw.parameter_initial_onSphere hN p] with q hq
      exact (quenched_pairing (Nat.ne_of_gt hN) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
        q.1 q.2 hq T s hs).symm

end SphericalAging.ActualAnnealedBackwardPairing
