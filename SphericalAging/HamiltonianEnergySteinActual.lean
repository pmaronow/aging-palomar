module

public import SphericalAging.HamiltonianDisorderResponseGrowth
public import SphericalAging.GaussianEnergyStein

public section

/-! Actual finite-N Gaussian energy integration by parts for the genuinely
constructed Hamiltonian SDE terminal state and its proved tensor derivative.
Differentiability, sphere support, forcing representation, sharp response
moments, and Gaussian integrability are supplied by proofs, not premises. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.HamiltonianEnergySteinActual
open HardSphereDynamics FiniteModel HamiltonianDisorderTerminalDerivative
open HamiltonianDisorderResponseGrowth HamiltonianPredictableForcing
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma stateResponse_coordinate_growth (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : Disorder N p) (x : State N) (T t : ℝ≥0) (ht : t ≤ T) (I : TensorIndex N p) :
    ‖stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)‖ ≤
      (disorderConstant (N := N) (p := p) β R hR : ℝ)*
        Real.exp (exponentBase (N := N) (p := p) β R hR t / 2 +
          ((exponentSlope (N := N) (p := p) β R hR t / 2 : ℝ≥0) : ℝ)*‖J‖) := by
  have h := stateResponse_affine_exp_norm_bound (NullAugmentation.driver D₀) β R hR J
    (Pi.single I 1) x T t ht
    (fun A hm hz => NullAugmentation.augment_null_known_zero F hm hz)
  simpa only [Pi.norm_single,norm_one,mul_one] using h

/-- Coefficientwise Gaussian Stein identity for the actual differentiated
Hamiltonian diffusion, conditional only on its sphere initial point. -/
theorem coefficient_energy_stein_actual (hN : 0 < N) (hp : 0 < p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t ≤ T) (I : TensorIndex N p) :
    (∫ J : Disorder N p, J I * (∫ omega,
      GaussianIntegrationByParts.hamiltonianCoefficient I
        ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) omega) ∂P) ∂disorderLaw N p) =
      ∫ J : Disorder N p, ∫ omega,
        inner ℝ (gradient (GaussianIntegrationByParts.hamiltonianCoefficient I)
          ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) omega))
          ((stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)) omega)
            ∂P ∂disorderLaw N p := by
  apply GaussianEnergyStein.coefficient_energy_stein hN hp I
    (fun J => stateClass (NullAugmentation.driver D₀) β R hR J x T t)
    (fun J => stateResponse (NullAugmentation.driver D₀) β R hR J x T t)
    (fun J => stateClass_hasFDerivAt_disorder D₀ β R hR J x T t)
    (fun J => (stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht).mono
      (fun omega homega => (onSphere_iff_norm_sq _).mp homega))
    (disorderConstant (N := N) (p := p) β R hR)
    (exponentSlope (N := N) (p := p) β R hR t / 2)
    (exponentBase (N := N) (p := p) β R hR t / 2)
    (fun J => stateResponse_coordinate_growth D₀ β R hR J x T t ht I)

/-- Exact Hamiltonian Gaussian energy identity for the actual sphere
terminal family and its true tensor-disorder Jacobian response. -/
theorem hamiltonian_energy_stein_actual (hN : 0 < N) (hp : 0 < p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t ≤ T) :
    (∫ J : Disorder N p, ∫ omega,
      Hamiltonian N p J ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) omega)
        ∂P ∂disorderLaw N p) =
      ∑ I : TensorIndex N p, ∫ J : Disorder N p, ∫ omega,
        inner ℝ (gradient (GaussianIntegrationByParts.hamiltonianCoefficient I)
          ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) omega))
          ((stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)) omega)
            ∂P ∂disorderLaw N p := by
  apply GaussianEnergyStein.hamiltonian_energy_stein hN hp
    (fun J => stateClass (NullAugmentation.driver D₀) β R hR J x T t)
    (fun J => stateResponse (NullAugmentation.driver D₀) β R hR J x T t)
    (fun J => stateClass_hasFDerivAt_disorder D₀ β R hR J x T t)
    (fun J => (stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht).mono
      (fun omega homega => (onSphere_iff_norm_sq _).mp homega))
    (fun _ => disorderConstant (N := N) (p := p) β R hR)
    (fun _ => exponentSlope (N := N) (p := p) β R hR t / 2)
    (fun _ => exponentBase (N := N) (p := p) β R hR t / 2)
    (fun I J => stateResponse_coordinate_growth D₀ β R hR J x T t ht I)

end SphericalAging.HamiltonianEnergySteinActual
