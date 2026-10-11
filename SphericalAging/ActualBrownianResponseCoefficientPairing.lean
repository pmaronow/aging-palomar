module

public import SphericalAging.ActualBrownianResponseCoefficientIntegral
public import SphericalAging.ActualBrownianCoefficientStein
public import SphericalAging.TwoTimeResponseHorizon

public section

/-! The genuine joint actual Brownian Hessian coefficient field represents
the literal physical causal Duhamel kernel, including its true Brownian
L² representative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianResponseCoefficientPairing
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
  ActualBrownianResponseCoefficientIntegral IndependentMixedCoefficientDuhamel
  ActualTerminalHorizonConsistency TwoTimeResponseParameter TwoTimeResponseTimeParameter
  TwoTimeResponseHorizon ResponseMatrixEnergyContraction AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualSphereTransition ActualDisorderGammaVariance
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem brownianHessianField_pairing (hN : 0<N) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T H S : ℝ≥0) (hHT : H≤T)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N))
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx))
    (I : TensorIndex N p) (r : WaitingTime H) (q : Disorder N p×State N) (hx : OnSphere q.2) :
    β*(∫ ω,brownianHessianField β R hR H S U I (r,(q,ω)) ∂VectorBrownian.law N)=
      independentKernelPairing (Nat.ne_of_gt hN) (VectorBrownian.driver N) β q.1 R hR hNR q.2 hx
        T H I (brownianClass S) r := by
  unfold independentKernelPairing
  congr 1
  have hm := physicalMatrix_horizon_independent (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
    r (H-r) (H+1) (by exact (tsub_le_self).trans (le_add_right le_rfl)) (H-r) le_rfl q hx
  have hmr : physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR r (H-r) (H-r) q hx=
      CanonicalDisorderDuhamelMatrix.responseMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β q.1 R hR hNR q.2 hx H r := rfl
  apply integral_congr_ae
  filter_upwards [hUs r q hx,jointProcess_ae (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q,
    stateClass_ae_global_at (VectorBrownian.driver N) β R hR q.1 q.2 T H hHT,brownianClass_ae S]
      with ω hu hX hH hB
  change inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) _ (U (r,(q,ω)) _)) _=_
  rw [hu,hm,hmr,hH,hB]
  have hXH := hX H
  have hXr := hX r
  simp only [trajectory] at *
  rw [hXH,hXr]

end SphericalAging.ActualBrownianResponseCoefficientPairing
