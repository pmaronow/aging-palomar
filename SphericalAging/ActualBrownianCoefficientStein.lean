module

public import SphericalAging.IndependentMixedCoefficientDuhamel
public import SphericalAging.ActualDisorderGammaVariance

public section

/-! Literal Gaussian disorder Stein and physical causal Duhamel for the
actual Brownian weighted coefficient observable. The Brownian vector is
unbounded and its true L² class is supplied by the constructed Wiener law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianCoefficientStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  IndependentMixedCoefficientDerivative IndependentMixedHamiltonianGaussianStein
  IndependentMixedCoefficientDuhamel HamiltonianDisorderTerminalDerivative
  CanonicalDisorderDuhamelMatrix BrownianVectorMoments ActualDisorderGammaVariance ResponseMatrixEnergyContraction
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem actual_brownian_coefficient_gradient_stein_duhamel (hN : 0<N) (hp : 0<p)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (x : State N) (hx : OnSphere x) (T s t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) :
    (∫ J : Disorder N p,J I*(∫ ω,
      inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω))
        (brownianVector s ω) ∂VectorBrownian.law N) ∂disorderLaw N p)=
      ∫ J : Disorder N p,∫ r,β*(∫ ω,
        inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
          (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω)
          (sampleMatrix (responseMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β J R hR hNR x hx t r) ω
            (gradient (hamiltonianCoefficient I)
              (HamiltonianJointProcess.globalProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) r ω))))
          (brownianVector s ω) ∂VectorBrownian.law N) ∂finiteTimeMeasure t ∂disorderLaw N p := by
  have hh := actual_independent_coefficient_gradient_stein_duhamel hN hp
    (VectorBrownian.driver N) β R hR hNR x hx T t ht I (brownianClass s)
  have hleft : (fun J : Disorder N p => J I*coefficientObservable (VectorBrownian.driver N) β R hR x T t I (brownianClass s) J)=
      (fun J => J I*(∫ ω,inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω))
          (brownianVector s ω) ∂VectorBrownian.law N)) := by
    funext J
    congr 1
    apply integral_congr_ae
    filter_upwards [brownianClass_ae (N := N) s] with ω hω
    rw [hω]
  rw [hleft] at hh
  exact hh.trans (integral_congr_ae (.of_forall (fun J => integral_congr_ae (.of_forall (fun r => by
    unfold independentKernelPairing
    congr 1
    apply integral_congr_ae
    filter_upwards [brownianClass_ae (N := N) s] with ω hω
    rw [hω])))))

end SphericalAging.ActualBrownianCoefficientStein
