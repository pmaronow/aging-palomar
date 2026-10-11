module

public import SphericalAging.ActualGammaPredictorTaylorMoment
public import SphericalAging.ActualGammaPredictorLinearErrorMoment

public section

/-! Exact spatial increment of the genuine backward Γ predictor. The
noise row, Taylor remainder, and frozen-noise linear error are the actual
constructed quantities, without any moment or variance premise. -/
noncomputable section
open StochasticCalculus
open scoped NNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualGammaPredictorIncrementDecomposition
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereGammaVariance
open ActualGammaBackwardPredictor BrownianVectorMoments BrownianPairingSpatialTaylor
open BrownianPairingSpatialRegularity ActualGammaPredictorNoiseBounds
open ActualGammaPredictorTaylorMoment ActualGammaPredictorLinearErrorMoment
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem spatial_increment_eq (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (X : ℝ≥0→VectorBrownian.Space N→State N) (T t s q r h : ℝ≥0)
    (ω : VectorBrownian.Space N) :
    predictor β R hR J T t s q (X (r+h) ω) (brownianVector (r+h) ω)-
      predictor β R hR J T t s q (X r ω) (brownianVector r ω)=
      (∑ j : Fin N,noiseRow β R hR J T t s q (X r ω) (brownianVector r ω) j*
        VectorIto.increment (NullAugmentation.driver (VectorBrownian.driver N)) j r (r+h) ω)+
      taylorRemainder β R hR J X T t s q r h ω+
      linearError β R hR J T t s q r h X ω := by
  have hn := actual_linearIncrement_noise_sum β R hR J T t s q (X r ω)
    (brownianVector r ω) (brownianVector (r+h) ω-brownianVector r ω)
  have hi (j : Fin N) :
      (brownianVector (r+h) ω-brownianVector r ω) j=
        VectorIto.increment (NullAugmentation.driver (VectorBrownian.driver N)) j r (r+h) ω := rfl
  simp only [hi] at hn
  rw [←hn]
  simp only [taylorRemainder,linearError,remainder,pairing,predictor,initialMean,
    add_sub_cancel]
  ring

end SphericalAging.ActualGammaPredictorIncrementDecomposition
