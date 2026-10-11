module

public import SphericalAging.ActualQuenchedPastVectorMean
public import SphericalAging.ActualGammaFutureInnovation

public section

/-! The actual fixed-disorder Brownian pairing satisfies its physical
integral row. The earlier Brownian value is unbounded; its genuine L² law
and full-filtration martingale orthogonality justify its use. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualQuenchedGammaIntegral
open HardSphereDynamics FiniteModel ActualSphereTransition BrownianVectorMoments
  ActualGammaFutureInnovation ActualQuenchedPastVectorMean
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def gammaPair (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p) (x : State N)
    (t s : ℝ≥0) : ℝ :=
  ∫ ω,inner ℝ (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t ω)
    (brownianVector s ω)/(Real.sqrt 2*N) ∂VectorBrownian.law N

 theorem actual_quenched_gamma_integral (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (s t : ℝ≥0) (hst : s≤t) :
    gammaPair β R hR J x t s=gammaPair β R hR J x s s+
      ∫ u in (s : ℝ)..(t : ℝ),∫ ω,
        pastDrift (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x
          (brownianVector s) (u,ω) ∂VectorBrownian.law N := by
  have hy : StronglyMeasurable[NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N) s] (brownianVector (N := N) s) :=
    (brownianVector_waiting_measurable s).stronglyMeasurable
  exact actual_quenched_past_vector_mean hN (VectorBrownian.driver N) β R hR hNR J x hx
    s t hst (brownianVector s) hy (brownianVector_memLp s (q := 2) (by norm_num))

end SphericalAging.ActualQuenchedGammaIntegral
