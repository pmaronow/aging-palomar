module

public import SphericalAging.ActualBackgroundGammaVariance
public import SphericalAging.ActualBrownianPrimitiveTimeModulus

public section

/-! The genuine L² background Brownian pairing is the Brownian conditional
mean of the literal independent Gaussian × sphere × Wiener model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualBackgroundGammaLaw
open FiniteModel HardSphereDynamics ActualSphereTransition ActualBackgroundOverlapLaw
open ActualDisorderGammaVariance ActualSphereGammaVariance ActualBackgroundGammaVariance
open ActualBrownianPrimitiveTimeModulus ActualStateIncrementMoments BrownianVectorMoments
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def jointGamma (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0)
    (q : (Disorder N p×State N)×VectorBrownian.Space N) : ℝ :=
  inner ℝ (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 t q.2)
    (brownianVector s q.2)/(Real.sqrt 2*(N : ℝ))

theorem backgroundMean_eq_joint_mean (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (T t s : ℝ≥0) (ht : t≤T) (q : Disorder N p×State N) :
    backgroundMean β R hR T t s q=
      ∫ ω,jointGamma β R hR t s (q,ω) ∂VectorBrownian.law N := by
  unfold backgroundMean initialMean gammaMean
  rw [L2.inner_def,← integral_div]
  apply integral_congr_ae
  filter_upwards [terminalClass_ae_joint (VectorBrownian.driver N) β R hR q.1 q.2 T t ht,
    brownianClass_ae s] with ω hx hb
  simp only [hx,hb,jointGamma,real_inner_comm]

theorem actualGamma_ae_joint (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0) :
    actualGamma (p := p) β R hR t s=ᵐ[AnnealedModelLaw.law N p] jointGamma β R hR t s := by
  filter_upwards [actualState_ae_joint (N := N) (p := p) β R hR t] with ω hx
  simp only [actualGamma,jointGamma,actualBrownian,hx]

theorem actualConditionalGamma_ae_background (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (T t s : ℝ≥0) (ht : t≤T) :
    (fun q : Disorder N p×State N => ∫ ω,actualGamma β R hR t s (q,ω) ∂VectorBrownian.law N)
      =ᵐ[AnnealedModelLaw.parameterLaw N p] backgroundMean β R hR T t s := by
  have hh := Measure.ae_ae_of_ae_prod (actualGamma_ae_joint (N := N) (p := p) β R hR t s)
  filter_upwards [hh] with q hq
  exact (integral_congr_ae hq).trans (backgroundMean_eq_joint_mean β R hR T t s ht q).symm

theorem actual_conditional_gamma_background_variance (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T t s : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    variance (fun q : Disorder N p×State N =>
      ∫ ω,actualGamma β R hR t s (q,ω) ∂VectorBrownian.law N)
      (AnnealedModelLaw.parameterLaw N p)≤(s : ℝ)*backgroundVarianceCeiling p β T/(N : ℝ) := by
  rw [variance_congr (actualConditionalGamma_ae_background β R hR T t s ht)]
  exact actual_background_gamma_variance hN hp β R hR hNR T t s ht hT

end SphericalAging.ActualBackgroundGammaLaw
