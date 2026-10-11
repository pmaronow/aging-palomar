module

public import SphericalAging.ActualGammaPredictorIncrementDecomposition
public import SphericalAging.ActualGammaPredictorLaggedNoise
public import SphericalAging.ActualGammaPredictorComparison
public import SphericalAging.SecondMomentPerturbation

public section

/-! True local mean-square increments of the backward Γ predictor, with a
sharp dimension-scaled linear term and an actual quadratic error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ActualGammaPredictorLocalIncrement
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereGammaVariance
open ActualGammaBackwardPredictor ActualGammaPredictorNoiseBounds BrownianVectorMoments
open ActualGammaPredictorTaylorMoment ActualGammaPredictorLinearErrorMoment
open ActualGammaPredictorCompactTaylor ActualGammaPredictorComparison
open ActualGammaPredictorLaggedNoise ActualGammaPredictorIncrementDecomposition
open WeightedBrownianNoiseRow SecondMomentPerturbation ActualSphereFrozenNoiseIncrement
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def rowCeiling (β : ℝ≥0) (J : Disorder N p) (T s : ℝ≥0) : ℝ :=
  ((3*(s : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+3/2)/(N : ℝ)

@[expose] def errorCeiling (β : ℝ≥0) (J : Disorder N p) (S : ℝ≥0) (C : ℝ) : ℝ :=
  2*(taylorMomentCeiling β J S C+
    2*(C/(Real.sqrt 2*(N : ℝ))+C)^2*frozenErrorCeiling β J S*(1+(N : ℝ)*S))

theorem errorCeiling_nonneg (β : ℝ≥0) (J : Disorder N p) (S : ℝ≥0) (C : ℝ) :
    0≤errorCeiling β J S C := by
  unfold errorCeiling taylorMomentCeiling ActualSphereInitialFourthIncrement.smallFourthCeiling
    frozenErrorCeiling ActualSphereOneStepEulerError.oneStepCeiling
  have := GaussianLandscape.landscapeNorm_nonnegative N p J
  positivity

theorem rowCeiling_nonneg (β : ℝ≥0) (J : Disorder N p) (T s : ℝ≥0) :
    0≤rowCeiling β J T s := by unfold rowCeiling;positivity

section Actual
variable (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    {Z0 : VectorBrownian.Space N→State N} (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀ U,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X U)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀u,OnSphere (X u ω))
    (T t s S r h : ℝ≥0) (ht : t≤T) (hst : s≤t) (hT : 0<T)
    (hqs : r+h≤s) (hrS : r≤S) (hhS : h≤S) (C : ℝ) (hC : 0≤C)
    (hBound : SpatialBound (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-(r+h)))
      (initialMean β R hR J T (t-(r+h)) (s-(r+h))) C)

include hN hp hNR hX hSphere ht hT hqs hrS hhS hC hBound in
theorem spatial_increment_secondMoment (η : ℝ) (hη : 0<η) :
    (∫ ω,(predictor β R hR J T t s (r+h) (X (r+h) ω) (brownianVector (r+h) ω)-
      predictor β R hR J T t s (r+h) (X r ω) (brownianVector r ω))^2 ∂VectorBrownian.law N)≤
      ((1+η)*rowCeiling β J T s)*(h : ℝ)+(1+1/η)*errorCeiling β J S C*(h : ℝ)^2 := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let Z : Fin N→VectorBrownian.Space N→ℝ :=
    fun j ω => noiseRow β R hR J T t s (r+h) (X r ω) (brownianVector r ω) j
  let A : VectorBrownian.Space N→ℝ := fun ω =>
    predictor β R hR J T t s (r+h) (X (r+h) ω) (brownianVector (r+h) ω)-
      predictor β R hR J T t s (r+h) (X r ω) (brownianVector r ω)
  let B : VectorBrownian.Space N→ℝ := fun ω => ∑j : Fin N,Z j ω*VectorIto.increment D j r (r+h) ω
  let Rem := taylorRemainder β R hR J X T t s (r+h) r h
  let Err := linearError β R hR J T t s (r+h) r h X
  have hrq : r≤r+h := le_add_of_nonneg_right (show (0 : ℝ≥0)≤h from bot_le)
  have hn : 0<N := by omega
  have hA2 : MemLp A 2 P :=
    (past_spatial_predictor_memLp hn β R hR hNR J X hX hSphere T t s ht hT (r+h) (r+h)).sub
      (past_spatial_predictor_memLp hn β R hR hNR J X hX hSphere T t s ht hT r (r+h))
  have hZ2 (j : Fin N) : MemLp (Z j) 2 P :=
    lagged_noiseRow_memLp β R hR J X hX T t s r (r+h) hT hN hp hNR hSphere ht hrq hqs j
  have hZm (j : Fin N) : AEStronglyMeasurable[NullAugmentation.augment (VectorBrownian.filtration N) P r] (Z j) P :=
    (lagged_noiseRow_stronglyMeasurable β R hR J X hX T t s r (r+h) hT j).aestronglyMeasurable
  have hb := row_secondMoment D hrq Z hZ2 hZm
  have hz := lagged_noiseRow_secondMoment β R hR J X hX T t s r (r+h) hT hN hp hNR hSphere ht hrq hqs
  have hRem := actual_taylorRemainder_secondMoment hn β R hR hNR J S r h hrS hhS X hX hSphere
    T t s (r+h) hT C hC hBound
  have hErr := actual_linearError_secondMoment β R hR J T t s (r+h) r h X hX hT hn hp hNR hSphere
    S hrS hhS C hC hBound
  have he : ∀ᵐ ω ∂P,A ω=B ω+Rem ω+Err ω := .of_forall
    (spatial_increment_eq β R hR J X T t s (r+h) r h)
  have hi := integral_square_perturbation A B Rem Err hA2.integrable_sq hb.1.integrable_sq hRem.1 hErr.1 he η hη
  have hBb : (∫ω,(B ω)^2 ∂P)≤(h : ℝ)*rowCeiling β J T s := by
    rw [hb.2]
    simp only [NNReal.coe_add,add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left hz.2 h.coe_nonneg
  have hRB : (∫ω,(Rem ω)^2 ∂P)+(∫ω,(Err ω)^2 ∂P)≤
      (taylorMomentCeiling β J S C+
      2*(C/(Real.sqrt 2*(N : ℝ))+C)^2*frozenErrorCeiling β J S*(1+(N : ℝ)*S))*(h : ℝ)^2 := by
    have hh := add_le_add hRem.2 hErr.2
    simpa only [add_mul] using hh
  calc
    _≤(1+η)*(∫ω,(B ω)^2 ∂P)+2*(1+1/η)*((∫ω,(Rem ω)^2 ∂P)+(∫ω,(Err ω)^2 ∂P)) := hi
    _≤(1+η)*((h : ℝ)*rowCeiling β J T s)+2*(1+1/η)*
        ((taylorMomentCeiling β J S C+
        2*(C/(Real.sqrt 2*(N : ℝ))+C)^2*frozenErrorCeiling β J S*(1+(N : ℝ)*S))*(h : ℝ)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hBb (by positivity))
        (mul_le_mul_of_nonneg_left hRB (by positivity))
    _=_ := by dsimp only [errorCeiling];ring

include hN hp hNR hX hSphere ht hst hT hqs hrS hhS hC hBound in
theorem predictor_increment_secondMoment (η : ℝ) (hη : 0<η) :
    (∫ ω,(predictor β R hR J T t s (r+h) (X (r+h) ω) (brownianVector (r+h) ω)-
      predictor β R hR J T t s r (X r ω) (brownianVector r ω))^2 ∂VectorBrownian.law N)≤
      ((1+η)*rowCeiling β J T s)*(h : ℝ)+(1+1/η)*errorCeiling β J S C*(h : ℝ)^2 :=
  (predictor_increment_spatial_comparison (by omega : 0<N) β R hR hNR J X hX hSphere T t s ht hst hT
    r (r+h) (le_add_of_nonneg_right (show (0 : ℝ≥0)≤h from bot_le)) hqs).trans
      (spatial_increment_secondMoment hN hp β R hR hNR J X hX hSphere T t s S r h ht hT hqs hrS hhS C hC hBound η hη)

end Actual
end SphericalAging.ActualGammaPredictorLocalIncrement
