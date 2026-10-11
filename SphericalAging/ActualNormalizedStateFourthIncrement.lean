module

public import SphericalAging.ActualStateIncrementFourthMoment
public import SphericalAging.DyadicContinuousChaining

public section

/-! Actual normalized state paths satisfy a dimension-independent fourth
increment estimate on every bounded time interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualNormalizedStateFourthIncrement
open HardSphereDynamics FiniteModel AnnealedCutoffProcess ActualStateIncrementMoments
open ActualStateIncrementFourthMoment GaussianLandscapeMoments
set_option maxHeartbeats 1000000
variable {N p : ℕ}

@[expose] def normalizedState (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (t : ℝ≥0)
    (ω : Parameter N p×VectorBrownian.Space N) : State N :=
  (Real.sqrt (N:ℝ))⁻¹ • actualState β R hR t ω

@[expose] def fourthCoefficient (p : ℕ) (β T : ℝ≥0) : ℝ :=
  80*(2*(T:ℝ)+4)*(1+((β:ℝ)*(p:ℝ))^3*momentCeiling p 3)

theorem fourthCoefficient_nonneg (p : ℕ) (β T : ℝ≥0) : 0 ≤ fourthCoefficient p β T := by
  unfold fourthCoefficient momentCeiling
  positivity

theorem incrementFourthCeiling_le_quadratic (p : ℕ) (β T t : ℝ≥0) (ht : t ≤ T) :
    incrementFourthCeiling p β t ≤ fourthCoefficient p β T*(t:ℝ)^2 := by
  have htr : (t:ℝ) ≤ (T:ℝ) := ht
  have hm : 0 ≤ 1+((β:ℝ)*(p:ℝ))^3*momentCeiling p 3 := by
    unfold momentCeiling
    positivity
  unfold incrementFourthCeiling fourthCoefficient
  have hh : 2*(t:ℝ)^3+4*(t:ℝ)^2 ≤ (2*(T:ℝ)+4)*(t:ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right htr (sq_nonneg (t:ℝ))]
  have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh hm) (by norm_num : (0:ℝ)≤80)
  convert he using 1 <;> ring

theorem norm_scaled_four (v : State N) :
    ‖(Real.sqrt (N:ℝ))⁻¹ • v‖^4 = ‖v‖^4/(N:ℝ)^2 := by
  have hs : (Real.sqrt (N:ℝ))^4=(N:ℝ)^2 := by
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow,inv_pow,hs,div_eq_mul_inv,mul_comm]

theorem normalizedState_continuous (β R : ℝ≥0) (hR : 0 < (R:ℝ)) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,Continuous (fun t => normalizedState (p:=p) β R hR t ω) := by
  filter_upwards [AnnealedGlobalSDE.globalProcess_continuous
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p)] with ω hω
  exact hω.const_smul ((Real.sqrt (N:ℝ))⁻¹)

theorem normalizedState_increment_memLp_four (hN : 1 ≤ N) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (s t : ℝ≥0) :
    MemLp (fun ω => normalizedState (p:=p) β R hR (s+t) ω-
      normalizedState β R hR s ω) 4 (AnnealedModelLaw.law N p) := by
  have hh := (ActualBrownianPrimitiveTimeModulus.actualStateIncrement_memLp_four
    (p:=p) hN β R hR hNR s t).const_smul ((Real.sqrt (N:ℝ))⁻¹)
  change MemLp (fun ω => ((Real.sqrt (N:ℝ))⁻¹) •
    (actualState (p:=p) β R hR (s+t) ω-actualState β R hR s ω)) 4 (AnnealedModelLaw.law N p) at hh
  simpa only [normalizedState,smul_sub] using hh

theorem normalizedState_increment_fourthMoment (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T s t : ℝ≥0) (ht : t ≤ T) :
    (∫ω,‖normalizedState (p:=p) β R hR (s+t) ω-normalizedState β R hR s ω‖^4
      ∂AnnealedModelLaw.law N p) ≤ fourthCoefficient p β T*(t:ℝ)^2 := by
  simp only [normalizedState,←smul_sub,norm_scaled_four]
  rw [integral_div]
  exact (actual_increment_fourthMoment hN hp β R hR hNR s t).trans
    (incrementFourthCeiling_le_quadratic p β T t ht)

end SphericalAging.ActualNormalizedStateFourthIncrement
