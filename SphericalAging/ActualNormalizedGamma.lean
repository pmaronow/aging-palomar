module

public import SphericalAging.BrownianNormalizedDyadicTightness
public import SphericalAging.ActualNormalizedOverlap

public section

/-! The literal Γ observable is a normalized state--Brownian inner product,
with a genuine compact-path L² envelope. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualNormalizedGamma
open HardSphereDynamics ActualStateIncrementMoments ActualNormalizedStateFourthIncrement
open ActualNormalizedOverlap ActualBrownianPrimitiveTimeModulus BrownianNormalizedDyadicTightness
open ActualBrownianCompactSupSecondMoment
variable {N p : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem actualGamma_eq_normalized_inner (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (t s : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    actualGamma β R hR t s ω=
      ⟪normalizedState β R hR t ω,normalizedBrownian s ω⟫_ℝ/Real.sqrt 2 := by
  rw [show ⟪normalizedState β R hR t ω,normalizedBrownian s ω⟫_ℝ=
    ⟪actualState β R hR t ω,actualBrownian s ω⟫_ℝ/(N:ℝ) from
      scaled_inner_identity hN _ _]
  unfold actualGamma
  ring

@[expose] def gammaEnvelope (T : ℝ≥0) : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N→ℝ :=
  normalizedBrownianSup T

theorem gammaEnvelope_nonneg (T : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    0≤gammaEnvelope T ω := normalizedBrownianSup_nonneg T ω

theorem gammaEnvelope_memLp_two (T : ℝ≥0) :
    MemLp (gammaEnvelope (N:=N) (p:=p) T) 2 (AnnealedModelLaw.law N p) :=
  normalizedBrownianSup_memLp_two T

theorem gammaEnvelope_secondMoment_le (hN : 1≤N) (T : ℝ≥0) :
    (∫ω,(gammaEnvelope (N:=N) (p:=p) T ω)^2 ∂AnnealedModelLaw.law N p)≤1+3*(T:ℝ)^2 :=
  normalizedBrownianSup_secondMoment_le hN T

theorem gammaEnvelope_mean_le (hN : 1≤N) (T : ℝ≥0) :
    (∫ω,gammaEnvelope (N:=N) (p:=p) T ω ∂AnnealedModelLaw.law N p)≤Real.sqrt (1+3*(T:ℝ)^2) := by
  have hCS := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq
    (AnnealedModelLaw.law N p) (gammaEnvelope (N:=N) (p:=p) T) (gammaEnvelope_memLp_two T)
  simp only [probReal_univ,one_mul] at hCS
  exact (Real.le_sqrt (integral_nonneg (gammaEnvelope_nonneg T)) (by positivity)).mpr
    (hCS.trans (gammaEnvelope_secondMoment_le hN T))

theorem actualGamma_uniform_envelope (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,∀t s,s≤T→|actualGamma β R hR t s ω|≤gammaEnvelope T ω := by
  have hs2 : 1≤Real.sqrt 2 := by norm_num
  filter_upwards [normalizedState_norm_one (p:=p) hN β R hR hNR] with ω hω t s hs
  rw [actualGamma_eq_normalized_inner (by omega : 0<N),abs_div,abs_of_nonneg (Real.sqrt_nonneg 2)]
  calc
    _≤‖normalizedBrownian s ω‖/Real.sqrt 2 :=
      div_le_div_of_nonneg_right (by
        simpa only [hω t,one_mul] using
          abs_real_inner_le_norm (normalizedState β R hR t ω) (normalizedBrownian s ω)) (Real.sqrt_nonneg 2)
    _≤gammaEnvelope T ω/Real.sqrt 2 :=
      div_le_div_of_nonneg_right (normalizedBrownian_norm_le_sup T s hs ω) (Real.sqrt_nonneg 2)
    _≤gammaEnvelope T ω := (div_le_self (gammaEnvelope_nonneg T ω) hs2)

theorem inner_difference_weighted (x y a b : State N) (ha : ‖a‖=1) :
    |⟪x,y⟫_ℝ-⟪a,b⟫_ℝ|≤‖x-a‖*‖y‖+‖y-b‖ := by
  have he : ⟪x,y⟫_ℝ-⟪a,b⟫_ℝ=⟪x-a,y⟫_ℝ+⟪a,y-b⟫_ℝ := by
    rw [inner_sub_left,inner_sub_right]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by
    simpa only [ha,one_mul] using
      add_le_add (abs_real_inner_le_norm (x-a) y) (abs_real_inner_le_norm a (y-b)))

end SphericalAging.ActualNormalizedGamma
