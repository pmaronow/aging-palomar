module

public import SphericalAging.ActualNormalizedStateFourthIncrement

public section

/-! Literal overlaps are inner products of unit normalized actual states. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal InnerProductSpace
namespace SphericalAging.ActualNormalizedOverlap
open HardSphereDynamics ActualStateIncrementMoments ActualNormalizedStateFourthIncrement ActualModelOverlapVariance
variable {N p : ℕ}
set_option maxHeartbeats 800000

theorem normalizedState_norm_one (hN : 1 ≤ N) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,∀t,‖normalizedState (p:=p) β R hR t ω‖=1 := by
  filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω t
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  simp only [normalizedState,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _),FiniteCorrelationIto.sphere_norm (hω t),inv_mul_cancel₀ (Real.sqrt_pos.mpr hn).ne']

theorem scaled_inner_identity (hN : 0 < N) (x y : State N) :
    ⟪(Real.sqrt (N:ℝ))⁻¹ • x,(Real.sqrt (N:ℝ))⁻¹ • y⟫_ℝ = ⟪x,y⟫_ℝ/(N:ℝ) := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hs := Real.sq_sqrt hn.le
  simp only [real_inner_smul_left,real_inner_smul_right]
  calc
    (Real.sqrt (N:ℝ))⁻¹ * ((Real.sqrt (N:ℝ))⁻¹ * ⟪x,y⟫_ℝ) =
        ((Real.sqrt (N:ℝ))⁻¹)^2 * ⟪x,y⟫_ℝ := by ring
    _ = _ := by rw [inv_pow,hs,div_eq_mul_inv,mul_comm]

theorem actualOverlap_eq_normalized_inner (hN : 0 < N) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (s t : ℝ≥0) (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    actualOverlap β R hR s t ω =
      ⟪normalizedState β R hR s ω,normalizedState β R hR t ω⟫_ℝ :=
  (scaled_inner_identity hN (actualState β R hR s ω) (actualState β R hR t ω)).symm

theorem unit_inner_difference_le (x y a b : State N) (hy : ‖y‖=1) (ha : ‖a‖=1) :
    |⟪x,y⟫_ℝ-⟪a,b⟫_ℝ| ≤ ‖x-a‖+‖y-b‖ := by
  have he : ⟪x,y⟫_ℝ-⟪a,b⟫_ℝ=⟪x-a,y⟫_ℝ+⟪a,y-b⟫_ℝ := by
    rw [inner_sub_left,inner_sub_right]
    ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  simpa only [hy,ha,mul_one,one_mul] using
    add_le_add (abs_real_inner_le_norm (x-a) y) (abs_real_inner_le_norm a (y-b))

end SphericalAging.ActualNormalizedOverlap
