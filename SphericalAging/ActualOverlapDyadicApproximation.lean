module

public import SphericalAging.ActualStateDyadicTightness
public import SphericalAging.ActualNormalizedOverlap
public import SphericalAging.ActualOverlapTimeModulus
public import SphericalAging.BoundedMeshMeanComparison

public section

/-! Actual compact-time overlap approximation and its mean, using the
genuine normalized-state dyadic good event. -/
noncomputable section
open Set MeasureTheory StochasticCalculus
open scoped NNReal InnerProductSpace
namespace SphericalAging.ActualOverlapDyadicApproximation
open HardSphereDynamics ActualStateIncrementMoments ActualNormalizedStateFourthIncrement
open ActualStateDyadicTightness ActualNormalizedOverlap DyadicProcessGoodEvent DyadicContinuousChaining
open ActualModelOverlapVariance ActualOverlapTimeModulus BoundedMeshMeanComparison
variable {N p : ℕ}
set_option maxHeartbeats 1000000

theorem normalizedState_stronglyMeasurable (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (t : ℝ≥0) :
    StronglyMeasurable (normalizedState (N:=N) (p:=p) β R hR t) := by
  exact ((AnnealedGlobalSDE.globalProcess_stronglyAdapted
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p) t).mono
      ((AnnealedModelLaw.filtration N p).le t)).const_smul ((Real.sqrt (N:ℝ))⁻¹)

theorem stateBadTail_measurableSet (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (T : ℝ≥0) (m : ℕ) :
    MeasurableSet (stateBadTail (N:=N) (p:=p) β R hR T m) := by
  unfold stateBadTail badTail
  apply MeasurableSet.iUnion
  intro j
  unfold badGrid
  simp only [setOf_exists]
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_lt measurable_const
    (((normalizedState_stronglyMeasurable β R hR _).sub
      (normalizedState_stronglyMeasurable β R hR _)).norm.measurable)

theorem actualOverlap_uniform_bound (hN : 1 ≤ N) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,∀s t,|actualOverlap (p:=p) β R hR s t ω| ≤ 1 := by
  filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω s t
  exact FiniteCorrelationIto.overlap_abs_le_one (by omega : 0<N) (hω s) (hω t)

theorem actualOverlap_grid_approximation_on_good (hN : 1 ≤ N) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) (m : ℕ) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,ω ∉ stateBadTail (p:=p) β R hR T m →
      ∀s t : ℝ≥0,s ≤ T → t ≤ T →
        |actualOverlap β R hR s t ω-
          actualOverlap β R hR (timeApprox T m s) (timeApprox T m t) ω| ≤ 2*gridErrorCeiling m := by
  filter_upwards [state_grid_approximation_on_good (p:=p) β R hR T m,
    normalizedState_norm_one hN β R hR hNR] with ω hω hn hgood s t hs ht
  rw [actualOverlap_eq_normalized_inner (by omega : 0<N),actualOverlap_eq_normalized_inner (by omega : 0<N)]
  refine (unit_inner_difference_le _ _ _ _ (hn t) (hn (timeApprox T m s))).trans ?_
  have hs' := hω hgood s hs
  have ht' := hω hgood t ht
  rw [norm_sub_rev] at hs' ht'
  linarith

theorem actualOverlap_mean_grid_difference_le (hN : 1 ≤ N) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) (m : ℕ)
    (s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) :
    |(∫ω,actualOverlap (p:=p) β R hR s t ω ∂AnnealedModelLaw.law N p)-
      ∫ω,actualOverlap β R hR (timeApprox T m s) (timeApprox T m t) ω ∂AnnealedModelLaw.law N p| ≤
        2*gridErrorCeiling m+2*(AnnealedModelLaw.law N p).real (stateBadTail (p:=p) β R hR T m) := by
  apply mean_difference_le_bad_event
    ((actualOverlap_memLp_two (p:=p) hN β R hR hNR s t).integrable (by norm_num))
    ((actualOverlap_memLp_two (p:=p) hN β R hR hNR _ _).integrable (by norm_num))
    (stateBadTail_measurableSet β R hR T m) (by norm_num [gridErrorCeiling,dyadicRatio]; positivity) (by norm_num)
  · filter_upwards [actualOverlap_uniform_bound hN β R hR hNR] with ω hω
    exact (abs_sub _ _).trans (by linarith [hω s t,hω (timeApprox T m s) (timeApprox T m t)])
  · exact (actualOverlap_grid_approximation_on_good hN β R hR hNR T m).mono
      (fun ω hω hgood => hω hgood s t hs ht)

end SphericalAging.ActualOverlapDyadicApproximation
