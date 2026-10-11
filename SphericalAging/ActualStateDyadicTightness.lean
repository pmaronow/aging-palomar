module

public import SphericalAging.ActualNormalizedStateFourthIncrement
public import SphericalAging.DyadicProcessGoodEvent

public section

/-! Dimension-uniform dyadic tightness of the literal normalized physical
state trajectory, from its genuine fourth increment moments. -/
noncomputable section
open Set MeasureTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualStateDyadicTightness
open HardSphereDynamics ActualNormalizedStateFourthIncrement DyadicProcessGoodEvent DyadicContinuousChaining
variable {N p : ℕ}
set_option maxHeartbeats 1000000

@[expose] def dyadicRatio : ℝ := 9/10

@[expose] def stateBadTail (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (T : ℝ≥0) (m : ℕ) :=
  badTail (normalizedState (N:=N) (p:=p) β R hR) T dyadicRatio m

@[expose] def tailProbabilityCeiling (p : ℕ) (β T : ℝ≥0) (m : ℕ) : ℝ :=
  (fourthCoefficient p β T*(T:ℝ)^2)*(1/(2*dyadicRatio^4))^(m+1)/(1-1/(2*dyadicRatio^4))

@[expose] def gridErrorCeiling (m : ℕ) : ℝ := dyadicRatio^(m+1)/(1-dyadicRatio)

theorem uniformPartitionTime_succ_add (T : ℝ≥0) (n k : ℕ) :
    uniformPartitionTime T (2^n) (k+1) = uniformPartitionTime T (2^n) k+T/(2^n:ℝ≥0) := by
  unfold uniformPartitionTime
  push_cast
  rw [mul_add]
  simp only [mul_one,add_div]

theorem dyadicMesh_le_horizon (T : ℝ≥0) (n : ℕ) : T/(2^n:ℝ≥0) ≤ T := by
  apply div_le_self T.coe_nonneg
  exact one_le_pow₀ (by norm_num : (1:ℝ≥0)≤2)

theorem normalized_grid_fourthMoment (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) (n k : ℕ) :
    (∫ω,‖normalizedState (p:=p) β R hR (uniformPartitionTime T (2^n) (k+1)) ω-
      normalizedState β R hR (uniformPartitionTime T (2^n) k) ω‖^4 ∂AnnealedModelLaw.law N p) ≤
      (fourthCoefficient p β T*(T:ℝ)^2)/(2^n:ℝ)^2 := by
  rw [uniformPartitionTime_succ_add]
  have hh := normalizedState_increment_fourthMoment hN hp β R hR hNR T
    (uniformPartitionTime T (2^n) k) (T/(2^n:ℝ≥0)) (dyadicMesh_le_horizon T n)
  simpa only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,div_pow,mul_div_assoc] using hh

theorem stateBadTail_measure_le (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) (m : ℕ) :
    (AnnealedModelLaw.law N p) (stateBadTail (p:=p) β R hR T m) ≤
      ENNReal.ofReal (tailProbabilityCeiling p β T m) := by
  apply badTail_measure_le _ _ _ _ (mul_nonneg (fourthCoefficient_nonneg p β T) (sq_nonneg _))
    (by norm_num [dyadicRatio]) (by norm_num [dyadicRatio]) m
  intro n
  apply badGrid_measure_le _ _ _ _ (by norm_num [dyadicRatio]) n
  · intro k
    rw [uniformPartitionTime_succ_add]
    exact normalizedState_increment_memLp_four hN β R hR hNR
      (uniformPartitionTime T (2^n) k.val) (T/(2^n:ℝ≥0))
  · intro k
    exact normalized_grid_fourthMoment hN hp β R hR hNR T n k.val

theorem state_grid_approximation_on_good (β R : ℝ≥0) (hR : 0 < (R:ℝ))
    (T : ℝ≥0) (m : ℕ) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,ω ∉ stateBadTail (p:=p) β R hR T m →
      ∀s : ℝ≥0,s ≤ T →
        ‖normalizedState β R hR (timeApprox T m s) ω-normalizedState β R hR s ω‖ ≤ gridErrorCeiling m := by
  filter_upwards [normalizedState_continuous (p:=p) β R hR] with ω hω hgood s hs
  exact path_distance_to_grid_on_good (by norm_num [dyadicRatio]) (by norm_num [dyadicRatio]) hgood hω s hs

theorem gridErrorCeiling_tendsto_zero : Tendsto gridErrorCeiling atTop (𝓝 0) := by
  unfold gridErrorCeiling
  have hh := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num [dyadicRatio] : |dyadicRatio|<1)).comp
    (tendsto_add_atTop_nat 1)
  simpa only [gridErrorCeiling,Function.comp_def,zero_div] using hh.div_const (1-dyadicRatio)

theorem tailProbabilityCeiling_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (tailProbabilityCeiling p β T) atTop (𝓝 0) := by
  unfold tailProbabilityCeiling
  have hh := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (by norm_num [dyadicRatio] : |1/(2*dyadicRatio^4)|<1)).comp (tendsto_add_atTop_nat 1)
  simpa only [tailProbabilityCeiling,Function.comp_def,mul_zero,zero_div] using
    (hh.const_mul (fourthCoefficient p β T*(T:ℝ)^2)).div_const (1-1/(2*dyadicRatio^4))

end SphericalAging.ActualStateDyadicTightness
