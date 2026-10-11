module

public import SphericalAging.ActualCKCorrelationIntegralResidual

public section

/-! The literal finite-N mean correlation CK integral defect vanishes
uniformly on each compact causal time triangle. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKCorrelationCompactDefect
open HardSphereDynamics FiniteModel ActualSphereTransition ActualAnnealedCorrelationIntegral
  ActualCKCorrelationSlopeResidual ActualCKCorrelationUniformResidual
  ActualCKCorrelationIntegralResidual
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def compactDefectCeiling (p : ℕ) (β T : ℝ≥0) (N : ℕ) : ℝ :=
  (T : ℝ)*correlationSlopeResidualCeiling p β T T T N

 theorem actual_correlation_integral_residual_uniform (hN : 3≤N) (hp : 3≤p) (β T : ℝ≥0)
    (hT : 0<T) (s t : ℝ≥0) (hst : s≤t) (htT : t≤T) :
    |correlationIntegralResidual (by omega : N≠0) p β s t|≤compactDefectCeiling p β T N := by
  have hε : 0≤correlationSlopeResidualCeiling p β T T T N :=
    (abs_nonneg _).trans (actual_correlation_slope_residual_uniform hN hp β T hT 0 0 le_rfl (by positivity))
  have hlen : (t : ℝ)-s≤T := by
    have htt : (t : ℝ)≤T := htT
    linarith [s.coe_nonneg]
  exact (actual_correlation_integral_residual_le hN hp β s t T hst htT hT).trans
    (mul_le_mul_of_nonneg_right hlen hε)

 theorem compactDefectCeiling_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (fun n : ℕ => compactDefectCeiling p β T (n+3)) atTop (𝓝 0) := by
  simpa only [compactDefectCeiling,mul_zero] using
    (correlationSlopeResidualCeiling_tendsto_zero p β T T T).const_mul (T : ℝ)

 theorem actual_correlation_ck_defect_tendstoUniformlyOn (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℝ≥0×ℝ≥0 =>
      correlationIntegralResidual (N := n+3) (by omega : n+3≠0) p β z.1 z.2)
      (fun _ => (0 : ℝ)) atTop {z | z.1≤z.2 ∧ z.2≤T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := (compactDefectCeiling_tendsto_zero p β T).eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn z hz
  rw [Real.dist_eq,zero_sub,abs_neg]
  exact (actual_correlation_integral_residual_uniform (by omega : 3≤n+3) hp β T hT
    z.1 z.2 hz.1 hz.2).trans_lt hn

end SphericalAging.ActualCKCorrelationCompactDefect
