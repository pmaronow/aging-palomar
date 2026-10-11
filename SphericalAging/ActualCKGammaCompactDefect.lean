module

public import SphericalAging.ActualCKGammaIntegralResidual

public section

/-! The literal actual mean Γ CK integral defect vanishes uniformly on
each compact causal time triangle. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKGammaCompactDefect
open ActualCKGammaSlopeResidual ActualCKGammaUniformResidual ActualCKGammaIntegralResidual
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def gammaCompactDefectCeiling (p : ℕ) (β T : ℝ≥0) (N : ℕ) : ℝ :=
  (T : ℝ)*gammaSlopeResidualCeiling p β T T T N

 theorem actual_gamma_integral_residual_uniform (hN : 3≤N) (hp : 3≤p) (β T : ℝ≥0)
    (hT : 0<T) (t s : ℝ≥0) (hst : s≤t) (htT : t≤T) :
    |gammaIntegralResidual (by omega : N≠0) p β t s|≤gammaCompactDefectCeiling p β T N := by
  have hε : 0≤gammaSlopeResidualCeiling p β T T T N :=
    (abs_nonneg _).trans (actual_gamma_slope_residual_uniform hN hp β T hT 0 0 (by positivity) (by positivity))
  have hlen : (t : ℝ)-s≤T := by
    have htt : (t : ℝ)≤T := htT
    linarith [s.coe_nonneg]
  exact (actual_gamma_integral_residual_le hN hp β t s T hst htT hT).trans
    (mul_le_mul_of_nonneg_right hlen hε)

 theorem gammaCompactDefectCeiling_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (fun n : ℕ => gammaCompactDefectCeiling p β T (n+3)) atTop (𝓝 0) := by
  simpa only [gammaCompactDefectCeiling,mul_zero] using
    (gammaSlopeResidualCeiling_tendsto_zero p β T T T).const_mul (T : ℝ)

 theorem actual_gamma_ck_defect_tendstoUniformlyOn (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℝ≥0×ℝ≥0 =>
      gammaIntegralResidual (N := n+3) (by omega : n+3≠0) p β z.1 z.2)
      (fun _ => (0 : ℝ)) atTop {z | z.2≤z.1 ∧ z.1≤T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := (gammaCompactDefectCeiling_tendsto_zero p β T).eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn z hz
  rw [Real.dist_eq,zero_sub,abs_neg]
  exact (actual_gamma_integral_residual_uniform (by omega : 3≤n+3) hp β T hT
    z.1 z.2 hz.1 hz.2).trans_lt hn

end SphericalAging.ActualCKGammaCompactDefect
