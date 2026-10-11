module

public import SphericalAging.ActualCKCorrelationCompactDefect
public import SphericalAging.ActualCKGammaCompactDefect

public section

/-! Both literal actual CK integral defects vanish along every genuine
diverging dimension sequence, uniformly on a compact causal triangle. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKJointDefectDimensionLimit
open ActualCKCorrelationCompactDefect ActualCKCorrelationIntegralResidual
  ActualCKGammaCompactDefect ActualCKGammaIntegralResidual
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} {L : Filter A} {dim : A→ℕ}

 theorem actual_correlation_defect_dimension_tendstoUniformlyOn (hdim : Tendsto dim L atTop)
    (hD : ∀ j,3≤dim j) (p : ℕ) (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) :
    TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 =>
      correlationIntegralResidual (N := dim j) (by have := hD j;omega) p β z.1 z.2)
      (fun _ => (0 : ℝ)) L {z | z.1≤z.2 ∧ z.2≤T} := by
  have hCeil : Tendsto (compactDefectCeiling p β T) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 3).mp (compactDefectCeiling_tendsto_zero p β T)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := (hCeil.comp hdim).eventually (gt_mem_nhds hε)
  filter_upwards [he] with j hj z hz
  rw [Real.dist_eq,zero_sub,abs_neg]
  exact (actual_correlation_integral_residual_uniform (hD j) hp β T hT z.1 z.2 hz.1 hz.2).trans_lt hj

 theorem actual_gamma_defect_dimension_tendstoUniformlyOn (hdim : Tendsto dim L atTop)
    (hD : ∀ j,3≤dim j) (p : ℕ) (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) :
    TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 =>
      gammaIntegralResidual (N := dim j) (by have := hD j;omega) p β z.1 z.2)
      (fun _ => (0 : ℝ)) L {z | z.2≤z.1 ∧ z.1≤T} := by
  have hCeil : Tendsto (gammaCompactDefectCeiling p β T) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 3).mp (gammaCompactDefectCeiling_tendsto_zero p β T)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := (hCeil.comp hdim).eventually (gt_mem_nhds hε)
  filter_upwards [he] with j hj z hz
  rw [Real.dist_eq,zero_sub,abs_neg]
  exact (actual_gamma_integral_residual_uniform (hD j) hp β T hT z.1 z.2 hz.1 hz.2).trans_lt hj

 theorem actual_joint_ck_defects_dimension_limit (hdim : Tendsto dim L atTop)
    (hD : ∀ j,3≤dim j) (p : ℕ) (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) :
    TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 =>
      correlationIntegralResidual (N := dim j) (by have := hD j;omega) p β z.1 z.2)
      (fun _ => (0 : ℝ)) L {z | z.1≤z.2 ∧ z.2≤T} ∧
    TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 =>
      gammaIntegralResidual (N := dim j) (by have := hD j;omega) p β z.1 z.2)
      (fun _ => (0 : ℝ)) L {z | z.2≤z.1 ∧ z.1≤T} :=
  ⟨actual_correlation_defect_dimension_tendstoUniformlyOn hdim hD p hp β T hT,
    actual_gamma_defect_dimension_tendstoUniformlyOn hdim hD p hp β T hT⟩

end SphericalAging.ActualCKJointDefectDimensionLimit
