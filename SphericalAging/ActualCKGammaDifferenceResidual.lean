module

public import SphericalAging.ActualCKGammaCompactDefect

public section

/-! The actual Γ CK row between two terminal times, with the same Brownian
waiting time. Its literal defect is the difference of two checked Γ row
residuals, so it vanishes uniformly on compact causal triples. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKGammaDifferenceResidual
open FiniteModel ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral ActualCKGammaSlopeResidual
  ActualCKGammaIntegralResidual ActualCKGammaCompactDefect ActualCKGammaUniformResidual
  AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Integrability of the true CK Γ slope follows from the physical drift and
its derived integrable error, without an integrability premise. -/
theorem ckGammaSlope_intervalIntegrable (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (s t T : ℝ≥0) (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    IntervalIntegrable (fun u : ℝ => ckGammaSlope (by omega : N≠0) p β u.toNNReal s)
      volume (s : ℝ) (t : ℝ) := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let f := fun u : ℝ => ∫ q : ModelSample N p,
    gammaDriftField β (N+1) (modelRadius_pos N) s (u,q) ∂AnnealedModelLaw.law N p
  have hf : Integrable f ν := (gammaDriftField_integrable (p := p)
    (by omega : 0<N) (by omega : 0<p) β (N+1) (modelRadius_pos N)
      (modelRadius_sq N) s t).integral_prod_left
  have he := (actual_gamma_slope_error_integrable_bound hN hp β t s T hst htT hT).1
  have hg : Integrable (fun u : ℝ => ckGammaSlope (by omega : N≠0) p β u.toNNReal s) ν := by
    convert hf.sub he using 1
    funext u
    dsimp only [f,Pi.sub_apply]
    ring
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (s : ℝ)≤t from hst)).mpr hg

@[expose] def gammaDifferenceResidual (hN : N≠0) (p : ℕ) (β : ℝ≥0) (t a s : ℝ≥0) : ℝ :=
  annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) t s-
    annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) a s-
      ∫ u in (a : ℝ)..(t : ℝ),ckGammaSlope hN p β u.toNNReal s

/-- Exact two-terminal subtraction of the actual finite-dimensional Γ rows. -/
theorem gammaDifferenceResidual_eq (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (t a s T : ℝ≥0) (hsa : s≤a) (hat : a≤t) (htT : t≤T) (hT : 0<T) :
    gammaDifferenceResidual (by omega : N≠0) p β t a s=
      gammaIntegralResidual (by omega : N≠0) p β t s-
        gammaIntegralResidual (by omega : N≠0) p β a s := by
  have hi := ckGammaSlope_intervalIntegrable hN hp β s t T (hsa.trans hat) htT hT
  have hsaR : (s : ℝ)≤a := hsa
  have hatR : (a : ℝ)≤t := hat
  have hia := hi.mono_set (by
    rw [uIcc_of_le hsaR,uIcc_of_le (hsaR.trans hatR)]
    exact Icc_subset_Icc le_rfl hatR)
  have hiat := hi.mono_set (by
    rw [uIcc_of_le hatR,uIcc_of_le (hsaR.trans hatR)]
    exact Icc_subset_Icc hsaR le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hia hiat
  unfold gammaDifferenceResidual gammaIntegralResidual
  linarith

/-- The genuine two-terminal Γ defect is uniformly small on causal triples. -/
theorem actual_gamma_difference_residual_uniform (hN : 3≤N) (hp : 3≤p)
    (β T : ℝ≥0) (hT : 0<T) (t a s : ℝ≥0) (hsa : s≤a) (hat : a≤t) (htT : t≤T) :
    |gammaDifferenceResidual (by omega : N≠0) p β t a s|≤
      2*gammaCompactDefectCeiling p β T N := by
  rw [gammaDifferenceResidual_eq hN hp β t a s T hsa hat htT hT]
  exact (abs_sub _ _).trans (by
    have h1 := actual_gamma_integral_residual_uniform hN hp β T hT t s (hsa.trans hat) htT
    have h2 := actual_gamma_integral_residual_uniform hN hp β T hT a s hsa (hat.trans htT)
    linarith)

/-- The full triple-indexed finite-N off-diagonal Γ row converges uniformly. -/
theorem actual_gamma_difference_residual_tendstoUniformlyOn (hp : 3≤p)
    (β T : ℝ≥0) (hT : 0<T) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℝ≥0×(ℝ≥0×ℝ≥0) =>
      gammaDifferenceResidual (N := n+3) (by omega : n+3≠0) p β z.1 z.2.1 z.2.2)
      (fun _ => (0 : ℝ)) atTop {z | z.2.2≤z.2.1 ∧ z.2.1≤z.1 ∧ z.1≤T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have htend : Tendsto (fun n : ℕ => 2*gammaCompactDefectCeiling p β T (n+3)) atTop (𝓝 0) :=
    by simpa only [mul_zero] using (gammaCompactDefectCeiling_tendsto_zero p β T).const_mul 2
  filter_upwards [htend.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [Real.dist_eq,zero_sub,abs_neg]
  exact (actual_gamma_difference_residual_uniform (by omega : 3≤n+3) hp β T hT
    z.1 z.2.1 z.2.2 hz.1 hz.2.1 hz.2.2).trans_lt hn

end SphericalAging.ActualCKGammaDifferenceResidual
