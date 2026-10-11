module

public import SphericalAging.ActualCKSource33Suprema

public section

/-! Source 3.3 is derived from the literal finite-dimensional model: the
expected causal supremum of squared C error plus first-power Γ error
vanishes, and the sum of absolute errors converges uniformly in probability.
No finite-N concentration, mean bridge or CK limit is assumed. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualCKSource33Convergence
open ActualCKSource33Suprema ActualCKCompactPathConvergence ActualCKPathSupremumMeasurability
  ActualCKMeanKernelConvergence ActualCompactCKMemoryLimit CompactKernelMemoryLimit
  AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem correlationCKSup_firstMoment_le_sqrt (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    (∫ω,correlationCKSup N p β (N+1) (modelRadius_pos N) d T ω ∂AnnealedModelLaw.law N p)≤
      Real.sqrt (∫ω,(correlationCKSup N p β (N+1) (modelRadius_pos N) d T ω)^2 ∂AnnealedModelLaw.law N p) := by
  have hh := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq (AnnealedModelLaw.law N p)
    (correlationCKSup N p β (N+1) (modelRadius_pos N) d T)
      (correlationCKSup_memLp_two hN hp β d hd T)
  simp only [probReal_univ,one_mul] at hh
  exact (Real.le_sqrt (integral_nonneg_of_ae (correlationCKSup_nonneg β (N+1) (modelRadius_pos N) d hd T))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr hh

 theorem actual_correlation_ck_compact_firstMoment_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ω,correlationCKSup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω
      ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  have hu := (actual_correlation_ck_compact_secondMoment_tendsto_zero dim hdim hp β hβ d hd T).sqrt
  simp only [Real.sqrt_zero] at hu
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg_of_ae
    (correlationCKSup_nonneg β (dim n+1) (modelRadius_pos (dim n)) d hd T))) _ hu
  filter_upwards [hdim.eventually (eventually_ge_atTop 1)] with n hn
  exact correlationCKSup_firstMoment_le_sqrt hn (by omega : 0<p) β d hd T

 theorem actual_source33_expected_sup_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ω,bridgeExpectationSup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω
      ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  have hu := (actual_correlation_ck_compact_secondMoment_tendsto_zero dim hdim hp β hβ d hd T).add
    (actual_gamma_ck_compact_firstMoment_tendsto_zero dim hdim hp β hβ d hd T)
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg_of_ae
    ((bridgeSup_bounds β (dim n+1) (modelRadius_pos (dim n)) d hd T).mono (fun _ h => h.1)))) _ hu
  filter_upwards [hdim.eventually (eventually_ge_atTop 1)] with n hn
  have hc := (correlationCKSup_memLp_two hn (by omega : 0<p) β d hd T).integrable_sq
  have hg := (gammaCKSup_memLp_two hn (by omega : 0<p) β d hd T).integrable (by norm_num)
  have hh := integral_mono_ae (bridgeExpectationSup_integrable hn (by omega : 0<p) β d hd T)
    (hc.add hg) ((bridgeSup_bounds β (dim n+1) (modelRadius_pos (dim n)) d hd T).mono (fun _ h => h.2.1))
  simp only [Pi.add_apply] at hh
  rw [integral_add hc hg] at hh
  exact hh

 theorem actual_source33_absolute_expected_sup_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ω,bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω
      ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  have hu := (actual_correlation_ck_compact_firstMoment_tendsto_zero dim hdim hp β hβ d hd T).add
    (actual_gamma_ck_compact_firstMoment_tendsto_zero dim hdim hp β hβ d hd T)
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg_of_ae
    ((bridgeSup_bounds β (dim n+1) (modelRadius_pos (dim n)) d hd T).mono (fun _ h => h.2.2.1)))) _ hu
  filter_upwards [hdim.eventually (eventually_ge_atTop 1)] with n hn
  have hc := (correlationCKSup_memLp_two hn (by omega : 0<p) β d hd T).integrable (by norm_num)
  have hg := (gammaCKSup_memLp_two hn (by omega : 0<p) β d hd T).integrable (by norm_num)
  have hh := integral_mono_ae (bridgeProbabilitySup_integrable hn (by omega : 0<p) β d hd T)
    (hc.add hg) ((bridgeSup_bounds β (dim n+1) (modelRadius_pos (dim n)) d hd T).mono (fun _ h => h.2.2.2))
  simp only [Pi.add_apply] at hh
  rw [integral_add hc hg] at hh
  exact hh

 theorem actual_source33_probability_le_expected_sup (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    (AnnealedModelLaw.law N p).real {ω | ε<bridgeProbabilitySup N p β (N+1) (modelRadius_pos N) d T ω}≤
      (∫ω,bridgeProbabilitySup N p β (N+1) (modelRadius_pos N) d T ω ∂AnnealedModelLaw.law N p)/ε := by
  have hh := mul_meas_ge_le_integral_of_nonneg
    ((bridgeSup_bounds β (N+1) (modelRadius_pos N) d hd T).mono (fun _ h => h.2.2.1))
      (bridgeProbabilitySup_integrable hN hp β d hd T) ε
  have hm : (AnnealedModelLaw.law N p).real {ω | ε<bridgeProbabilitySup N p β (N+1) (modelRadius_pos N) d T ω}≤
      (AnnealedModelLaw.law N p).real {ω | ε≤bridgeProbabilitySup N p β (N+1) (modelRadius_pos N) d T ω} :=
    measureReal_mono (fun ω h => by
      change ε<bridgeProbabilitySup N p β (N+1) (modelRadius_pos N) d T ω at h
      change ε≤bridgeProbabilitySup N p β (N+1) (modelRadius_pos N) d T ω
      exact le_of_lt h)
  apply (le_div_iff₀ hε).mpr
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hm hε.le).trans hh

 theorem actual_source33_probability_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0)
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (AnnealedModelLaw.law (dim n) p).real
      {ω | ε<bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω}) atTop (𝓝 0) := by
  have hu := (actual_source33_absolute_expected_sup_tendsto_zero dim hdim hp β hβ d hd T).div_const ε
  simp only [zero_div] at hu
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hu
  filter_upwards [hdim.eventually (eventually_ge_atTop 1)] with n hn
  exact actual_source33_probability_le_expected_sup hn (by omega : 0<p) β d hd T hε

 theorem actual_source33_ennreal_probability_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0)
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => AnnealedModelLaw.law (dim n) p
      {ω | ε<bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω}) atTop (𝓝 0) := by
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (actual_source33_probability_tendsto_zero dim hdim hp β hβ d hd T hε)
  change Tendsto (fun n => ENNReal.ofReal ((AnnealedModelLaw.law (dim n) p).real
    {ω | ε<bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω})) atTop (𝓝 (ENNReal.ofReal 0)) at hh
  have he : (fun n => ENNReal.ofReal ((AnnealedModelLaw.law (dim n) p).real
    {ω | ε<bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω}))=
      fun n => AnnealedModelLaw.law (dim n) p
        {ω | ε<bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω} := by
    funext n
    exact ofReal_measureReal (μ:=AnnealedModelLaw.law (dim n) p) (s:=
      {ω | ε<bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω})
  rw [he] at hh
  simpa only [ENNReal.ofReal_zero] using hh

end SphericalAging.ActualCKSource33Convergence
