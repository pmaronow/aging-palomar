module

public import SphericalAging.StationaryRenewalInputs
public import SphericalAging.StationaryRenewalRepresentation
public import SphericalAging.RenewalConvolutionLimit
public import SphericalAging.CompleteMonotoneDerivativeAsymptotics

public section

/-! Genuine existence of the critical stationary amplitude, from the actual
renewal equation and Dirichlet energy, with every normalized derivative limit. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryAmplitude
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization StationaryLogProfile StationaryDirichletTheorem
  StationaryRenewalInputs StationaryRenewalRepresentation
  RenewalConvolutionLimit LipschitzIntegrableDecay
  LogBetaRenewal LogBetaMoments LogBetaRenewalSeries LogBetaConvolutionPowers
  LogBetaRenewalDensityTheorem CompleteMonotoneDerivativeAsymptotics

/-- The actual smoothed stationary profile has the explicit renewal limit.
Every renewal-law, source and remainder hypothesis is proved from the
stationary assumptions, rather than included in this theorem's premises. -/
theorem normalized_smoothed_profile_limit (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    Tendsto (criticalSmoothedProfile a (normalizedProfile q c)) atTop
      (𝓝 ((∫ x : ℝ,criticalRenewalSource p q a c r x)/(∫ y : ℝ,y ∂law (1-2*a) a))) := by
  obtain ⟨MF,MG,LF,LG,hMF,hMG,hF,hG,hGi,hbF,hbG,hLF,hLG,hBot,hEq,_⟩ :=
    normalized_renewal_inputs p β γ q a c r hp h ha0 ha1 hbalance
  obtain ⟨_,_,_,_,hLocal,⟨C,hC,hTail⟩,hULim⟩ :=
    log_beta_renewal_density (show 0<1-2*a by linarith) ha0 (show a<1 by linarith)
  have hU : Measurable (renewalDensity (1-2*a) a) :=
    Measurable.tsum (fun n => (powerDensity_properties (by linarith) ha0 (by linarith) n).1.measurable)
  have hAbsTail (y : ℝ) (hy : 1<y) : |renewalDensity (1-2*a) a y|≤C := by
    rw [abs_of_nonneg (hTail y hy.le).1]
    exact (hTail y hy.le).2
  have hConv := renewal_convolution_tendsto hU (hLocal 1 |>.mono_set Ioc_subset_Icc_self)
    hC hAbsTail hULim hGi hMG hbG (lipschitz_integrable_tendsto_zero_atTop hLG hGi)
  have hRepr (x : ℝ) := log_beta_renewal_representation (show 0<1-2*a by linarith) ha0
    (show a<1 by linarith) _ _ hF hG hGi MF MG hMF hMG hbF hbG hBot hEq x
  have hLim := hConv.congr (fun x => (hRepr x).symm)
  simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hLim

/-- A genuinely positive limiting normalized amplitude exists. Its square
is exactly the actual integral of the renewal source divided by the mean. -/
theorem normalized_critical_amplitude_exists (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ A0 : ℝ,0<A0 ∧
      A0^2=(∫ x : ℝ,criticalRenewalSource p q a c r x)/(∫ y : ℝ,y ∂law (1-2*a) a) ∧
      Tendsto (logProfile a (normalizedProfile q c)) atTop (𝓝 A0) ∧
      Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (𝓝 A0) := by
  let D := logProfile a (normalizedProfile q c)
  let F := criticalSmoothedProfile a (normalizedProfile q c)
  let ell := (∫ x : ℝ,criticalRenewalSource p q a c r x)/(∫ y : ℝ,y ∂law (1-2*a) a)
  obtain ⟨MF,MG,LF,LG,hMF,hMG,hF,hG,hGi,hbF,hbG,hLF,hLG,hBot,hEq,hApprox⟩ :=
    normalized_renewal_inputs p β γ q a c r hp h ha0 ha1 hbalance
  have hFLim := normalized_smoothed_profile_limit p β γ q a c r hp h ha0 ha1 hbalance
  have hSquare : Tendsto (fun x : ℝ => D x^2) atTop (𝓝 ell) := by
    have he := hFLim.sub hApprox
    simp only [sub_zero] at he
    convert he using 1
    funext x
    ring
  obtain ⟨A,d,L,hA,hd,hD,hLower,hLip,hDBot,hEnergy,hInc,_⟩ :=
    stationary_critical_dirichlet p β γ q a c r hp h ha0 ha1 hbalance
  have hLowerSquare : ∀ᶠ x : ℝ in atTop,d^2≤D x^2 := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have hl := hLower x hx
    have hpD := (hD x).1
    change d≤D x at hl
    change 0<D x at hpD
    nlinarith
  have hEll : 0<ell := (sq_pos_of_pos hd).trans_le (ge_of_tendsto hSquare hLowerSquare)
  have hDlim : Tendsto D atTop (𝓝 (Real.sqrt ell)) := by
    have hs := hSquare.sqrt
    apply hs.congr
    intro x
    exact Real.sqrt_sq (le_of_lt (hD x).1)
  have hRaw : Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (𝓝 (Real.sqrt ell)) := by
    apply (hDlim.comp Real.tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    change Real.exp (a*Real.log t)*normalizedProfile q c (Real.exp (Real.log t))=t^a*normalizedProfile q c t
    rw [Real.exp_log ht,Real.rpow_def_of_pos ht]
    congr 1
    rw [mul_comm]
  exact ⟨Real.sqrt ell,Real.sqrt_pos.mpr hEll,Real.sq_sqrt hEll.le,hDlim,hRaw⟩

/-- Full normalized critical amplitude and all-order derivative asymptotics.
The amplitude is derived from the genuine stationary equation and has a
strictly positive lower bound; no amplitude or renewal conclusion is assumed. -/
theorem normalized_critical_amplitude_all_derivatives (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ A0 : ℝ,0<A0 ∧ Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (𝓝 A0) ∧
      (∀ n : ℕ,Tendsto (fun t : ℝ => t^(a+(n:ℝ))*
        ((-1:ℝ)^n*iteratedDeriv n (normalizedProfile q c) t)) atTop
          (𝓝 (A0*(∏ j∈Finset.range n,(a+(j:ℝ)))))) := by
  obtain ⟨A0,hA0,_,_,hAmp⟩ := normalized_critical_amplitude_exists p β γ q a c r hp h ha0 ha1 hbalance
  exact ⟨A0,hA0,hAmp,fun n => normalized_all_order_derivative_asymptotics_product p β γ q c r h hAmp n⟩

end
end SphericalAging.StationaryAmplitude
