module

public import SphericalAging.StationaryPhysicalScaling
public import SphericalAging.StationaryDerivativeRescaling

public section

/-! Complete source Theorem stationary-critical-amplitude: actual physical
profile, every positive-order derivative, and response asymptotics, under
the exact stationary inputs (S1)--(S4) used in the manuscript. -/
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryCriticalRelaxation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization StationaryAmplitude StationaryPhysicalScaling
  StationaryDerivativeRescaling CompleteMonotoneDerivativeAsymptotics

/-- The actual physical response is the negative ordinary derivative of c
on positive lags, reconstructed from the genuine normalized derivative. -/
theorem physical_response_eq_negative_deriv (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (hq : q<1) (t : ℝ) (ht : 0<t) :
    -deriv c t=r t := by
  have he := normalized_physical_iteratedDeriv p β γ q c r h hq ht (n:=1) (by norm_num)
  simp only [iteratedDeriv_one,Nat.cast_one,sub_self,zpow_zero,one_mul] at he
  have hd := (StationaryPatchedProfiles.normalized_profile_hasDerivAt p β γ q c r h
    (t/(1-q)) (div_pos ht (sub_pos.mpr hq))).deriv
  rw [he,hd,neg_neg,normalizedResponse,mul_div_cancel₀ t (ne_of_gt (sub_pos.mpr hq))]

/-- Full physical-lag conclusion from the already-proved normalized
stationary equation. The positive amplitude is constructed by actual renewal,
Dirichlet and Laplace arguments, not assumed. -/
theorem stationary_critical_relaxation_from_normalized (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r) (hq : q<1)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ Aβ : ℝ,0<Aβ ∧
      Tendsto (fun t : ℝ => t^a*(c t-q)) atTop (𝓝 Aβ) ∧
      (∀ n : ℕ,1≤n → Tendsto (fun t : ℝ => t^(a+(n:ℝ))*
        ((-1:ℝ)^n*iteratedDeriv n c t)) atTop
          (𝓝 (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ)))))) ∧
      Tendsto (fun t : ℝ => t^(a+1)*r t) atTop (𝓝 (a*Aβ)) := by
  obtain ⟨A0,hA0,_,_,hAmp⟩ := normalized_critical_amplitude_exists p β γ q a c r hp h ha0 ha1 hbalance
  let Aβ := (1-q)^(1+a)*A0
  have hAβ : 0<Aβ := mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr hq) _) hA0
  have hC := physical_profile_amplitude q a A0 hq c hAmp
  have hDerivs (n : ℕ) (hn : 1≤n) : Tendsto (fun t : ℝ => t^(a+(n:ℝ))*
      ((-1:ℝ)^n*iteratedDeriv n c t)) atTop
        (𝓝 (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))) := by
    simpa only [Aβ,add_comm a 1,risingFactor_eq_prod] using
      physical_all_order_derivative_asymptotics p β γ q c r h hq hAmp (show 0<n by omega)
  have hResponse := hDerivs 1 (by norm_num)
  simp only [Nat.cast_one,pow_one,neg_one_mul,iteratedDeriv_one,
    Finset.prod_range_one,Nat.cast_zero,add_zero] at hResponse
  have hr : Tendsto (fun t : ℝ => t^(a+1)*r t) atTop (𝓝 (a*Aβ)) := by
    have hh : Tendsto (fun t : ℝ => t^(a+1)*(-deriv c t)) atTop (𝓝 (a*Aβ)) := by
      simpa only [mul_comm] using hResponse
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [physical_response_eq_negative_deriv p β γ q c r h hq t ht]
  exact ⟨Aβ,hAβ,hC,hDerivs,hr⟩

/-- Complete manuscript Theorem stationary-critical-amplitude under exactly
the genuine stationary hypotheses (S1)--(S4): stationary regularity/equation,
spectral probability representation with plateau atom, selected marginality,
and the actual Gamma-selected exponent. No normalized, renewal, Dirichlet,
or asymptotic conclusion occurs among the premises. -/
theorem stationary_critical_relaxation (p : ℕ) (hp : 3≤p) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hc1 : ContDiffOn ℝ 1 c (Ici 0)) (hr1 : ContDiffOn ℝ 1 r (Ici 0))
    (hc0 : c 0=1) (hr0 : r 0=1)
    (hderiv : ∀ t : ℝ,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀ t : ℝ,0≤t → 0<r t)
    (hlim : Tendsto c atTop (𝓝 q))
    (hmemory : ∀ t : ℝ,0≤t → -r t=
      -1+∫ s in 0..t,purePhi p (β^2) γ (c (t-s))*r s)
    (hplateau : purePhi p (β^2) γ q*(1-q)=1)
    (hqd : CriticalEndpoint.dynamicalPlateau p≤q) (hq1 : q<1)
    (hm : CriticalEndpoint.marginality p (β^2) q=1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0)=0) (hatom : ν {0}=ENNReal.ofReal q)
    (hrep : ∀ t : ℝ,0≤t → c t=∫ x : ℝ,Real.exp (-x*t) ∂ν)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ Aβ : ℝ,0<Aβ ∧
      Tendsto (fun t : ℝ => t^a*(c t-q)) atTop (𝓝 Aβ) ∧
      (∀ n : ℕ,1≤n → Tendsto (fun t : ℝ => t^(a+(n:ℝ))*
        ((-1:ℝ)^n*iteratedDeriv n c t)) atTop
          (𝓝 (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ)))))) ∧
      Tendsto (fun t : ℝ => t^(a+1)*r t) atTop (𝓝 (a*Aβ)) := by
  have h := normalized_stationary_profile p hp β γ q c r hc1 hr1 hc0 hr0 hderiv hrpos hlim
    hmemory hplateau hqd hq1 hm ν hneg hatom hrep
  exact stationary_critical_relaxation_from_normalized p β γ q a c r hp h hq1 ha0 ha1 hbalance

end
end SphericalAging.StationaryCriticalRelaxation
