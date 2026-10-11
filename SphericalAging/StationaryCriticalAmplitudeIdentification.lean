module

public import SphericalAging.StationarySelectedCriticalRelaxation

public section

/-! Exact mathematical amplitude identification in source Remark16.2,
from the actual stationary inputs and actual normalized renewal limit. -/
open Set Filter MeasureTheory Asymptotics
open scoped Topology ENNReal NNReal
namespace SphericalAging.StationaryCriticalAmplitudeIdentification
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization StationaryAmplitude StationaryPhysicalScaling
open StationaryLogProfile StationaryAsymptoticEquivalence StationaryRenewalInputs

/-- The source Gamma relation determines the exponent from its parameter
alone; different profiles with the same parameter have the same exponent. -/
theorem critical_exponent_depends_only_on_parameter {a b θ : ℝ}
    (ha : a∈Ioo 0 (1/2)) (hb : b∈Ioo 0 (1/2))
    (hA : CriticalEndpoint.exponentCoefficient a=θ)
    (hB : CriticalEndpoint.exponentCoefficient b=θ) : a=b :=
  CriticalExponent.exponentCoefficient_strictAntiOn.injOn
    ⟨ha.1.le,ha.2⟩ ⟨hb.1.le,hb.2⟩ (hA.trans hB.symm)

/-- Exact source Remark16.2: the true exponent is selected by p,q; the true
positive normalized amplitude is the actual logarithmic-profile limit and
square root of the actual renewal-source mass divided by its mean; the true
physical amplitude is exactly (1-q)^(1+a) times that normalized amplitude.
No amplitude, renewal, normalized-profile or limit conclusion is assumed. -/
theorem stationary_critical_amplitude_identification (p : ℕ) (hp : 3≤p)
    (β γ q : ℝ) (c r : ℝ → ℝ) (hr1 : ContDiffOn ℝ 1 r (Ici 0))
    (hc0 : c 0=1) (hr0 : r 0=1)
    (hderiv : ∀t : ℝ,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀t : ℝ,0≤t → 0<r t) (hlim : Tendsto c atTop (𝓝 q))
    (hmemory : ∀t : ℝ,0≤t → -r t=
      -1+∫s in 0..t,purePhi p (β^2) γ (c (t-s))*r s)
    (hplateau : purePhi p (β^2) γ q*(1-q)=1)
    (hqd : CriticalEndpoint.dynamicalPlateau p≤q) (hq1 : q<1)
    (hm : CriticalEndpoint.marginality p (β^2) q=1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0)=0) (hatom : ν {0}=ENNReal.ofReal q)
    (hrep : ∀t : ℝ,0≤t → c t=∫x : ℝ,Real.exp (-x*t) ∂ν) :
    ∃a A0 : ℝ,a∈Ioo 0 (1/2) ∧
      CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q ∧
      (∀b∈Ioo (0:ℝ) (1/2),CriticalEndpoint.exponentCoefficient b=CriticalEndpoint.relaxationParameter p q → b=a) ∧
      0<A0 ∧
      A0^2=(∫x : ℝ,criticalRenewalSource p q a c r x)/(∫y : ℝ,y ∂LogBetaRenewal.law (1-2*a) a) ∧
      A0=Real.sqrt ((∫x : ℝ,criticalRenewalSource p q a c r x)/(∫y : ℝ,y ∂LogBetaRenewal.law (1-2*a) a)) ∧
      Tendsto (logProfile a (normalizedProfile q c)) atTop (𝓝 A0) ∧
      Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (𝓝 A0) ∧
      0<(1-q)^(1+a)*A0 ∧
      Tendsto (fun t : ℝ => t^a*(c t-q)) atTop (𝓝 ((1-q)^(1+a)*A0)) ∧
      (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => ((1-q)^(1+a)*A0)*t^(-a)) := by
  have hc1 : ContDiffOn ℝ 1 c (Ici 0) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici (0:ℝ))).mpr
    refine ⟨fun t ht => (hderiv t ht).differentiableWithinAt,?_⟩
    apply hr1.continuousOn.neg.congr
    intro t ht
    exact (hderiv t ht).derivWithin (uniqueDiffOn_Ici (0:ℝ) t ht)
  have h := normalized_stationary_profile p hp β γ q c r hc1 hr1 hc0 hr0 hderiv hrpos hlim
    hmemory hplateau hqd hq1 hm ν hneg hatom hrep
  obtain ⟨a,ha,hunique⟩ := CriticalExponent.selected_critical_exponent_exists_unique p hp q hqd hq1
  obtain ⟨A0,hA0,hSquare,hLog,hRaw⟩ := normalized_critical_amplitude_exists p β γ q a c r hp h ha.1.1 ha.1.2 ha.2
  have hSqrt : A0=Real.sqrt ((∫x : ℝ,criticalRenewalSource p q a c r x)/(∫y : ℝ,y ∂LogBetaRenewal.law (1-2*a) a)) := by
    rw [←hSquare]
    exact (Real.sqrt_sq hA0.le).symm
  have hPhysical := physical_profile_amplitude q a A0 hq1 c hRaw
  have hAβ : 0<(1-q)^(1+a)*A0 := mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr hq1) _) hA0
  refine ⟨a,A0,ha.1,ha.2,fun b hb hbalance => hunique b ⟨hb,hbalance⟩,
    hA0,hSquare,hSqrt,hLog,hRaw,hAβ,hPhysical,?_⟩
  exact raw_power_isEquivalent_of_weighted_limit _ _ _ hAβ.ne' hPhysical

end
end SphericalAging.StationaryCriticalAmplitudeIdentification
