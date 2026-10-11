module

public import SphericalAging.StationaryAsymptoticEquivalence
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

public section

/-! Complete source critical-relaxation theorem with the exact stationary
input list: the profile's C1 regularity is derived from the actual response
and derivative equation, not added as a separate hypothesis. -/
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryCriticalInputTheorem
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization StationaryAsymptoticEquivalence

/-- Complete literal critical-relaxation theorem under (S1)--(S4). -/
theorem stationary_critical_relaxation_exact_inputs (p : ℕ) (hp : 3≤p) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hr1 : ContDiffOn ℝ 1 r (Ici 0))
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
      (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => Aβ*t^(-a)) ∧
      (∀ n : ℕ,1≤n → (fun t : ℝ => (-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
        (fun t : ℝ => (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
      (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a*Aβ)*t^(-(a+1))) := by
  have hc1 : ContDiffOn ℝ 1 c (Ici 0) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici (0:ℝ))).mpr
    refine ⟨fun t ht => (hderiv t ht).differentiableWithinAt,?_⟩
    apply hr1.continuousOn.neg.congr
    intro t ht
    exact (hderiv t ht).derivWithin (uniqueDiffOn_Ici (0:ℝ) t ht)
  exact stationary_critical_equivalences p hp β γ q a c r hc1 hr1 hc0 hr0 hderiv hrpos hlim
    hmemory hplateau hqd hq1 hm ν hneg hatom hrep ha0 ha1 hbalance

end
end SphericalAging.StationaryCriticalInputTheorem
