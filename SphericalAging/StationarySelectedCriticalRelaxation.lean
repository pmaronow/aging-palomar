module

public import SphericalAging.StationaryCriticalInputTheorem
public import SphericalAging.CriticalExponent

public section

/-! Complete stationary critical relaxation, constructing the unique exponent
from the actual selected plateau rather than taking the exponent as input. -/
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationarySelectedCriticalRelaxation
noncomputable section
open StationaryNormalization

/-- The actual stationary assumptions construct both the unique critical
exponent and a positive amplitude for all three literal asymptotic clauses. -/
theorem stationary_selected_critical_relaxation (p : ℕ) (hp : 3≤p) (β γ q : ℝ) (c r : ℝ → ℝ)
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
 :
    ∃! a : ℝ,a∈Ioo 0 (1/2) ∧
      CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q ∧
      ∃ Aβ : ℝ,0<Aβ ∧
        (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => Aβ*t^(-a)) ∧
        (∀ n : ℕ,1≤n → (fun t : ℝ => (-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
          (fun t : ℝ => (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
        (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a*Aβ)*t^(-(a+1))) := by
  obtain ⟨a,ha,hunique⟩ := CriticalExponent.selected_critical_exponent_exists_unique p hp q hqd hq1
  refine ⟨a,⟨ha.1,ha.2,?_⟩,?_⟩
  · exact StationaryCriticalInputTheorem.stationary_critical_relaxation_exact_inputs p hp β γ q a c r
      hr1 hc0 hr0 hderiv hrpos hlim hmemory hplateau hqd hq1 hm ν hneg hatom hrep
      ha.1.1 ha.1.2 ha.2
  · intro b hb
    exact hunique b ⟨hb.1,hb.2.1⟩

end
end SphericalAging.StationarySelectedCriticalRelaxation
