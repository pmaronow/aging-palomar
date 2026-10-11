module

public import SphericalAging.StationaryCriticalRelaxation
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

public section

/-! Literal asymptotic-equivalence versions of the complete critical
relaxation theorem. The weighted limits are converted using actual positive
powers, and every derivative coefficient is proved nonzero. -/
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryAsymptoticEquivalence
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization StationaryCriticalRelaxation

/-- A genuine nonzero weighted limit is the literal source f~At^{-alpha}. -/
theorem raw_power_isEquivalent_of_weighted_limit (f : ℝ → ℝ) (α A : ℝ) (hA : A≠0)
    (h : Tendsto (fun t : ℝ => t^α*f t) atTop (𝓝 A)) :
    (fun t : ℝ => f t) ~[atTop] (fun t : ℝ => A*t^(-α)) := by
  apply isEquivalent_of_tendsto_one
  have hd : Tendsto (fun t : ℝ => (t^α*f t)/A) atTop (𝓝 1) := by
    simpa only [div_self hA] using h.div_const A
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  change (t^α*f t)/A=f t/(A*t^(-α))
  rw [Real.rpow_neg ht.le]
  field_simp [hA,ne_of_gt (Real.rpow_pos_of_pos ht α)]

/-- The exact rising factorial is strictly positive for every natural order. -/
theorem critical_rising_product_positive (a : ℝ) (ha : 0<a) (n : ℕ) :
    0<(∏ j∈Finset.range n,(a+(j:ℝ))) := by
  apply Finset.prod_pos
  intro j _
  exact add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg j)

/-- Literal source asymptotic equivalences, obtained from the full actual
critical-relaxation proof under the normalized stationary inputs. -/
theorem stationary_critical_equivalences_from_normalized (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r) (hq : q<1)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ Aβ : ℝ,0<Aβ ∧
      (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => Aβ*t^(-a)) ∧
      (∀ n : ℕ,1≤n → (fun t : ℝ => (-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
        (fun t : ℝ => (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
      (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a*Aβ)*t^(-(a+1))) := by
  obtain ⟨Aβ,hAβ,hC,hD,hR⟩ := stationary_critical_relaxation_from_normalized p β γ q a c r hp h hq ha0 ha1 hbalance
  refine ⟨Aβ,hAβ,raw_power_isEquivalent_of_weighted_limit _ _ _ hAβ.ne' hC,?_,
    raw_power_isEquivalent_of_weighted_limit _ _ _ (ne_of_gt (mul_pos ha0 hAβ)) hR⟩
  intro n hn
  exact raw_power_isEquivalent_of_weighted_limit _ _ _
    (ne_of_gt (mul_pos hAβ (critical_rising_product_positive a ha0 n))) (hD n hn)

/-- Complete literal manuscript Theorem stationary-critical-amplitude under
exactly (S1)--(S4), with no normalized, renewal or asymptotic conclusion assumed. -/
theorem stationary_critical_equivalences (p : ℕ) (hp : 3≤p) (β γ q a : ℝ) (c r : ℝ → ℝ)
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
      (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => Aβ*t^(-a)) ∧
      (∀ n : ℕ,1≤n → (fun t : ℝ => (-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
        (fun t : ℝ => (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
      (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a*Aβ)*t^(-(a+1))) := by
  have h := normalized_stationary_profile p hp β γ q c r hc1 hr1 hc0 hr0 hderiv hrpos hlim
    hmemory hplateau hqd hq1 hm ν hneg hatom hrep
  exact stationary_critical_equivalences_from_normalized p β γ q a c r hp h hq1 ha0 ha1 hbalance

end
end SphericalAging.StationaryAsymptoticEquivalence
