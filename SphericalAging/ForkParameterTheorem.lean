module

public import SphericalAging.ForkParameterLimits

public section

/-! Complete local source Lemma 10.5, with the actual finite K/L
parameters, quantitative errors, age limits and ordered saturation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.ForkParameterTheorem
open ProfileCenterEnergy ForkParameterBounds ForkParameterLimits PlateauAlgebra

theorem source10_5 {p : ℕ} {β ell e q : ℝ} {c r : ℝ → ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0≤q) (hq1 : q<1)
    (hell : ell=multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀ u, 0<u → 0≤r u) :
    (∀ K : ℕ, 1≤K → ∀ L : ℝ, 0≤L →
      (0≤forkNorm c K L-c (2*L) ∧ forkNorm c K L-c (2*L)≤1/(K:ℝ)) ∧
      |forkEnergy p β e c r K L-prefixEnergy p β e c r L|≤β*(p:ℝ)*((p:ℝ)-1)/(K:ℝ)) ∧
    (Tendsto (fun L : ℝ => c (2*L)) atTop (𝓝 q) ∧
      Tendsto (prefixEnergy p β e c r) atTop
        (𝓝 (e-β*(1-q^p-p*q^(p-1)*(1-q))))) ∧
    (0<q → β^2*marginalityPolynomial p q=1 →
      (∀ L : ℝ, 0≤L →
        Tendsto (fun K : ℕ => forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2))
          atTop (𝓝 (prefixEnergy p β e c r L/(c (2*L))^((p:ℝ)/2)))) ∧
      Tendsto (fun L : ℝ =>
        limUnder atTop (fun K : ℕ => forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2)))
        atTop (𝓝 (TreeEnergyCeilings.threshold p))) := by
  refine ⟨?_,prefix_age_limits hp hβ H hq1 hell he,?_⟩
  · intro K hK L hL
    exact ⟨norm_error H hK hL,energy_error H hβ.le hK hL hr⟩
  · intro hqpos hm
    exact ordered_normalization hp hβ H hqpos hq1 hell he hr hm

end SphericalAging.ForkParameterTheorem
