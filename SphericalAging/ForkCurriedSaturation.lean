module

public import SphericalAging.ForkParameterLimits
public import SphericalAging.CurriedLimitTransfer
public import SphericalAging.ExternalFieldElementaryPenalty

public section

/-! The literal marginal stationary fork energy saturates the algorithmic
threshold in the correct branch-then-length order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ForkCurriedSaturation
open Set Filter ProfileCenterEnergy ForkParameterBounds ForkParameterLimits
  CurriedLimitTransfer
open scoped Topology

theorem actual_ordered_threshold_limit {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1) :
    Tendsto (fun z : ℝ×ℕ => forkEnergy p β e c r z.2 z.1/
      (forkNorm c z.2 z.1)^((p:ℝ)/2)) (atTop.curry atTop)
      (𝓝 (ExternalFieldElementaryPenalty.thresholdEnergy p)) := by
  have ho := ordered_normalization hp hβ H hq hq1 hell he hr hm
  have hi : ∀ᶠL : ℝ in atTop,Tendsto
      (fun K : ℕ => forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2))
      atTop (𝓝 (limUnder atTop (fun K : ℕ =>
        forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2)))) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [(ho.1 L hL).limUnder_eq]
    exact ho.1 L hL
  have heq : TreeEnergyCeilings.threshold p=ExternalFieldElementaryPenalty.thresholdEnergy p := rfl
  rw [heq] at ho
  exact tendsto_curried_of_iterated_limits hi ho.2

end SphericalAging.ForkCurriedSaturation
