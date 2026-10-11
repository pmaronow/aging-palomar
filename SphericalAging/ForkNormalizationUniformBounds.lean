module

public import SphericalAging.ForkCurriedSaturation
public import SphericalAging.ForkNormalizedEnergy

public section

/-! Actual positive-plateau normalization bounds are uniform in branch count
and fork age. They discharge the radius and energy comparison assumptions
in the general-spin transfer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ForkNormalizationUniformBounds
open Set Filter ProfileCenterEnergy ForkParameterBounds ForkParameterLimits
  ForkNormalizedEnergy ForkEnergyComparison
open scoped Topology

theorem positive_normalization_bounds (p : ℕ) {q Q : ℝ}
    (hq : 0<q) (hqQ : q≤Q) :
    (0≤Q^(-((p:ℝ)/2)) ∧ Q^(-((p:ℝ)/2))≤q^(-((p:ℝ)/2))) ∧
    (Real.sqrt Q)⁻¹≤(Real.sqrt q)⁻¹ ∧ comparison p Q≤comparison p q := by
  have hQ : 0<Q := hq.trans_le hqQ
  have hr : (Real.sqrt Q)⁻¹≤(Real.sqrt q)⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.mpr hQ) (Real.sqrt_pos.mpr hq)).mpr
      (Real.sqrt_le_sqrt hqQ)
  refine ⟨⟨Real.rpow_nonneg hQ.le _,Real.rpow_le_rpow_of_nonpos hq hqQ (neg_nonpos.mpr (by positivity))⟩,hr,?_⟩
  unfold comparison comparisonConstant
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr (p-1))
      (Nat.cast_nonneg p)) (Real.sqrt_nonneg _)

theorem profile_fork_normalization_bounds {p : ℕ} {q L : ℝ} {c r : ℝ→ℝ} {K : ℕ}
    (H : Profile c r q) (hq : 0<q) (hr : ∀u,0<u→0≤r u)
    (hK : 1≤K) (hL : 0≤L) :
    (0<forkNorm c K L ∧ forkNorm c K L≤1) ∧
    (0≤(forkNorm c K L)^(-((p:ℝ)/2)) ∧
      (forkNorm c K L)^(-((p:ℝ)/2))≤q^(-((p:ℝ)/2))) ∧
    (Real.sqrt (forkNorm c K L))⁻¹≤(Real.sqrt q)⁻¹ ∧
      comparison p (forkNorm c K L)≤comparison p q := by
  have hb := fork_norm_bounds H hr hK hL
  exact ⟨⟨hq.trans_le (hb.1.trans hb.2.1),hb.2.2.1⟩,
    positive_normalization_bounds p hq (hb.1.trans hb.2.1)⟩

theorem profile_fork_saturation {Θ : Type*} {l : Filter Θ}
    {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    (L : Θ→ℝ) (K : Θ→ℕ) (hL : ∀a,0≤L a) (hK : ∀a,1≤K a)
    (hLK : Tendsto (fun a => (L a,K a)) l (atTop.curry atTop)) :
    Tendsto (fun a => (forkNorm c (K a) (L a))^(-((p:ℝ)/2))*
      forkEnergy p β e c r (K a) (L a)) l
      (𝓝 (ExternalFieldElementaryPenalty.thresholdEnergy p)) := by
  have hs := (ForkCurriedSaturation.actual_ordered_threshold_limit hp hβ H hq hq1
    hell he hr hm).comp hLK
  apply hs.congr'
  exact Eventually.of_forall fun a => by
    have hQ := (profile_fork_normalization_bounds (p:=p) H hq hr (hK a) (hL a)).1.1
    change forkEnergy p β e c r (K a) (L a)/(forkNorm c (K a) (L a))^((p:ℝ)/2)=
      (forkNorm c (K a) (L a))^(-((p:ℝ)/2))*forkEnergy p β e c r (K a) (L a)
    rw [Real.rpow_neg hQ.le,div_eq_mul_inv]
    ring

end SphericalAging.ForkNormalizationUniformBounds
