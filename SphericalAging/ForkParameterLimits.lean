module

public import SphericalAging.ForkParameterBounds

public section

/-! Source 10.5: the genuine branch limit followed by the age limit,
including the literal ordered normalized limit at marginality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ForkParameterLimits
open ProfileCenterEnergy ForkParameterBounds PlateauAlgebra

theorem reciprocal_branch_tendsto :
    Tendsto (fun K : ℕ => 1/(K:ℝ)) atTop (𝓝 0) := by
  simpa only [one_div,Function.comp_def] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun K : ℕ => (K:ℝ)) atTop atTop)

theorem norm_branch_tendsto {c r : ℝ → ℝ} {q L : ℝ}
    (H : Profile c r q) (hL : 0≤L) :
    Tendsto (fun K : ℕ => forkNorm c K L) atTop (𝓝 (c (2*L))) := by
  have hb : ∀ᶠ K : ℕ in atTop, ‖forkNorm c K L-c (2*L)‖≤1/(K:ℝ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hK
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_error H hK hL).1]
    exact (norm_error H hK hL).2
  have hh := squeeze_zero_norm' hb reciprocal_branch_tendsto
  simpa only [sub_add_cancel,zero_add] using hh.add_const (c (2*L))

theorem energy_branch_tendsto {p : ℕ} {β e q L : ℝ} {c r : ℝ → ℝ}
    (H : Profile c r q) (hβ : 0≤β) (hL : 0≤L)
    (hr : ∀ u, 0<u → 0≤r u) :
    Tendsto (fun K : ℕ => forkEnergy p β e c r K L) atTop
      (𝓝 (prefixEnergy p β e c r L)) := by
  have hb : ∀ᶠ K : ℕ in atTop,
      ‖forkEnergy p β e c r K L-prefixEnergy p β e c r L‖≤
        β*(p:ℝ)*((p:ℝ)-1)/(K:ℝ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hK
    rw [Real.norm_eq_abs]
    exact energy_error H hβ hK hL hr
  have hz : Tendsto (fun K : ℕ => β*(p:ℝ)*((p:ℝ)-1)/(K:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      reciprocal_branch_tendsto.const_mul (β*(p:ℝ)*((p:ℝ)-1))
  have hh := squeeze_zero_norm' hb hz
  simpa only [sub_add_cancel,zero_add] using hh.add_const (prefixEnergy p β e c r L)

theorem profile_antitone {c r : ℝ → ℝ} {q : ℝ}
    (H : Profile c r q) (hr : ∀ u, 0<u → 0≤r u) : AntitoneOn c (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) H.continuous_c
  · intro u hu
    rw [interior_Ici] at hu
    exact (H.fdt u hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    rw [(H.fdt u hu).deriv]
    exact neg_nonpos.mpr (hr u hu)

theorem plateau_le_profile {c r : ℝ → ℝ} {q u : ℝ}
    (H : Profile c r q) (hr : ∀ u, 0<u → 0≤r u) (hu : 0≤u) : q≤c u := by
  apply le_of_tendsto H.limit
  filter_upwards [eventually_ge_atTop u] with v hv
  exact profile_antitone H hr hu (hu.trans hv) hv

theorem fork_norm_bounds {c r : ℝ → ℝ} {q L : ℝ} {K : ℕ}
    (H : Profile c r q) (hr : ∀ u, 0<u → 0≤r u) (hK : 1≤K) (hL : 0≤L) :
    q≤c (2*L) ∧ c (2*L)≤forkNorm c K L ∧ forkNorm c K L≤1 ∧
      1/(K:ℝ)≤forkNorm c K L := by
  have hK0 : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hK1 : (1:ℝ)≤K := by exact_mod_cast hK
  have hi : 0≤1/(K:ℝ) := div_nonneg zero_le_one hK0.le
  have hi1 : 1/(K:ℝ)≤1 := (div_le_one hK0).mpr hK1
  have hc := H.bounds (2*L) (by positivity)
  refine ⟨plateau_le_profile H hr (by positivity),?_,?_,?_⟩
  · linarith [(norm_error H hK hL).1]
  · unfold forkNorm
    nlinarith
  · unfold forkNorm
    nlinarith

theorem normalized_branch_tendsto {p : ℕ} {β e q L : ℝ} {c r : ℝ → ℝ}
    (H : Profile c r q) (hβ : 0≤β) (hL : 0≤L) (hq : 0<q)
    (hr : ∀ u, 0<u → 0≤r u) :
    Tendsto (fun K : ℕ => forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2))
      atTop (𝓝 (prefixEnergy p β e c r L/(c (2*L))^((p:ℝ)/2))) := by
  have hd : 0<c (2*L) := hq.trans_le (plateau_le_profile H hr (by positivity))
  exact (energy_branch_tendsto H hβ hL hr).div
    ((norm_branch_tendsto H hL).rpow_const (Or.inl hd.ne'))
    (Real.rpow_pos_of_pos hd _).ne'

theorem prefix_age_limits {p : ℕ} {β ell e q : ℝ} {c r : ℝ → ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq1 : q<1)
    (hell : ell=multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β)) :
    Tendsto (fun L : ℝ => c (2*L)) atTop (𝓝 q) ∧
    Tendsto (prefixEnergy p β e c r) atTop
      (𝓝 (e-β*(1-q^p-p*q^(p-1)*(1-q)))) := by
  subst e
  exact ⟨(CenterEnergyTheorem.source8_2 hp hβ H hq1 hell).1,
    (CenterEnergyTheorem.source8_2 hp hβ H hq1 hell).2.1⟩

theorem normalized_age_tendsto {p : ℕ} {β ell e q : ℝ} {c r : ℝ → ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β)) :
    Tendsto (fun L : ℝ => prefixEnergy p β e c r L/(c (2*L))^((p:ℝ)/2))
      atTop (𝓝 ((e-β*(1-q^p-p*q^(p-1)*(1-q)))/q^((p:ℝ)/2))) := by
  have hs := prefix_age_limits hp hβ H hq1 hell he
  exact hs.2.div (hs.1.rpow_const (Or.inl hq.ne')) (Real.rpow_pos_of_pos hq _).ne'

theorem ordered_normalization {p : ℕ} {β ell e q : ℝ} {c r : ℝ → ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀ u, 0<u → 0≤r u)
    (hm : β^2*marginalityPolynomial p q=1) :
    (∀ L : ℝ, 0≤L →
      Tendsto (fun K : ℕ => forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2))
        atTop (𝓝 (prefixEnergy p β e c r L/(c (2*L))^((p:ℝ)/2)))) ∧
    Tendsto (fun L : ℝ =>
      limUnder atTop (fun K : ℕ => forkEnergy p β e c r K L/(forkNorm c K L)^((p:ℝ)/2)))
      atTop (𝓝 (TreeEnergyCeilings.threshold p)) := by
  have hK := fun (L : ℝ) (hL : 0≤L) =>
    normalized_branch_tendsto (p:=p) (e:=e) (L:=L) H hβ.le hL hq hr
  refine ⟨hK,?_⟩
  have hs := normalized_age_tendsto hp hβ H hq hq1 hell he
  have hsat := ((CenterEnergyTheorem.source8_2 hp hβ H hq1 hell).2.2 hq).2.2.2.mpr hm
  rw [←he] at hsat
  rw [hsat] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  exact (hK L hL).limUnder_eq.symm

end SphericalAging.ForkParameterLimits
