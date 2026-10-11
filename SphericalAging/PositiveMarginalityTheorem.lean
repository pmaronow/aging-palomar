module

public import SphericalAging.MarginalPlateauSign

public section

/-! Complete local source Lemma 8.3, from the exact preceding finite-age
center ceiling and scalar strict-sign constraints. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.PositiveMarginalityTheorem
open PlateauAlgebra ProfileCenterEnergy NormalizedCenterAMGM MarginalPlateauSign

theorem source8_3 {p : ℕ} {β q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hceiling : ∀L : ℝ,0≤L→
      prefixEnergyLimit p β (multiplier p β q) c r L≤
        TreeEnergyCeilings.threshold p*c (2*L)^((p:ℝ)/2))
    (hsign : ∀x∈Ioo q 1,scalarSignPolynomial p β (multiplier p β q) x<0) :
    β^2*marginalityPolynomial p q=1 ∧ spinodalPlateau p≤q := by
  have htwo : Tendsto (fun L : ℝ => 2*L) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr tendsto_id
  have he := prefixEnergyLimit_tendsto (β:=β) hp H
  have hd : Tendsto (fun L : ℝ => c (2*L)^((p:ℝ)/2)) atTop
      (𝓝 (q^((p:ℝ)/2))) := (H.limit.comp htwo).rpow_const (Or.inl hq.ne')
  have hu : centerEnergy p β q≤TreeEnergyCeilings.threshold p*q^((p:ℝ)/2) := by
    apply le_of_tendsto_of_tendsto he (hd.const_mul (TreeEnergyCeilings.threshold p))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    exact hceiling L hL
  have hden : 0<q^((p:ℝ)/2) := Real.rpow_pos_of_pos hq _
  have hn : centerEnergy p β q/q^((p:ℝ)/2)≤TreeEnergyCeilings.threshold p :=
    (div_le_iff₀ hden).mpr hu
  rw [←sqrt_pow_eq_rpow hq.le p] at hn
  have hm := center_energy_ceiling_forces_marginality hp hβ hq hq1 hn
  exact ⟨hm,marginal_sign_forces_larger_root hp hβ hq hq1 hm hsign⟩

end SphericalAging.PositiveMarginalityTheorem
