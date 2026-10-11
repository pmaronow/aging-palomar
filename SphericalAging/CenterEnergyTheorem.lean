module

public import SphericalAging.NormalizedCenterAMGM
public import SphericalAging.TreeEnergyCeilings

public section

/-! Complete local source Lemma 8.2, including the source real-power
normalization, exact AM--GM identity and equality characterization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace SphericalAging.CenterEnergyTheorem
open ProfileCenterEnergy PlateauAlgebra NormalizedCenterAMGM

theorem source8_2 {p : ℕ} {β ell q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) (H : Profile c r q) (hq1 : q<1)
    (hell : ell=multiplier p β q) :
    Tendsto (fun L : ℝ => c (2*L)) atTop (𝓝 q) ∧
    Tendsto (prefixEnergyLimit p β ell c r) atTop
      (𝓝 ((ell-1)/((p:ℝ)*β)-β*(1-q^p-p*q^(p-1)*(1-q)))) ∧
    (0<q→
      0<centerZ p β q ∧
      ((ell-1)/((p:ℝ)*β)-β*(1-q^p-p*q^(p-1)*(1-q)))/q^((p:ℝ)/2)=
        Real.sqrt (((p:ℝ)-1)/(p:ℝ))*(centerZ p β q+1/centerZ p β q) ∧
      TreeEnergyCeilings.threshold p≤
        ((ell-1)/((p:ℝ)*β)-β*(1-q^p-p*q^(p-1)*(1-q)))/q^((p:ℝ)/2) ∧
      (((ell-1)/((p:ℝ)*β)-β*(1-q^p-p*q^(p-1)*(1-q)))/q^((p:ℝ)/2)=
        TreeEnergyCeilings.threshold p↔β^2*marginalityPolynomial p q=1)) := by
  subst ell
  have he : (multiplier p β q-1)/((p:ℝ)*β)-β*(1-q^p-p*q^(p-1)*(1-q))=
      centerEnergy p β q := rfl
  refine ⟨?_,?_,?_⟩
  · exact H.limit.comp ((tendsto_const_mul_atTop_of_pos
      (show (0:ℝ)<2 by norm_num)).mpr tendsto_id)
  · rw [he]
    exact prefixEnergyLimit_tendsto hp H
  · intro hq
    rw [he]
    refine ⟨centerZ_positive hp hβ hq hq1,
      normalized_center_energy_identity hp hβ hq hq1,?_,?_⟩
    · rw [←sqrt_pow_eq_rpow hq.le p]
      exact normalized_center_energy_lower_bound hp hβ hq hq1
    · rw [←sqrt_pow_eq_rpow hq.le p]
      exact normalized_center_energy_eq_iff hp hβ hq hq1

end SphericalAging.CenterEnergyTheorem
