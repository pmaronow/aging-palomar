module

public import SphericalAging.SelectedSectorTheorem

public section

/-! The exact scalar alternatives and positive energy correction in
Remark 8.7. The intermediate interval is not classified from below. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SphericalAging.RemarkIntermediateTemperature
open Set Filter PlateauAlgebra AllTemperatureTheorem CKSpecification
open scoped Topology

theorem marginal_root_lt_transition {p : ℕ} {β q : ℝ} (hp : 3≤p)
    (hq : q∈Ico (spinodalPlateau p) 1)
    (hm : β^2*marginalityPolynomial p q=1)
    (hb : β^2<transitionBetaSquared p) : q<transitionPlateau p := by
  by_contra hn
  have hle : transitionPlateau p≤q := le_of_not_gt hn
  have hG := (marginalityPolynomial_strictAntiOn hp).antitoneOn
    ⟨(spinodal_lt_transition hp).le,(transition_plateau_lt_one hp).le⟩
    ⟨hq.1,hq.2.le⟩ hle
  have hGp : 0<marginalityPolynomial p (transitionPlateau p) := by
    unfold marginalityPolynomial
    exact mul_pos (mul_pos (mul_pos (spin_positive hp) (spin_minus_one_positive hp))
      (pow_pos (transition_plateau_pos hp) _)) (sq_pos_of_pos (sub_pos.mpr (transition_plateau_lt_one hp)))
  have hu := mul_le_mul_of_nonneg_left hG (sq_nonneg β)
  have hs := mul_lt_mul_of_pos_right hb hGp
  rw [hm] at hu
  rw [transition_beta_marginality hp] at hs
  linarith

theorem intermediate_energy_correction {p : ℕ} {β q : ℝ} (hp : 3≤p)
    (hβ : 0<β) (hq : q∈Ico (spinodalPlateau p) 1)
    (hm : β^2*marginalityPolynomial p q=1)
    (hb : β^2<transitionBetaSquared p) :
    clusterEnergy p β q=β+
      q*((p:ℝ)-2-((p:ℝ)-1)*q)/((p:ℝ)*β*((p:ℝ)-1)*(1-q)^2) ∧
      β<clusterEnergy p β q := by
  have hq0 : 0<q := (spinodal_plateau_pos hp).trans_le hq.1
  have hqd := marginal_root_lt_transition hp hq hm hb
  have hp0 := (spin_positive hp).ne'
  have hp1 := (spin_minus_one_positive hp).ne'
  have hgap : 1-q≠0 := (sub_pos.mpr hq.2).ne'
  have heq : clusterEnergy p β q=β+
      q*((p:ℝ)-2-((p:ℝ)-1)*q)/((p:ℝ)*β*((p:ℝ)-1)*(1-q)^2) := by
    rw [cluster_energy_decomposition hp hβ.ne' (ne_of_lt hq.2),pow_pred_relation hp]
    unfold marginalityPolynomial at hm
    field_simp [hp0,hp1,hβ.ne',hgap]
    nlinarith [congrArg (fun y : ℝ => y*q) hm]
  refine ⟨heq,?_⟩
  have hnum : 0<(p:ℝ)-2-((p:ℝ)-1)*q := by
    have ht := mul_lt_mul_of_pos_left hqd (spin_minus_one_positive hp)
    rw [transition_linear_identity hp] at ht
    linarith
  have hcor : 0<q*((p:ℝ)-2-((p:ℝ)-1)*q)/((p:ℝ)*β*((p:ℝ)-1)*(1-q)^2) := by
    exact div_pos (mul_pos hq0 hnum)
      (mul_pos (mul_pos (mul_pos (spin_positive hp) hβ) (spin_minus_one_positive hp))
        (sq_pos_of_pos (sub_pos.mpr hq.2)))
  rw [heq]
  linarith

theorem zero_branch_multiplier_energy {p : ℕ} {β : ℝ} (hp : 3≤p) (hβ : 0<β) :
    multiplier p β 0=1+β^2*p ∧ clusterEnergy p β 0=β := by
  have hp1 : p-1≠0 := by omega
  constructor
  · simp [multiplier,hp1]
  · unfold clusterEnergy
    simp only [multiplier,sub_zero,one_div_one,zero_pow hp1,sub_zero,add_sub_cancel_left]
    field_simp [(spin_positive hp).ne',hβ.ne']

end SphericalAging.RemarkIntermediateTemperature
