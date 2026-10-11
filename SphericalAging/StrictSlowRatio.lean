module

public import SphericalAging.PersistentDefectLimits

public section

/-! The strictly positive slow sector follows from the actual scalar marginality
equation and the preceding selected-root sector, with no margin premise. -/
noncomputable section
open Set
namespace SphericalAging.StrictSlowRatio
open PlateauAlgebra WeightedSlowRatioTheorem

theorem plateau_strict {p : ℕ} {β q : ℝ} (hp : 3≤p)
    (hq : transitionPlateau p≤q)
    (hm : β^2*marginalityPolynomial p q=1)
    (hβ : transitionBetaSquared p<β^2) : transitionPlateau p<q := by
  apply lt_of_le_of_ne hq
  intro he
  rw [←he] at hm
  have ht := transition_beta_marginality hp
  have hG : marginalityPolynomial p (transitionPlateau p)≠0 := by
    intro hh
    rw [hh,mul_zero] at ht
    norm_num at ht
  have hb := mul_right_cancel₀ hG (hm.trans ht.symm)
  exact hβ.ne hb.symm

theorem slowRatio_bounds {p : ℕ} {q : ℝ} (hp : 3≤p) (hq : 0<q) (hq1 : q<1)
    (hqd : transitionPlateau p<q) : 0<slowRatio p q ∧ slowRatio p q<1 := by
  have hp2 : 0<(p:ℝ)-2 := by
    have hh : (3:ℝ)≤p := by exact_mod_cast hp
    linarith
  have hp1 : 0<(p:ℝ)-1 := by linarith
  constructor
  · exact div_pos (mul_pos hp2 (sub_pos.mpr hq1)) hq
  · unfold slowRatio
    apply (div_lt_one hq).2
    unfold transitionPlateau at hqd
    have hh := (div_lt_iff₀ hp1).1 hqd
    nlinarith

end SphericalAging.StrictSlowRatio
