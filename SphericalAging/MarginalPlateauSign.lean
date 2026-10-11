module

public import SphericalAging.CenterEnergyTheorem

public section

/-! Exclusion of the smaller marginal plateau directly from the actual
preceding scalar strict-sign constraint, using two mean-value arguments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set
namespace SphericalAging.MarginalPlateauSign
open PlateauAlgebra

@[expose] def signSlope (p : ℕ) (β ell x : ℝ) : ℝ :=
  β^2*(p:ℝ)*((p:ℝ)-1)*x^(p-2)*(1-x)-
    (ell-β^2*p+β^2*p*x^(p-1))

theorem scalarSign_hasDerivAt {p : ℕ} (hp : 3≤p) (β ell x : ℝ) :
    HasDerivAt (scalarSignPolynomial p β ell) (signSlope p β ell x) x := by
  have hd := (((hasDerivAt_const x (ell-β^2*(p:ℝ))).add
    (((hasDerivAt_id x).pow (p-1)).const_mul (β^2*(p:ℝ)))).mul
      ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))).sub_const 1
  convert hd using 1
  · ext y
    simp [scalarSignPolynomial]
  · simp only [Nat.sub_sub,Nat.cast_sub (by omega : 1≤p),Nat.cast_one,
      Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply,id_eq]
    unfold signSlope
    ring

theorem signSlope_hasDerivAt {p : ℕ} (hp : 3≤p) (β ell x : ℝ) :
    HasDerivAt (signSlope p β ell)
      (β^2*(p:ℝ)*((p:ℝ)-1)*x^(p-3)*(((p:ℝ)-2)-(p:ℝ)*x)) x := by
  have hd := ((((hasDerivAt_id x).pow (p-2)).const_mul
    (β^2*(p:ℝ)*((p:ℝ)-1))).mul
      ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))).sub
    ((hasDerivAt_const x (ell-β^2*(p:ℝ))).add
      (((hasDerivAt_id x).pow (p-1)).const_mul (β^2*(p:ℝ))))
  convert hd using 1
  · ext y
    rfl
  · simp only [Nat.sub_sub,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply,id_eq]
    rw [Nat.cast_sub (by omega : 2≤p),Nat.cast_sub (by omega : 1≤p)]
    norm_num only [Nat.cast_ofNat]
    have hpow : x^(p-2)=x^(p-3)*x := by
      rw [show p-2=p-3+1 by omega,pow_succ]
    rw [hpow]
    ring

theorem marginal_sign_forces_larger_root {p : ℕ} {β q : ℝ}
    (hp : 3≤p) (hβ : 0<β) (hq : 0<q) (hq1 : q<1)
    (hmarg : β^2*marginalityPolynomial p q=1)
    (hsign : ∀x∈Ioo q 1,scalarSignPolynomial p β (multiplier p β q) x<0) :
    spinodalPlateau p≤q := by
  by_contra hn
  have hqm : q<spinodalPlateau p := lt_of_not_ge hn
  let y : ℝ := (q+spinodalPlateau p)/2
  have hqy : q<y := by dsimp [y]; linarith
  have hym : y<spinodalPlateau p := by dsimp [y]; linarith
  have hy1 : y<1 := hym.trans (spinodal_plateau_lt_one hp)
  have hzero : scalarSignPolynomial p β (multiplier p β q) q=0 :=
    (scalar_zero_iff_multiplier (ne_of_lt hq1)).mpr rfl
  have hslope : signSlope p β (multiplier p β q) q=0 := by
    have hd : 1-q≠0 := (sub_pos.mpr hq1).ne'
    have hphi : multiplier p β q-β^2*p+β^2*p*q^(p-1)=1/(1-q) := by
      unfold multiplier
      ring
    unfold signSlope
    rw [hphi]
    apply sub_eq_zero.mpr
    apply (eq_div_iff hd).mpr
    unfold marginalityPolynomial at hmarg
    nlinarith [hmarg]
  have hmSlope : StrictMonoOn (signSlope p β (multiplier p β q)) (Icc q y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc q y)
      (by unfold signSlope; fun_prop)
    intro x hx
    rw [interior_Icc] at hx
    rw [(signSlope_hasDerivAt hp β (multiplier p β q) x).deriv]
    have hx0 : 0<x := hq.trans hx.1
    have hbr : 0<((p:ℝ)-2)-(p:ℝ)*x := by
      have hxm : x<spinodalPlateau p := hx.2.trans hym
      unfold spinodalPlateau at hxm
      have hh := (lt_div_iff₀ (spin_positive hp)).mp hxm
      nlinarith
    exact mul_pos (mul_pos (mul_pos (mul_pos (sq_pos_of_pos hβ)
      (spin_positive hp)) (spin_minus_one_positive hp)) (pow_pos hx0 _)) hbr
  have hmF : StrictMonoOn (scalarSignPolynomial p β (multiplier p β q)) (Icc q y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc q y)
      (by unfold scalarSignPolynomial; fun_prop)
    intro x hx
    rw [interior_Icc] at hx
    rw [(scalarSign_hasDerivAt hp β (multiplier p β q) x).deriv]
    have hh := hmSlope ⟨le_rfl,hqy.le⟩ ⟨hx.1.le,hx.2.le⟩ hx.1
    rw [hslope] at hh
    exact hh
  have hh := hmF ⟨le_rfl,hqy.le⟩ ⟨hqy.le,le_rfl⟩ hqy
  rw [hzero] at hh
  exact (not_lt_of_ge hh.le) (hsign y ⟨hqy,hy1⟩)

end SphericalAging.MarginalPlateauSign
