module

public import SphericalAging.ProfileCenterEnergy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! Exact source-normalized center-energy identity with the actual real-power
definition of z, together with its sharp AM--GM equality case. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace SphericalAging.NormalizedCenterAMGM
open PlateauAlgebra

@[expose] def centerZ (p : ℕ) (β q : ℝ) : ℝ :=
  β*Real.sqrt ((p:ℝ)*((p:ℝ)-1))*q^(((p:ℝ)-2)/2)*(1-q)

theorem sqrt_pow_eq_rpow {q : ℝ} (hq : 0≤q) (p : ℕ) :
    Real.sqrt (q^p)=q^((p:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hq]
  congr 1
  ring

theorem centerZ_positive {p : ℕ} {β q : ℝ}
    (hp : 3≤p) (hβ : 0<β) (hq : 0<q) (hq1 : q<1) : 0<centerZ p β q := by
  unfold centerZ
  exact mul_pos (mul_pos (mul_pos hβ
    (Real.sqrt_pos.mpr (mul_pos (spin_positive hp) (spin_minus_one_positive hp))))
      (Real.rpow_pos_of_pos hq _)) (sub_pos.mpr hq1)

theorem centerZ_sq {p : ℕ} {β q : ℝ} (hp : 3≤p) (hq : 0≤q) :
    centerZ p β q^2=β^2*marginalityPolynomial p q := by
  have hcast : ((p:ℝ)-2)/2*2=((p-2:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 2≤p)]
    norm_num
  have hpow : (q^(((p:ℝ)-2)/2))^2=q^(p-2) := by
    rw [←Real.rpow_mul_natCast hq]
    norm_num only [Nat.cast_ofNat]
    rw [hcast,Real.rpow_natCast]
  unfold centerZ marginalityPolynomial
  rw [mul_pow,mul_pow,mul_pow,hpow,Real.sq_sqrt
    (mul_nonneg (spin_positive hp).le (spin_minus_one_positive hp).le)]
  ring

theorem normalized_center_energy_identity {p : ℕ} {β q : ℝ}
    (hp : 3≤p) (hβ : 0<β) (hq : 0<q) (hq1 : q<1) :
    centerEnergy p β q/q^((p:ℝ)/2)=
      Real.sqrt (((p:ℝ)-1)/(p:ℝ))*(centerZ p β q+1/centerZ p β q) := by
  let k : ℝ := Real.sqrt (((p:ℝ)-1)/(p:ℝ))
  let Q : ℝ := q^((p:ℝ)/2)
  let a : ℝ := q/((p:ℝ)*β*(1-q))
  let b : ℝ := β*((p:ℝ)-1)*q^(p-1)*(1-q)
  have hp0 := (spin_positive hp).ne'
  have hk : 0<k := Real.sqrt_pos.mpr (div_pos (spin_minus_one_positive hp) (spin_positive hp))
  have hQ : 0<Q := Real.rpow_pos_of_pos hq _
  have hz := centerZ_positive hp hβ hq hq1
  have hroot : k*Real.sqrt ((p:ℝ)*((p:ℝ)-1))=(p:ℝ)-1 := by
    apply (sq_eq_sq₀ (mul_nonneg hk.le (Real.sqrt_nonneg _))
      (spin_minus_one_positive hp).le).mp
    rw [mul_pow,Real.sq_sqrt (div_nonneg (spin_minus_one_positive hp).le
      (spin_positive hp).le),Real.sq_sqrt
      (mul_nonneg (spin_positive hp).le (spin_minus_one_positive hp).le)]
    field_simp
  have hcast : ((p:ℝ)-2)/2+(p:ℝ)/2=((p-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤p)]
    norm_num
    ring
  have hpow : q^(((p:ℝ)-2)/2)*Q=q^(p-1) := by
    dsimp only [Q]
    rw [←Real.rpow_add hq,hcast,Real.rpow_natCast]
  have hb : k*centerZ p β q*Q=b := by
    unfold centerZ
    calc
      k*(β*Real.sqrt ((p:ℝ)*((p:ℝ)-1))*q^(((p:ℝ)-2)/2)*(1-q))*Q =
          β*(k*Real.sqrt ((p:ℝ)*((p:ℝ)-1)))*
            (q^(((p:ℝ)-2)/2)*Q)*(1-q) := by ring
      _ = b := by rw [hroot,hpow]
  have hab : a*b=k^2*Q^2 := by
    have hh := center_energy_term_product hp hβ.ne' (ne_of_lt hq1)
    change a*b=(((p:ℝ)-1)/(p:ℝ))*q^p at hh
    change a*b=(Real.sqrt (((p:ℝ)-1)/(p:ℝ)))^2*(q^((p:ℝ)/2))^2
    rw [←sqrt_pow_eq_rpow hq.le p,Real.sq_sqrt (pow_nonneg hq.le p)]
    rw [Real.sq_sqrt (div_nonneg (spin_minus_one_positive hp).le (spin_positive hp).le)]
    exact hh
  have ha : a=k*Q/centerZ p β q := by
    apply (eq_div_iff hz.ne').mpr
    rw [←hb] at hab
    have hx : k*Q≠0 := mul_ne_zero hk.ne' hQ.ne'
    apply mul_right_cancel₀ hx
    nlinarith [hab]
  rw [center_energy_decomposition hp hβ.ne' (ne_of_lt hq1)]
  change (a+b)/Q=k*(centerZ p β q+1/centerZ p β q)
  rw [ha,←hb]
  field_simp
  ring

end SphericalAging.NormalizedCenterAMGM
