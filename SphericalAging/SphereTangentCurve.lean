module

public import SphericalAging.HardSphereDynamics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Pow

public section

/-! An actual smooth sphere curve realizes every tangent initial vector. -/
noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace SphericalAging.SphereTangentCurve
open HardSphereDynamics
variable {N : ℕ}

@[expose]  def curve (x v : State N) (r : ℝ) : State N :=
  (Real.sqrt (N : ℝ)/Real.sqrt ((N : ℝ)+r^2*‖v‖^2)) • (x+r • v)

 theorem curve_zero (hN : 0 < N) (x v : State N) : curve x v 0=x := by
  simp only [curve,zero_pow (by norm_num : 2 ≠ 0),zero_mul,add_zero,zero_smul]
  rw [div_self (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),one_smul]

 theorem curve_onSphere (hN : 0 < N) {x v : State N} (hx : OnSphere x)
    (hv : inner ℝ x v=0) (r : ℝ) : OnSphere (curve x v r) := by
  apply (onSphere_iff_norm_sq _).mpr
  have hpos : 0 < (N : ℝ)+r^2*‖v‖^2 := by positivity
  have hnorm : ‖x+r • v‖^2=(N : ℝ)+r^2*‖v‖^2 := by
    simp only [norm_add_sq_real,real_inner_smul_right,hv,mul_zero,add_zero,
      (onSphere_iff_norm_sq _).mp hx,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [curve,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,div_pow,
    Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hpos.le,hnorm]
  exact div_mul_cancel₀ _ (ne_of_gt hpos)

 theorem curve_hasDerivAt (hN : 0 < N) {x v : State N} : HasDerivAt (curve x v) v 0 := by
  have hNreal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hpoly : HasDerivAt (fun r : ℝ => (N : ℝ)+r^2*‖v‖^2) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) (N : ℝ)).add (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖v‖^2)) using 1 <;> first | rfl | simp
  have hs := hpoly.sqrt (by simpa using hNreal)
  have hc := (hasDerivAt_const (0 : ℝ) (Real.sqrt (N : ℝ))).div hs (by
    simpa only [zero_pow (by norm_num : 2 ≠ 0),zero_mul,add_zero] using
      Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN))
  have hv' := (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have h := hc.smul hv'
  convert h using 1 <;> first | rfl | simp [Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)]
end SphericalAging.SphereTangentCurve
