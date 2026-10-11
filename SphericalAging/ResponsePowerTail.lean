module

public import SphericalAging.MonotoneResponseTail
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Asymptotics.Defs

public section

/-! The actual power-law consequence in source Corollary 11.6. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ResponsePowerTail
open EarlierSmoothing

theorem power_square_tail {r : ℝ→ℝ} {A a D : ℝ}
    (ha : 0<a) (hA : 0≤A) (hD : 0<D)
    (hi : IntegrableOn (fun v => (r v)^2) (Ici D))
    (hb : ∀v : ℝ,D≤v→|r v|≤A*v^(-1-a)) :
    responseTail r D≤A^2*D^(-1-2*a)/(1+2*a) := by
  have hp : -2-2*a<(-1:ℝ) := by linarith
  have hir : IntegrableOn (fun v : ℝ => A^2*v^(-2-2*a)) (Ioi D) :=
    (integrableOn_Ioi_rpow_of_lt hp hD).const_mul _
  have he := setIntegral_mono_on (hi.mono_set Ioi_subset_Ici_self) hir measurableSet_Ioi
    (fun v hv => show (r v)^2≤A^2*v^(-2-2*a) from by
      have hpv : (v^(-1-a))^2=v^(-2-2*a) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (hD.le.trans hv.le)]
        congr 1
        norm_num
        ring
      have hn := Real.rpow_nonneg (hD.le.trans hv.le) (-1-a)
      have hh := hb v hv.le
      nlinarith [sq_abs (r v),abs_nonneg (r v),mul_nonneg hA hn])
  rw [integral_const_mul,integral_Ioi_rpow_of_lt hp hD] at he
  rw [responseTail,integral_Ici_eq_integral_Ioi]
  calc
    _ ≤ A^2*(-D^((-2-2*a)+1)/((-2-2*a)+1)) := he
    _ = _ := by
      rw [show (-2-2*a)+1=(-1-2*a) by ring,
        show -1-2*a=-(1+2*a) by ring]
      simp only [neg_div_neg_eq]
      ring

/-- Sharp displayed bound on the smoothing modulus, with its actual square
tail integral. -/
theorem power_smoothing_bound {r : ℝ→ℝ} {A a D : ℝ}
    (ha : 0<a) (hA : 0≤A) (hD : 0<D)
    (hi : IntegrableOn (fun v => (r v)^2) (Ici D))
    (hb : ∀v : ℝ,D≤v→|r v|≤A*v^(-1-a)) :
    Real.sqrt D*Real.sqrt (responseTail r D)≤A/Real.sqrt (1+2*a)*D^(-a) := by
  have ht := power_square_tail ha hA hD hi hb
  have hden : 0<1+2*a := by linarith
  have hsd := Real.sq_sqrt hD.le
  have hst := Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _):0≤responseTail r D)
  change Real.sqrt (responseTail r D)^2=responseTail r D at hst
  have hss := Real.sq_sqrt hden.le
  have hpow : (D^(-a))^2=D^(-2*a) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD.le]
    congr 1
    norm_num
    ring
  have hDpow : D*D^(-1-2*a)=D^(-2*a) := by
    calc
      _ = D^(1:ℝ)*D^(-1-2*a) := by rw [Real.rpow_one]
      _ = D^((1:ℝ)+(-1-2*a)) := (Real.rpow_add hD _ _).symm
      _ = _ := by congr 1; ring
  have hleft : (Real.sqrt D*Real.sqrt (responseTail r D))^2=D*responseTail r D := by
    rw [mul_pow,hsd,hst]
  have hright : (A/Real.sqrt (1+2*a)*D^(-a))^2=A^2*D^(-2*a)/(1+2*a) := by
    rw [mul_pow,div_pow,hss,hpow]
    ring
  have he := mul_le_mul_of_nonneg_left ht hD.le
  have heq : D*(A^2*D^(-1-2*a)/(1+2*a))=A^2*D^(-2*a)/(1+2*a) := by
    calc
      _ = A^2*(D*D^(-1-2*a))/(1+2*a) := by ring
      _ = _ := by rw [hDpow]
  rw [heq] at he
  have hn : 0≤A/Real.sqrt (1+2*a)*D^(-a) := by positivity
  nlinarith

/-- The source's Big-O hypothesis entails its Big-O conclusion for the true
smoothing modulus, by the proved power-integral estimate. -/
theorem power_smoothing_isBigO {r : ℝ→ℝ} {a : ℝ} (ha : 0<a)
    (hi : IntegrableOn (fun v => (r v)^2) (Ici 0))
    (hp : Asymptotics.IsBigO atTop r (fun v : ℝ => v^(-1-a))) :
    Asymptotics.IsBigO atTop (fun D : ℝ => Real.sqrt D*Real.sqrt (responseTail r D))
      (fun D : ℝ => D^(-a)) := by
  obtain ⟨C,hC⟩ := hp.bound
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp hC
  let A := max C 0
  apply Asymptotics.IsBigO.of_bound (A/Real.sqrt (1+2*a))
  filter_upwards [eventually_ge_atTop (max v₀ 1)] with D hD
  have hDpos : 0<D := by linarith [le_max_right v₀ 1]
  have hAb : 0≤A := le_max_right _ _
  have hb : ∀v : ℝ,D≤v→|r v|≤A*v^(-1-a) := by
    intro v hv
    have hvpos : 0≤v := hDpos.le.trans hv
    have hvc := hv₀ v ((le_max_left v₀ 1).trans (hD.trans hv))
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hvpos _)] at hvc
    exact hvc.trans (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg hvpos _))
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hDpos.le _)]
  exact power_smoothing_bound ha hAb hDpos
    (hi.mono_set (Ici_subset_Ici.mpr hDpos.le)) hb

end SphericalAging.ResponsePowerTail
