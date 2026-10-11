module

public import SphericalAging.DirichletKernel
public import SphericalAging.BetaGammaLaw

public section

/-! Genuine gamma-pair ratio density and its logarithmic cosh kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SphericalAging.GammaRatioDensity
open LogBetaRenewal DirichletKernel

@[expose] def ratioKernel (b t z : ℝ) : ℝ := z*gammaPDFReal b 1 z*gammaPDFReal b 1 (z*t)

@[expose] def ratioDensity (b t : ℝ) : ℝ :=
  if 0<t then t^(b-1)/(1+t)^(2*b)/beta b b else 0

theorem ratioKernel_transformed {b t z : ℝ} (ht : 0<t) (hz : 0<z) :
    ratioKernel b t z=
      (t^(b-1)/(Real.Gamma b)^2)*z^(2*b-1)*Real.exp (-((1+t)*z)) := by
  unfold ratioKernel
  rw [gammaPDFReal,ite_eq_left hz.le,gammaPDFReal,ite_eq_left (mul_pos hz ht).le,
    Real.one_rpow,one_mul,one_mul,Real.mul_rpow hz.le ht.le]
  have he : Real.exp (-z)*Real.exp (-(z*t))=Real.exp (-((1+t)*z)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hp : z*z^(b-1)*z^(b-1)=z^(2*b-1) := by
    calc
      _ = z^(1:ℝ)*z^(b-1)*z^(b-1) := by rw [Real.rpow_one]
      _ = z^(1+(b-1)+(b-1)) := by rw [Real.rpow_add hz,Real.rpow_add hz]
      _ = _ := by congr 1;ring
  calc
    _ = (z*z^(b-1)*z^(b-1))*t^(b-1)/((Real.Gamma b)^2)*
        (Real.exp (-z)*Real.exp (-(z*t))) := by ring
    _ = _ := by rw [he,hp];ring

theorem ratioKernel_nonnegative {b : ℝ} (hb : 0<b) (t : ℝ) {z : ℝ} (hz : 0≤z) :
    0≤ratioKernel b t z :=
  mul_nonneg (mul_nonneg hz (gammaPDFReal_nonneg hb zero_lt_one z))
    (gammaPDFReal_nonneg hb zero_lt_one (z*t))

theorem gamma_raw_integrable {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    IntegrableOn (fun z : ℝ => z^(s-1)*Real.exp (-(r*z))) (Ioi 0) := by
  have hbase := Real.GammaIntegral_convergent hs
  have hscaled : IntegrableOn
      (fun z : ℝ => Real.exp (-(r*z))*(r*z)^(s-1)) (Ioi 0) := by
    simpa only [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff (fun z : ℝ => Real.exp (-z)*z^(s-1)) 0 hr).mpr
        (by simpa only [mul_zero] using hbase)
  apply (hscaled.const_mul (r^(s-1))⁻¹).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.mul_rpow hr.le hz.le]
  have hn := ne_of_gt (Real.rpow_pos_of_pos hr (s-1))
  field_simp [hn]

theorem ratioKernel_integrable {b t : ℝ} (hb : 0<b) (ht : 0<t) :
    IntegrableOn (ratioKernel b t) (Ioi 0) := by
  apply ((gamma_raw_integrable (s:=2*b) (r:=1+t) (by linarith) (by linarith)).const_mul
    (t^(b-1)/(Real.Gamma b)^2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  simpa only [mul_assoc] using (ratioKernel_transformed (b:=b) ht hz).symm

theorem ratioKernel_zero_nonpositive (b t : ℝ) {z : ℝ} (hz : z≤0) :
    ratioKernel b t z=0 := by
  rcases lt_or_eq_of_le hz with hz | rfl
  · simp [ratioKernel,gammaPDFReal,not_le.mpr hz]
  · simp [ratioKernel]

theorem integral_ratioKernel {b t : ℝ} (hb : 0<b) (ht : 0<t) :
    (∫ z in Ioi (0:ℝ),ratioKernel b t z)=ratioDensity b t := by
  have hg : (∫ z in Ioi (0:ℝ),z^(2*b-1)*Real.exp (-((1+t)*z)))=
      (1/(1+t))^(2*b)*Real.Gamma (2*b) :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=2*b) (r:=1+t) (by linarith) (by linarith)
  calc
    _ = (t^(b-1)/(Real.Gamma b)^2)*
        (∫ z in Ioi (0:ℝ),z^(2*b-1)*Real.exp (-((1+t)*z))) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      simpa only [mul_assoc] using ratioKernel_transformed (b:=b) ht hz
    _ = _ := by
      rw [hg,ratioDensity,ite_eq_left ht,beta,Real.div_rpow zero_le_one (by linarith),Real.one_rpow]
      have hG := ne_of_gt (Real.Gamma_pos_of_pos hb)
      have hG2 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith : 0<2*b))
      have he : b+b=2*b := by ring
      rw [he]
      field_simp [hG,hG2]
      <;>ring

theorem ratioDensity_measurable (b : ℝ) : Measurable (ratioDensity b) := by
  unfold ratioDensity
  apply Measurable.ite measurableSet_Ioi
  · fun_prop
  · exact measurable_const

theorem lintegral_ratioKernel {b t : ℝ} (hb : 0<b) (ht : 0<t) :
    (∫⁻ z : ℝ,ENNReal.ofReal (ratioKernel b t z))=ENNReal.ofReal (ratioDensity b t) := by
  rw [←lintegral_add_compl _ measurableSet_Ioi]
  have hzero : (∫⁻ z in (Ioi (0:ℝ))ᶜ,ENNReal.ofReal (ratioKernel b t z))=0 := by
    apply setLIntegral_eq_zero measurableSet_Ioi.compl
    intro z hz
    change ENNReal.ofReal (ratioKernel b t z)=0
    rw [ratioKernel_zero_nonpositive b t (le_of_not_gt hz),ENNReal.ofReal_zero]
  rw [hzero,add_zero,←ofReal_integral_eq_lintegral_ofReal (ratioKernel_integrable hb ht)
    (Eventually.of_forall (fun z => ?_)),integral_ratioKernel hb ht]
  by_cases hz : 0≤z
  · exact ratioKernel_nonnegative hb t hz
  · rw [ratioKernel_zero_nonpositive b t (le_of_not_ge hz)]
    rfl

theorem log_ratio_cosh_identity (b h : ℝ) :
    Real.exp h*ratioDensity b (Real.exp h)=
      1/(beta b b*(2*Real.cosh (h/2))^(2*b)) := by
  rw [ratioDensity,ite_eq_left (Real.exp_pos h)]
  have hc : 0<2*Real.cosh (h/2) := by positivity
  have he : 1+Real.exp h=Real.exp (h/2)*(2*Real.cosh (h/2)) := by
    rw [Real.cosh_eq]
    have hp : Real.exp (h/2)*Real.exp (h/2)=Real.exp h := by
      rw [←Real.exp_add]
      congr 1
      ring
    have hm : Real.exp (h/2)*Real.exp (-(h/2))=1 := by
      rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
    nlinarith
  rw [he,Real.mul_rpow (Real.exp_pos _).le hc.le,
    Real.rpow_def_of_pos (Real.exp_pos h),Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos (h/2)),Real.log_exp]
  have hp : Real.exp h*Real.exp (h*(b-1))=Real.exp ((h/2)*(2*b)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp h*Real.exp (h*(b-1)))/
      (Real.exp ((h/2)*(2*b))*(2*Real.cosh (h/2))^(2*b)*beta b b) := by ring
    _ = _ := by rw [hp];field_simp

end SphericalAging.GammaRatioDensity
