module

public import SphericalAging.BetaGammaDensity

public section

/-! Actual critical Schur kernel and its beta-integral row mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace SphericalAging.DirichletKernel
open BetaGammaDensity

@[expose] def Xi (a s t : ℝ) : ℝ := (s*t)^(-a)/(s+t)^(2-2*a)

@[expose] def primeKernel (u v t : ℝ) : ℝ := t^(v-1)/(1+t)^(u+v)

theorem power_ratio_cancel {t w : ℝ} (ht : 0 < t) (hw : 0 < w) (r s : ℝ) :
    ((1/w)^r*(t/w)^s)/(w^2)=t^s/w^(r+s+2) := by
  rw [Real.div_rpow zero_le_one hw.le,Real.one_rpow,Real.div_rpow ht.le hw.le,
    Real.rpow_add hw (r+s) 2,Real.rpow_add hw r s,Real.rpow_two]
  field_simp [ne_of_gt hw,ne_of_gt (Real.rpow_pos_of_pos hw r),
    ne_of_gt (Real.rpow_pos_of_pos hw s)]

theorem transformed_betaPDF {u v t : ℝ} (ht : 0 < t) :
    (1/(1+t)^2)*betaPDFReal u v (substitution 1 t)=primeKernel u v t/beta u v := by
  have hw : 0<1+t := by linarith
  have hb := substitution_pos_lt_one (by norm_num : (0:ℝ)<1) ht
  have hd : 1-substitution 1 t=t/(1+t) := by
    dsimp [substitution]
    field_simp
    <;> ring
  rw [betaPDFReal,ite_eq_left hb,hd]
  have hp := power_ratio_cancel ht hw (u-1) (v-1)
  have he : (u-1)+(v-1)+2=u+v := by ring
  rw [he] at hp
  dsimp [substitution,primeKernel]
  calc
    _ = (((1/(1+t))^(u-1)*(t/(1+t))^(v-1))/(1+t)^2)/beta u v := by ring
    _ = _ := by rw [hp]

theorem Xi_symmetric (a s t : ℝ) : Xi a s t=Xi a t s := by
  simp [Xi,mul_comm,add_comm]

theorem Xi_nonnegative (a s t : ℝ) (hs : 0≤s) (ht : 0≤t) : 0≤Xi a s t := by
  unfold Xi
  positivity

theorem Xi_measurable (a : ℝ) : Measurable (fun q : ℝ×ℝ => Xi a q.1 q.2) := by
  unfold Xi
  fun_prop

theorem integral_betaPDF_interval {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    (∫ b in Ioo (0:ℝ) 1,betaPDFReal u v b)=1 := by
  calc
    _ = ∫ b : ℝ,betaPDFReal u v b := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro b hb
      simp only [mem_Ioo] at hb
      simp [betaPDFReal,hb]
    _ = 1 := LogBetaRenewal.integral_betaPDFReal hu hv

theorem beta_prime_integrable {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    IntegrableOn (primeKernel u v) (Ioi 0) := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t (ht : 0<t) => (substitution_hasDerivAt (by norm_num : (0:ℝ)<1) ht).hasDerivWithinAt)
    (substitution_injective (by norm_num : (0:ℝ)<1)) (betaPDFReal u v)
  rw [substitution_image (by norm_num : (0:ℝ)<1)] at hi
  have hg := hi.mp ((LogBetaRenewal.betaPDFReal_integrable hu hv).integrableOn)
  have hgb : IntegrableOn (fun t => primeKernel u v t/beta u v) (Ioi 0) := by
    apply hg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have habs : |(-1/(1+t)^2)|=1/(1+t)^2 := by
      rw [abs_div,abs_neg,abs_one,abs_of_nonneg (sq_nonneg _)]
    simpa only [habs,smul_eq_mul] using transformed_betaPDF ht
  have h := hgb.const_mul (beta u v)
  apply h.congr
  filter_upwards [] with t
  exact mul_div_cancel₀ _ (ne_of_gt (beta_pos hu hv))

theorem integral_beta_prime {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    (∫ t in Ioi 0,primeKernel u v t)=beta u v := by
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (ht : 0<t) => (substitution_hasDerivAt (by norm_num : (0:ℝ)<1) ht).hasDerivWithinAt)
    (substitution_injective (by norm_num : (0:ℝ)<1)) (betaPDFReal u v)
  rw [substitution_image (by norm_num : (0:ℝ)<1),integral_betaPDF_interval hu hv] at hi
  have hmass : (∫ t in Ioi 0,primeKernel u v t/beta u v)=1 := by
    rw [hi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have habs : |(-1/(1+t)^2)|=1/(1+t)^2 := by
      rw [abs_div,abs_neg,abs_one,abs_of_nonneg (sq_nonneg _)]
    simpa only [habs,smul_eq_mul] using (transformed_betaPDF ht).symm
  rw [integral_div] at hmass
  exact (div_eq_one_iff_eq (ne_of_gt (beta_pos hu hv))).mp hmass


theorem Xi_scaled {a s z : ℝ} (hs : 0<s) (hz : 0<z) :
    Xi a s (s*z)=s^(-2:ℝ)*primeKernel (1-a) (1-a) z := by
  have hsum : 0<1+z := by linarith
  have hn : s*(s*z)=(s*s)*z := by ring
  have hd : s+s*z=s*(1+z) := by ring
  unfold Xi primeKernel
  rw [hn,hd,Real.mul_rpow (mul_pos hs hs).le hz.le,
    Real.mul_rpow hs.le hs.le,Real.mul_rpow hs.le hsum.le]
  have he : (1-a)-1=-a := by ring
  have he' : (1-a)+(1-a)=2-2*a := by ring
  rw [he,he']
  have hp : s^(-a)*s^(-a)/s^(2-2*a)=s^(-2:ℝ) := by
    rw [←Real.rpow_add hs,←Real.rpow_sub hs]
    congr 1
    ring
  calc
    _ = (s^(-a)*s^(-a)/s^(2-2*a)) * (z^(-a)/(1+z)^(2-2*a)) := by ring
    _ = _ := by rw [hp]

/-- Integrability of each genuine Schur-kernel row on the positive ray. -/
theorem Xi_row_integrable {a s : ℝ} (ha : a<1) (hs : 0<s) :
    IntegrableOn (Xi a s) (Ioi 0) := by
  have hshape : 0<1-a := sub_pos.mpr ha
  have hi := (beta_prime_integrable hshape hshape).const_mul (s^(-2:ℝ))
  have hg : IntegrableOn (fun z => Xi a s (s*z)) (Ioi 0) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact (Xi_scaled hs hz).symm
  simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff (Xi a s) 0 hs).mp hg

/-- The exact beta row mass, proved by two actual changes of variables. -/
theorem integral_Xi_row {a s : ℝ} (ha : a<1) (hs : 0<s) :
    (∫ t in Ioi 0,Xi a s t)=beta (1-a) (1-a)/s := by
  have hshape : 0<1-a := sub_pos.mpr ha
  have hi := integral_comp_mul_left_Ioi' (Xi a s) 0 hs
  simp only [mul_zero,smul_eq_mul] at hi
  calc
    _ = s*(∫ z in Ioi 0,Xi a s (s*z)) := hi.symm
    _ = s*(∫ z in Ioi 0,s^(-2:ℝ)*primeKernel (1-a) (1-a) z) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      exact Xi_scaled hs hz
    _ = s*(s^(-2:ℝ)*beta (1-a) (1-a)) := by
      rw [integral_const_mul,integral_beta_prime hshape hshape]
    _ = _ := by
      rw [Real.rpow_neg hs.le,Real.rpow_two]
      field_simp [ne_of_gt hs]

end SphericalAging.DirichletKernel
