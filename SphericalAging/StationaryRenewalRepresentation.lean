module

public import SphericalAging.RenewalRemainder
public import SphericalAging.LogBetaRenewalDensityTheorem

public section

/-! Genuine renewal-series integrability and representation for the actual
log-beta law, using its proved renewal density. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryRenewalRepresentation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AbsorptionCutoff.Renewal RenewalRemainder LogBetaRenewal LogBetaMoments
  LogBetaConvolutionPowers LogBetaRenewalSeries LogBetaRenewalDensityTheorem

@[expose] def renewalConvolution (U G : ℝ → ℝ) (x : ℝ) := ∫ y in Ioi 0,U y*G (x-y)

/-- A locally integrable renewal kernel with bounded positive tail pairs
with every bounded L1 source; the product is genuinely integrable. -/
theorem renewalProduct_integrable (U G : ℝ → ℝ) (hU : Measurable U)
    (hLocal : IntegrableOn U (Icc 0 1)) (C M : ℝ) (hC : 0≤C) (hM : 0≤M)
    (hTail : ∀ y≥1,|U y|≤C) (hG : Integrable G) (hGm : Measurable G)
    (hbG : ∀ y,|G y|≤M) (x : ℝ) :
    IntegrableOn (fun y => U y*G (x-y)) (Ioi 0) := by
  have hm : Measurable (fun y => U y*G (x-y)) := hU.mul (hGm.comp (measurable_const.sub measurable_id))
  have hNear : IntegrableOn (fun y => U y*G (x-y)) (Ioc 0 1) := by
    apply ((hLocal.mono_set Ioc_subset_Icc_self).norm.const_mul M).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y _
    change ‖U y*G (x-y)‖≤M*‖U y‖
    rw [Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbG (x-y)) (abs_nonneg (U y))
  have hTranslated : Integrable (fun y => G (x-y)) := hG.comp_sub_left x
  have hFar : IntegrableOn (fun y => U y*G (x-y)) (Ioi 1) := by
    apply ((hTranslated.integrableOn (s:=Ioi 1)).norm.const_mul C).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change ‖U y*G (x-y)‖≤C*‖G (x-y)‖
    rw [Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hTail y hy.le) (abs_nonneg _)
  have hi := hNear.union hFar
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] at hi
  exact hi

/-- Genuine density formula for averaging by each positive convolution power. -/
theorem renewalAverage_density {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (G : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    renewalAverage (law ρ a) G (n+1) x=
      ∫ y in Ioi 0,powerDensity ρ a n y*G (x-y) := by
  have hp := (powerDensity_properties hρ ha ha1 n).1
  unfold renewalAverage
  rw [convPow_law_eq_withDensity hρ ha ha1,
    integral_withDensity_eq_integral_toReal_smul hp.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp.nonnegative _),smul_eq_mul]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  simp only [mem_Ioi,not_lt] at hy
  simp [hp.zero y hy]

/-- Absolute product integrability justifies the actual density-series
exchange, producing a genuine HasSum rather than a formal infinite identity. -/
theorem renewalAverage_tail_hasSum {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (G : ℝ → ℝ) (hG : Integrable G) (hGm : Measurable G) (M : ℝ) (hM : 0≤M)
    (hbG : ∀ y,|G y|≤M) (x : ℝ) :
    HasSum (fun n : ℕ => renewalAverage (law ρ a) G (n+1) x)
      (renewalConvolution (renewalDensity ρ a) G x) := by
  obtain ⟨_,_,_,hSum,hLocal,⟨C,hC,hTail⟩,_⟩ := log_beta_renewal_density hρ ha ha1
  have hUmeas : Measurable (renewalDensity ρ a) :=
    Measurable.tsum (fun n => (powerDensity_properties hρ ha ha1 n).1.measurable)
  have hAbsTail (y : ℝ) (hy : 1≤y) : |renewalDensity ρ a y|≤C := by
    rw [abs_of_nonneg (hTail y hy).1]
    exact (hTail y hy).2
  have hBoundInt : IntegrableOn (fun y => renewalDensity ρ a y*|G (x-y)|) (Ioi 0) := by
    apply renewalProduct_integrable (renewalDensity ρ a) (fun y => |G y|) hUmeas (hLocal 1) C M hC hM hAbsTail
      (by simpa only [Real.norm_eq_abs] using hG.norm) (by fun_prop) _ x
    intro y
    simpa only [abs_abs] using hbG y
  have hSeries := hasSum_integral_of_dominated_convergence (μ:=volume.restrict (Ioi 0))
    (F:=fun n y => powerDensity ρ a n y*G (x-y))
    (f:=fun y => renewalDensity ρ a y*G (x-y))
    (bound:=fun n y => powerDensity ρ a n y*|G (x-y)|)
    (fun n => ((powerDensity_properties hρ ha ha1 n).1.measurable.mul
      (hGm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((powerDensity_properties hρ ha ha1 n).1.nonnegative y)]))
    (Eventually.of_forall (fun y => (hSum y).mul_right _))
    (by simpa only [IntegrableOn,renewalDensity,tsum_mul_right] using hBoundInt)
    (Eventually.of_forall (fun y => (hSum y).hasSum.mul_right _))
  simpa only [←renewalAverage_density hρ ha ha1,renewalConvolution] using hSeries

/-- Full summation including the genuine Dirac zeroth convolution power. -/
theorem renewalAverage_hasSum {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (G : ℝ → ℝ) (hG : Integrable G) (hGm : Measurable G) (M : ℝ) (hM : 0≤M)
    (hbG : ∀ y,|G y|≤M) (x : ℝ) :
    HasSum (fun n : ℕ => renewalAverage (law ρ a) G n x)
      (G x+renewalConvolution (renewalDensity ρ a) G x) := by
  have he : HasSum (fun n : ℕ => renewalAverage (law ρ a) G n x)
      (renewalAverage (law ρ a) G 0 x+renewalConvolution (renewalDensity ρ a) G x) :=
    HasSum.zero_add (f:=fun n : ℕ => renewalAverage (law ρ a) G n x)
      (renewalAverage_tail_hasSum hρ ha ha1 G hG hGm M hM hbG x)
  simpa only [renewalAverage,convPow_zero,integral_dirac,sub_zero] using he

/-- The actual renewal representation, obtained by finite iteration,
absolute summation, and a proved vanishing remainder. -/
theorem log_beta_renewal_representation {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (F G : ℝ → ℝ) (hF : Measurable F) (hGm : Measurable G) (hG : Integrable G)
    (MF MG : ℝ) (hMF : 0≤MF) (hMG : 0≤MG)
    (hbF : ∀ y,‖F y‖≤MF) (hbG : ∀ y,|G y|≤MG)
    (hBot : Tendsto F atBot (𝓝 0))
    (hEq : ∀ x,F x-renewalAverage (law ρ a) F 1 x=G x) (x : ℝ) :
    F x=G x+renewalConvolution (renewalDensity ρ a) G x := by
  letI := law_probability hρ ha
  have hs := (renewalAverage_hasSum hρ ha ha1 G hG hGm MG hMG hbG x).tendsto_sum_nat
  have hr := renewalAverage_tendsto_zero (law ρ a) 1 (by norm_num)
    (negative_expTransform_lt_one hρ ha (by norm_num)) F hF MF hMF hbF hBot x
  have hLimit := hs.add hr
  simp only [add_zero] at hLimit
  have hConst : Tendsto (fun _ : ℕ => F x) atTop
      (𝓝 (G x+renewalConvolution (renewalDensity ρ a) G x)) := by
    apply hLimit.congr
    intro n
    exact (finite_renewal_iteration (law ρ a) F G hF hGm MF MG hbF
      (by simpa only [Real.norm_eq_abs] using hbG) hEq n x).symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst

end
end SphericalAging.StationaryRenewalRepresentation
