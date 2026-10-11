module

public import SphericalAging.GammaRatioDensity

public section

/-! Actual gamma-pair ratio distribution, derived by scalar Jacobian
substitution and nonnegative Fubini. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SphericalAging.GammaRatioLaw
open GammaRatioDensity BetaGammaLaw

theorem measurable_ratioKernel (b : ℝ) :
    Measurable (fun q : ℝ×ℝ => ratioKernel b q.2 q.1) := by
  unfold ratioKernel
  fun_prop

theorem lintegral_ratioKernel_negative {b t : ℝ} (ht : t<0) :
    (∫⁻ z : ℝ,ENNReal.ofReal (ratioKernel b t z))=ENNReal.ofReal (ratioDensity b t) := by
  rw [ratioDensity,ite_eq_right (not_lt.mpr ht.le),ENNReal.ofReal_zero]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro z
  by_cases hz : 0<z
  · have hzt : ¬0≤z*t := not_le.mpr (mul_neg_of_pos_of_neg hz ht)
    simp [ratioKernel,gammaPDFReal,hzt]
  · simp [ratioKernel_zero_nonpositive b t (le_of_not_gt hz)]

theorem gamma_ratio_lintegral {z b : ℝ} (hz : 0<z)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ w : ℝ,φ (w/z) ∂gammaMeasure b 1)=
      ∫⁻ t : ℝ,ENNReal.ofReal z*gammaPDF b 1 (z*t)*φ t := by
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul (f:=gammaPDF b 1)
    (g:=fun w : ℝ => φ (w/z)) volume
    (measurable_gammaPDFReal b 1).ennreal_ofReal (hφ.comp (measurable_id.div_const z))]
  rw [lintegral_scale (inv_pos.mpr hz)]
  apply lintegral_congr
  intro t
  have h1 : 1/z⁻¹=z := by simp
  have h2 : t/z⁻¹=z*t := by simp [div_eq_mul_inv,mul_comm]
  have h3 : (z*t)/z=t := by field_simp
  simpa only [h1,h2,h3,mul_assoc,Pi.mul_apply]

theorem weighted_gamma_ratio_lintegral {b : ℝ} (hb : 0<b) {z : ℝ} (hz : z≠0)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    gammaPDF b 1 z*(∫⁻ w : ℝ,φ (w/z) ∂gammaMeasure b 1)=
      ∫⁻ t : ℝ,ENNReal.ofReal (ratioKernel b t z)*φ t := by
  by_cases hzpos : 0<z
  · rw [gamma_ratio_lintegral hzpos hφ,
      ←lintegral_const_mul' (gammaPDF b 1 z) _ (show gammaPDF b 1 z≠∞ from ENNReal.ofReal_ne_top)]
    apply lintegral_congr
    intro t
    have he : gammaPDF b 1 z*ENNReal.ofReal z*gammaPDF b 1 (z*t)=
        ENNReal.ofReal (ratioKernel b t z) := by
      unfold gammaPDF ratioKernel
      rw [←ENNReal.ofReal_mul (gammaPDFReal_nonneg hb zero_lt_one z),
        ←ENNReal.ofReal_mul (mul_nonneg (gammaPDFReal_nonneg hb zero_lt_one z) hzpos.le)]
      congr 1
      ring
    simpa only [mul_assoc] using congrArg (fun k : ℝ≥0∞ => k*φ t) he
  · have hn : z<0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
    simp [gammaPDF_of_neg hn,ratioKernel_zero_nonpositive b _ hn.le]

theorem gamma_pair_ratio_law {b : ℝ} (hb : 0<b) :
    ((gammaMeasure b 1).prod (gammaMeasure b 1)).map
      (fun q : ℝ×ℝ => q.2/q.1)=
      volume.withDensity (fun t => ENNReal.ofReal (ratioDensity b t)) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map (g:=fun q : ℝ×ℝ => q.2/q.1) hφ (measurable_snd.div measurable_fst)]
  rw [lintegral_prod (fun q : ℝ×ℝ => φ (q.2/q.1)) (by fun_prop)]
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul]
  · change (∫⁻ z : ℝ,gammaPDF b 1 z*(∫⁻ w : ℝ,φ (w/z) ∂gammaMeasure b 1))=
      ∫⁻ t,φ t ∂volume.withDensity (fun t => ENNReal.ofReal (ratioDensity b t))
    rw [lintegral_withDensity_eq_lintegral_mul volume (ratioDensity_measurable b).ennreal_ofReal hφ]
    calc
      _ = ∫⁻ z : ℝ,∫⁻ t : ℝ,ENNReal.ofReal (ratioKernel b t z)*φ t := by
        apply lintegral_congr_ae
        filter_upwards [Measure.ae_ne volume (0:ℝ)] with z hz
        exact weighted_gamma_ratio_lintegral hb hz hφ
      _ = ∫⁻ t : ℝ,∫⁻ z : ℝ,ENNReal.ofReal (ratioKernel b t z)*φ t := by
        rw [lintegral_lintegral_swap]
        exact ((measurable_ratioKernel b).ennreal_ofReal.mul (hφ.comp measurable_snd)).aemeasurable
      _ = ∫⁻ t : ℝ,ENNReal.ofReal (ratioDensity b t)*φ t := by
        apply lintegral_congr_ae
        filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
        rw [lintegral_mul_const'' (f:=fun z : ℝ => ENNReal.ofReal (ratioKernel b t z)) _ ((measurable_ratioKernel b).comp
          (measurable_id.prodMk measurable_const)).ennreal_ofReal.aemeasurable]
        rcases lt_or_gt_of_ne ht with ht | ht
        · rw [lintegral_ratioKernel_negative ht]
        · rw [lintegral_ratioKernel hb ht]
  · exact (measurable_gammaPDFReal b 1).ennreal_ofReal
  · exact Measurable.lintegral_prod_right (hφ.comp (measurable_snd.div measurable_fst))

end SphericalAging.GammaRatioLaw
