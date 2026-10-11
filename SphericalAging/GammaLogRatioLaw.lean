module

public import SphericalAging.GammaRatioLaw
public import SphericalAging.GammaSmoothingVariance

public section

/-! The actual log-ratio law of two independent gamma variables. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SphericalAging.GammaLogRatioLaw
open GammaRatioDensity GammaRatioLaw GammaSmoothingVariance DirichletLogChange

@[expose] def logRatioDensity (b h : ℝ) : ℝ :=
  1/(beta b b*(2*Real.cosh (h/2))^(2*b))

theorem logRatioDensity_measurable (b : ℝ) : Measurable (logRatioDensity b) := by
  unfold logRatioDensity
  fun_prop

theorem ratio_log_law (b : ℝ) :
    (volume.withDensity (fun t => ENNReal.ofReal (ratioDensity b t))).map Real.log=
      volume.withDensity (fun h => ENNReal.ofReal (logRatioDensity b h)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map (g:=Real.log) hφ Real.measurable_log,
    lintegral_withDensity_eq_lintegral_mul (f:=fun t => ENNReal.ofReal (ratioDensity b t))
      (g:=fun t => φ (Real.log t)) volume (ratioDensity_measurable b).ennreal_ofReal
      (hφ.comp Real.measurable_log),
    lintegral_withDensity_eq_lintegral_mul volume (logRatioDensity_measurable b).ennreal_ofReal hφ]
  change (∫⁻ t : ℝ,ENNReal.ofReal (ratioDensity b t)*φ (Real.log t))=
    ∫⁻ h : ℝ,ENNReal.ofReal (logRatioDensity b h)*φ h
  have hpos : (∫⁻ t : ℝ,ENNReal.ofReal (ratioDensity b t)*φ (Real.log t))=
      ∫⁻ t in Ioi (0:ℝ),ENNReal.ofReal (ratioDensity b t)*φ (Real.log t) := by
    rw [←lintegral_add_compl _ measurableSet_Ioi]
    have hzero : (∫⁻ t in (Ioi (0:ℝ))ᶜ,ENNReal.ofReal (ratioDensity b t)*φ (Real.log t))=0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi.compl
      intro t ht
      change ENNReal.ofReal (ratioDensity b t)*φ (Real.log t)=0
      have hn : ¬0<t := ht
      simp only [ratioDensity,ite_eq_right hn,ENNReal.ofReal_zero,zero_mul]
    rw [hzero,add_zero]
  rw [hpos,←lintegral_exp_change (fun t => ENNReal.ofReal (ratioDensity b t)*φ (Real.log t))]
  apply lintegral_congr
  intro h
  rw [Real.log_exp,←mul_assoc,←ENNReal.ofReal_mul (Real.exp_pos h).le,
    log_ratio_cosh_identity]
  rfl

theorem gamma_pair_log_difference_law {b : ℝ} (hb : 0<b) :
    ((gammaMeasure b 1).prod (gammaMeasure b 1)).map
      (fun q : ℝ×ℝ => Real.log q.2-Real.log q.1)=
      volume.withDensity (fun h => ENNReal.ofReal (logRatioDensity b h)) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  have hfst := (measurePreserving_fst (μ:=gammaMeasure b 1) (ν:=gammaMeasure b 1)).quasiMeasurePreserving.ae
    (gamma_ae_positive b)
  have hsnd := (measurePreserving_snd (μ:=gammaMeasure b 1) (ν:=gammaMeasure b 1)).quasiMeasurePreserving.ae
    (gamma_ae_positive b)
  have hae : (fun q : ℝ×ℝ => Real.log q.2-Real.log q.1)=ᵐ[
      (gammaMeasure b 1).prod (gammaMeasure b 1)] (fun q => Real.log (q.2/q.1)) := by
    filter_upwards [hfst,hsnd] with q hq1 hq2
    exact (Real.log_div (ne_of_gt hq2) (ne_of_gt hq1)).symm
  rw [Measure.map_congr hae]
  change ((gammaMeasure b 1).prod (gammaMeasure b 1)).map
    (Real.log ∘ fun q : ℝ×ℝ => q.2/q.1)=_
  rw [←Measure.map_map (g:=Real.log) (f:=fun q : ℝ×ℝ => q.2/q.1)
      Real.measurable_log (measurable_snd.div measurable_fst),
    gamma_pair_ratio_law hb,ratio_log_law]

end SphericalAging.GammaLogRatioLaw
