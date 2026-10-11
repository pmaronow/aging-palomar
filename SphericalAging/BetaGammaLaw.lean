module

public import SphericalAging.BetaGammaDensity
public import Mathlib.Probability.Independence.Basic

public section

/-! Distributional beta--gamma factorization from the actual density calculation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace SphericalAging.BetaGammaLaw
open BetaGammaDensity

theorem measurable_productKernel (ρ a : ℝ) :
    Measurable (fun q : ℝ×ℝ => productKernel ρ a q.2 q.1) := by
  unfold productKernel
  exact (((measurable_betaPDFReal ρ a).comp measurable_fst).mul
    ((measurable_gammaPDFReal (ρ+a) 1).comp (measurable_snd.div measurable_fst))).div
    measurable_fst

theorem lintegral_productKernel_positive {ρ a z : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (hz : 0 < z) :
    (∫⁻ b : ℝ, ENNReal.ofReal (productKernel ρ a z b)) = gammaPDF ρ 1 z := by
  rw [←lintegral_add_compl _ measurableSet_Ioo]
  have hzero : (∫⁻ b in (Ioo (0:ℝ) 1)ᶜ, ENNReal.ofReal (productKernel ρ a z b))=0 := by
    apply setLIntegral_eq_zero measurableSet_Ioo.compl
    intro b hb
    simp [productKernel_zero_outside hb]
  rw [hzero,add_zero,←ofReal_integral_eq_lintegral_ofReal
    (integrableOn_productKernel hρ ha hz)
    (Eventually.of_forall (productKernel_nonnegative hρ ha z)),integral_productKernel hρ ha hz]
  rfl

theorem lintegral_productKernel_negative {ρ a z : ℝ} (hz : z < 0) :
    (∫⁻ b : ℝ, ENNReal.ofReal (productKernel ρ a z b)) = gammaPDF ρ 1 z := by
  rw [gammaPDF_of_neg hz]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro b
  by_cases hb : 0 < b ∧ b < 1
  · have hn : ¬0≤z/b := not_le.mpr (div_neg_of_neg_of_pos hz hb.1)
    simp [productKernel,gammaPDFReal,hn]
  · simp [productKernel,betaPDFReal,hb]

theorem lintegral_scale {b : ℝ} (hb : 0 < b) (g : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ,g x) = ∫⁻ z : ℝ, ENNReal.ofReal (1/b)*g (z/b) := by
  have himage : (fun z : ℝ => z/b) '' univ=univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact ⟨z*b,mem_univ _,by simp [ne_of_gt hb]⟩
  have hinj : InjOn (fun z : ℝ => z/b) univ := by
    intro z hz w hw he
    exact (div_left_inj' (ne_of_gt hb)).mp he
  have hi := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun z _ => ((hasDerivAt_id z).div_const b).hasDerivWithinAt) hinj g
  simp only [id_eq] at hi
  rw [himage] at hi
  simpa only [one_div,abs_of_pos (inv_pos.mpr hb),Measure.restrict_univ] using hi

theorem gamma_scaled_lintegral {ρ a b : ℝ} (hb : 0 < b)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ g : ℝ,f (b*g) ∂gammaMeasure (ρ+a) 1)=
      ∫⁻ z : ℝ,ENNReal.ofReal (1/b)*gammaPDF (ρ+a) 1 (z/b)*f z := by
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul (f := gammaPDF (ρ+a) 1)
    (g := fun g : ℝ => f (b*g)) volume
    (measurable_gammaPDFReal (ρ+a) 1).ennreal_ofReal
    (hf.comp (measurable_id.const_mul b))]
  rw [lintegral_scale hb]
  apply lintegral_congr
  intro z
  change ENNReal.ofReal (1/b)*(gammaPDF (ρ+a) 1 (z/b)*f (b*(z/b)))=
    ENNReal.ofReal (1/b)*gammaPDF (ρ+a) 1 (z/b)*f z
  have hc : b*(z/b)=z := by field_simp [ne_of_gt hb]
  rw [hc]
  ring

theorem weighted_gamma_scaled_lintegral {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (b : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    betaPDF ρ a b*(∫⁻ g : ℝ,f (b*g) ∂gammaMeasure (ρ+a) 1)=
      ∫⁻ z : ℝ,ENNReal.ofReal (productKernel ρ a z b)*f z := by
  by_cases hb : 0 < b ∧ b < 1
  · rw [gamma_scaled_lintegral hb.1 hf,←lintegral_const_mul' (betaPDF ρ a b) _
      (show betaPDF ρ a b≠∞ from ENNReal.ofReal_ne_top)]
    apply lintegral_congr
    intro z
    have he : betaPDF ρ a b*ENNReal.ofReal (1/b)*gammaPDF (ρ+a) 1 (z/b)=
        ENNReal.ofReal (productKernel ρ a z b) := by
      unfold betaPDF gammaPDF productKernel
      rw [←ENNReal.ofReal_mul (LogBetaRenewal.betaPDFReal_nonnegative hρ ha b),
        ←ENNReal.ofReal_mul (mul_nonneg (LogBetaRenewal.betaPDFReal_nonnegative hρ ha b)
          (one_div_pos.mpr hb.1).le)]
      congr 1
      ring
    simpa only [mul_assoc] using congrArg (fun k : ℝ≥0∞ => k*f z) he
  · have hp : betaPDF ρ a b=0 := by simp [betaPDF,betaPDFReal,hb]
    have hk : ∀ z : ℝ, productKernel ρ a z b=0 := fun z => by
      simp [productKernel,betaPDFReal,hb]
    simp [hp,hk]

/-- Lemma16.13: independence as the actual product law gives the genuine
beta--gamma factorization, with no density identity among the premises. -/
theorem beta_gamma_product_law {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    ((betaMeasure ρ a).prod (gammaMeasure (ρ+a) 1)).map (fun q : ℝ×ℝ => q.1*q.2)=
      gammaMeasure ρ 1 := by
  letI := isProbabilityMeasureBeta hρ ha
  letI := isProbabilityMeasure_gammaMeasure (add_pos hρ ha) zero_lt_one
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map (g := fun q : ℝ×ℝ => q.1*q.2) hf (measurable_fst.mul measurable_snd),
    lintegral_prod (fun q : ℝ×ℝ => f (q.1*q.2))
      (hf.comp (measurable_fst.mul measurable_snd)).aemeasurable]
  rw [betaMeasure,lintegral_withDensity_eq_lintegral_mul (f := betaPDF ρ a) volume
    (measurable_betaPDFReal ρ a).ennreal_ofReal]
  · change (∫⁻ b : ℝ,betaPDF ρ a b*(∫⁻ g : ℝ,f (b*g) ∂gammaMeasure (ρ+a) 1))=
      ∫⁻ z : ℝ,f z ∂gammaMeasure ρ 1
    have he : (∫⁻ b : ℝ,betaPDF ρ a b*(∫⁻ g : ℝ,f (b*g) ∂gammaMeasure (ρ+a) 1))=
        ∫⁻ b : ℝ,∫⁻ z : ℝ,ENNReal.ofReal (productKernel ρ a z b)*f z := by
      apply lintegral_congr
      intro b
      exact weighted_gamma_scaled_lintegral hρ ha b hf
    rw [he,lintegral_lintegral_swap]
    · have hzero : ∀ᵐ z : ℝ ∂volume,z≠0 := by
        rw [ae_iff]
        simp
      have hpdf : ∀ᵐ z : ℝ ∂volume,
          (∫⁻ b : ℝ,ENNReal.ofReal (productKernel ρ a z b))=gammaPDF ρ 1 z := by
        filter_upwards [hzero] with z hz
        rcases lt_or_gt_of_ne hz with hn|hp
        · exact lintegral_productKernel_negative hn
        · exact lintegral_productKernel_positive hρ ha hp
      calc
        _ = ∫⁻ z : ℝ,gammaPDF ρ 1 z*f z := by
          apply lintegral_congr_ae
          filter_upwards [hpdf] with z hz
          rw [lintegral_mul_const _]
          · rw [hz]
          · exact ((measurable_productKernel ρ a).comp
              (measurable_id.prodMk measurable_const)).ennreal_ofReal
        _ = _ := by
          rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul (f := gammaPDF ρ 1) volume
            (measurable_gammaPDFReal ρ 1).ennreal_ofReal hf]
          rfl
    · exact ((measurable_productKernel ρ a).ennreal_ofReal.mul
        (hf.comp measurable_snd)).aemeasurable
  · exact Measurable.lintegral_prod_right (hf.comp (measurable_fst.mul measurable_snd))

/-- The source statement for arbitrary independent random variables with
the actual beta and gamma marginal distributions. -/
theorem independent_beta_gamma {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    {B G : Ω → ℝ} (hB : Measurable B) (hG : Measurable G)
    (hind : IndepFun B G P) (hlB : P.map B=betaMeasure ρ a)
    (hlG : P.map G=gammaMeasure (ρ+a) 1) :
    P.map (fun ω => B ω*G ω)=gammaMeasure ρ 1 := by
  have hp := hind.map_prod_eq_prod_map_map hB.aemeasurable hG.aemeasurable
  rw [hlB,hlG] at hp
  have h := beta_gamma_product_law hρ ha
  rw [←hp,Measure.map_map (g := fun q : ℝ×ℝ => q.1*q.2)
    (measurable_fst.mul measurable_snd) (hB.prodMk hG)] at h
  exact h

end SphericalAging.BetaGammaLaw
