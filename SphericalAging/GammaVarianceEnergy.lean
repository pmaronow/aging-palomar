module

public import SphericalAging.GammaLogRatioLaw

public section

/-! Exact integrated gamma variance as the actual logarithmic Dirichlet
energy. All identities are nonnegative integral identities before finiteness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SphericalAging.GammaVarianceEnergy
open GammaSmoothingVariance GammaLogRatioLaw DirichletIncrement

@[expose] def differenceEnergy (D : ℝ → ℝ) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ,ENNReal.ofReal ((D x-D (x+h))^2)

theorem differenceEnergy_measurable {D : ℝ → ℝ} (hD : Measurable D) :
    Measurable (differenceEnergy D) := by
  exact Measurable.lintegral_prod_right
    (((hD.comp measurable_snd).sub (hD.comp (measurable_snd.add measurable_fst))).pow_const 2).ennreal_ofReal

theorem gammaVariance_measurable {b : ℝ} (hb : 0<b) {D : ℝ → ℝ} (hD : Measurable D) :
    Measurable (gammaVariance b D) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  have hg : StronglyMeasurable (gammaAverage b D) :=
    ((hD.comp (measurable_fst.add (Real.measurable_log.comp measurable_snd))).stronglyMeasurable).integral_prod_right'
  have hg2 : StronglyMeasurable (gammaAverage b (fun y => (D y)^2)) :=
    (((hD.comp (measurable_fst.add (Real.measurable_log.comp measurable_snd))).pow_const 2).stronglyMeasurable).integral_prod_right'
  exact (hg2.sub (hg.pow 2)).measurable

theorem gammaVariance_ofReal_pair {b : ℝ} (hb : 0<b) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M) (x : ℝ) :
    ENNReal.ofReal (gammaVariance b D x)=ENNReal.ofReal (1/2:ℝ)*
      (∫⁻ q : ℝ×ℝ,ENNReal.ofReal ((D (x+Real.log q.1)-D (x+Real.log q.2))^2)
        ∂(gammaMeasure b 1).prod (gammaMeasure b 1)) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  have hm := gammaAverage_memLp hb hD hM x
  have hx := hm.comp_measurePreserving
    (measurePreserving_fst (μ:=gammaMeasure b 1) (ν:=gammaMeasure b 1))
  have hy := hm.comp_measurePreserving
    (measurePreserving_snd (μ:=gammaMeasure b 1) (ν:=gammaMeasure b 1))
  rw [gammaVariance_pair hb hD hM,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2)]
  congr 1
  exact ofReal_integral_eq_lintegral_ofReal (hx.sub hy).integrable_sq
    (Eventually.of_forall (fun q => sq_nonneg _))

theorem differenceEnergy_translate (D : ℝ → ℝ) (s t : ℝ) :
    (∫⁻ x : ℝ,ENNReal.ofReal ((D (x+s)-D (x+t))^2))=differenceEnergy D (t-s) := by
  have he := lintegral_add_right_eq_self (μ:=volume)
    (fun x : ℝ => ENNReal.ofReal ((D x-D (x+(t-s)))^2)) s
  simpa only [differenceEnergy,add_add_sub_cancel] using he

theorem lintegral_gammaVariance_difference {b : ℝ} (hb : 0<b) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M) :
    (∫⁻ x : ℝ,ENNReal.ofReal (gammaVariance b D x))=ENNReal.ofReal (1/2:ℝ)*
      (∫⁻ h : ℝ,ENNReal.ofReal (logRatioDensity b h)*differenceEnergy D h) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  simp_rw [gammaVariance_ofReal_pair hb hD hM]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  calc
    _ = ∫⁻ q : ℝ×ℝ,∫⁻ x : ℝ,
        ENNReal.ofReal ((D (x+Real.log q.1)-D (x+Real.log q.2))^2)
          ∂volume ∂(gammaMeasure b 1).prod (gammaMeasure b 1) := by
      rw [lintegral_lintegral_swap]
      exact (((hD.comp (measurable_fst.add
        (Real.measurable_log.comp (measurable_fst.comp measurable_snd)))).sub
        (hD.comp (measurable_fst.add
          (Real.measurable_log.comp (measurable_snd.comp measurable_snd))))).pow_const 2).ennreal_ofReal.aemeasurable
    _ = ∫⁻ q : ℝ×ℝ,differenceEnergy D (Real.log q.2-Real.log q.1)
        ∂(gammaMeasure b 1).prod (gammaMeasure b 1) := by
      apply lintegral_congr
      intro q
      exact differenceEnergy_translate D _ _
    _ = ∫⁻ h : ℝ,differenceEnergy D h ∂
        (((gammaMeasure b 1).prod (gammaMeasure b 1)).map
          (fun q : ℝ×ℝ => Real.log q.2-Real.log q.1)) := by
      rw [lintegral_map (g:=fun q : ℝ×ℝ => Real.log q.2-Real.log q.1)
        (differenceEnergy_measurable hD) (by fun_prop)]
    _ = _ := by
      rw [gamma_pair_log_difference_law hb,
        lintegral_withDensity_eq_lintegral_mul volume
          (logRatioDensity_measurable b).ennreal_ofReal (differenceEnergy_measurable hD)]
      rfl

theorem weighted_difference_identity {a : ℝ} (ha : a<1) {D : ℝ → ℝ}
    (x h : ℝ) :
    logRatioDensity (1-a) h*(D x-D (x+h))^2=
      (1/beta (1-a) (1-a))*energyDensity a D (x,x+h) := by
  unfold logRatioDensity energyDensity
  have he : (x-(x+h))/2=-(h/2) := by ring
  rw [he,Real.cosh_neg]
  have hp : 2*(1-a)=2-2*a := by ring
  rw [hp]
  ring

theorem weighted_difference_energy {a : ℝ} (ha : a<1) {D : ℝ → ℝ}
    (hD : Measurable D) :
    (∫⁻ h : ℝ,ENNReal.ofReal (logRatioDensity (1-a) h)*differenceEnergy D h)=
      ENNReal.ofReal (1/beta (1-a) (1-a))*
        (∫⁻ q : ℝ×ℝ,ENNReal.ofReal (energyDensity a D q) ∂volume.prod volume) := by
  have hB : 0<beta (1-a) (1-a) := beta_pos (by linarith) (by linarith)
  have hn (h : ℝ) : 0≤logRatioDensity (1-a) h := by
    unfold logRatioDensity
    positivity
  have he (x h : ℝ) :
      ENNReal.ofReal (logRatioDensity (1-a) h)*ENNReal.ofReal ((D x-D (x+h))^2)=
        ENNReal.ofReal (1/beta (1-a) (1-a))*ENNReal.ofReal (energyDensity a D (x,x+h)) := by
    rw [←ENNReal.ofReal_mul (hn h),weighted_difference_identity ha,
      ENNReal.ofReal_mul (one_div_pos.mpr hB).le]
  unfold differenceEnergy
  calc
    _ = ∫⁻ h : ℝ,∫⁻ x : ℝ,
        ENNReal.ofReal (logRatioDensity (1-a) h)*ENNReal.ofReal ((D x-D (x+h))^2) := by
      apply lintegral_congr
      intro h
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x : ℝ,∫⁻ h : ℝ,
        ENNReal.ofReal (logRatioDensity (1-a) h)*ENNReal.ofReal ((D x-D (x+h))^2) := by
      rw [lintegral_lintegral_swap]
      exact (((logRatioDensity_measurable (1-a)).comp measurable_fst).ennreal_ofReal.mul
        (((hD.comp measurable_snd).sub (hD.comp (measurable_snd.add measurable_fst))).pow_const 2).ennreal_ofReal).aemeasurable
    _ = ∫⁻ x : ℝ,ENNReal.ofReal (1/beta (1-a) (1-a))*
        (∫⁻ h : ℝ,ENNReal.ofReal (energyDensity a D (x,x+h))) := by
      apply lintegral_congr
      intro x
      simp_rw [he]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ x : ℝ,ENNReal.ofReal (1/beta (1-a) (1-a))*
        (∫⁻ y : ℝ,ENNReal.ofReal (energyDensity a D (x,y))) := by
      apply lintegral_congr
      intro x
      congr 1
      exact lintegral_add_left_eq_self (μ:=volume)
        (fun y : ℝ => ENNReal.ofReal (energyDensity a D (x,y))) x
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_prod _ (energyDensity_measurable hD a).ennreal_ofReal.aemeasurable]

theorem lintegral_gammaVariance_energy {a : ℝ} (ha : a<1) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M) :
    (∫⁻ x : ℝ,ENNReal.ofReal (gammaVariance (1-a) D x))=
      ENNReal.ofReal (1/(2*beta (1-a) (1-a)))*
        (∫⁻ q : ℝ×ℝ,ENNReal.ofReal (energyDensity a D q) ∂volume.prod volume) := by
  rw [lintegral_gammaVariance_difference (by linarith) hD hM,
    weighted_difference_energy ha hD,←mul_assoc,
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2)]
  congr 2
  ring

theorem gammaVariance_integrable {a : ℝ} (ha : a<1) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M)
    (hE : (∫⁻ q : ℝ×ℝ,ENNReal.ofReal (energyDensity a D q) ∂volume.prod volume)≠∞) :
    Integrable (gammaVariance (1-a) D) := by
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (gammaVariance_measurable (by linarith) hD).aestronglyMeasurable
    (Eventually.of_forall (gammaVariance_nonnegative (by linarith) hD hM))).mp
  rw [lintegral_gammaVariance_energy ha hD hM]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE

end SphericalAging.GammaVarianceEnergy
