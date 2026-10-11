module

public import SphericalAging.StationaryGammaScaling
public import SphericalAging.BetaGammaLaw

public section

/-! Actual logarithmic beta/gamma averaging and the genuine product law. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SphericalAging.StationaryBetaGammaAverage
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GammaSmoothingVariance LogBetaRenewal BetaGammaLaw

@[expose] def betaAverage (ρ a : ℝ) (F : ℝ → ℝ) (x : ℝ) := ∫ y,F (x-y) ∂law ρ a

/-- Genuine measurability of the gamma smoothing operator. -/
theorem gammaAverage_measurable (b : ℝ) (hb : 0<b) (D : ℝ → ℝ) (hD : Measurable D) :
    Measurable (gammaAverage b D) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  have hm : Measurable (fun q : ℝ×ℝ => D (q.1+Real.log q.2)) :=
    hD.comp (measurable_fst.add (Real.measurable_log.comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Genuine boundedness is preserved by the probability average. -/
theorem gammaAverage_bound (b : ℝ) (hb : 0<b) (D : ℝ → ℝ) (M : ℝ)
    (hM : ∀ y,‖D y‖≤M) (x : ℝ) : ‖gammaAverage b D x‖≤M := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  simpa only [gammaAverage,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=gammaMeasure b 1)
      (Eventually.of_forall (fun g => hM (x+Real.log g))))

/-- Genuine measurability of the causal logarithmic beta average. -/
theorem betaAverage_measurable (ρ a : ℝ) (hρ : 0<ρ) (ha : 0<a)
    (F : ℝ → ℝ) (hF : Measurable F) : Measurable (betaAverage ρ a F) := by
  letI := law_probability hρ ha
  have hm : Measurable (fun q : ℝ×ℝ => F (q.1-q.2)) :=
    hF.comp (measurable_fst.sub measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Independence and the actual beta--gamma product law intertwine both
logarithmic operators. There is no assumed averaging identity. -/
theorem betaAverage_gammaAverage (ρ a : ℝ) (hρ : 0<ρ) (ha : 0<a)
    (D : ℝ → ℝ) (hD : Measurable D) (M : ℝ) (hM : ∀ y,‖D y‖≤M) (x : ℝ) :
    betaAverage ρ a (gammaAverage (ρ+a) D) x=gammaAverage ρ D x := by
  letI := isProbabilityMeasureBeta hρ ha
  letI := isProbabilityMeasure_gammaMeasure (add_pos hρ ha) zero_lt_one
  letI := isProbabilityMeasure_gammaMeasure hρ zero_lt_one
  have hmK := gammaAverage_measurable (ρ+a) (add_pos hρ ha) D hD
  have hm : Measurable (fun q : ℝ×ℝ => D (x+Real.log q.1+Real.log q.2)) := by
    exact hD.comp ((measurable_const.add (Real.measurable_log.comp measurable_fst)).add
      (Real.measurable_log.comp measurable_snd))
  have hi : Integrable (fun q : ℝ×ℝ => D (x+Real.log q.1+Real.log q.2))
      ((betaMeasure ρ a).prod (gammaMeasure (ρ+a) 1)) :=
    (MemLp.of_bound hm.aestronglyMeasurable M
      (Eventually.of_forall (fun q => hM (x+Real.log q.1+Real.log q.2))) :
        MemLp (fun q : ℝ×ℝ => D (x+Real.log q.1+Real.log q.2)) 1
          ((betaMeasure ρ a).prod (gammaMeasure (ρ+a) 1))).integrable le_rfl
  have hp : ∀ᵐ q ∂((betaMeasure ρ a).prod (gammaMeasure (ρ+a) 1)),0<q.1 ∧ 0<q.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability : MeasurableSet {q : ℝ×ℝ | 0<q.1 ∧ 0<q.2})).mpr
    filter_upwards [beta_ae_unit_interval ρ a] with b hb
    filter_upwards [gamma_ae_positive (ρ+a)] with g hg
    exact ⟨hb.1,hg⟩
  calc
    _ = ∫ b,gammaAverage (ρ+a) D (x+Real.log b) ∂betaMeasure ρ a := by
      unfold betaAverage law
      rw [integral_map_of_stronglyMeasurable (φ:=fun b : ℝ => -Real.log b)
        (f:=fun y : ℝ => gammaAverage (ρ+a) D (x-y)) Real.measurable_log.neg
        (hmK.comp (measurable_const.sub measurable_id)).stronglyMeasurable]
      simp only [sub_neg_eq_add]
    _ = ∫ q : ℝ×ℝ,D (x+Real.log q.1+Real.log q.2)
        ∂((betaMeasure ρ a).prod (gammaMeasure (ρ+a) 1)) := by
      exact integral_integral (f:=fun b g : ℝ => D (x+Real.log b+Real.log g)) hi
    _ = ∫ q : ℝ×ℝ,D (x+Real.log (q.1*q.2))
        ∂((betaMeasure ρ a).prod (gammaMeasure (ρ+a) 1)) := by
      apply integral_congr_ae
      filter_upwards [hp] with q hq
      rw [Real.log_mul (ne_of_gt hq.1) (ne_of_gt hq.2),add_assoc]
    _ = ∫ g,D (x+Real.log g) ∂gammaMeasure ρ 1 := by
      rw [←beta_gamma_product_law hρ ha]
      rw [integral_map_of_stronglyMeasurable (φ:=fun q : ℝ×ℝ => q.1*q.2)
        (f:=fun g : ℝ => D (x+Real.log g)) (measurable_fst.mul measurable_snd)
        (hD.comp (measurable_const.add Real.measurable_log)).stronglyMeasurable]

end
end SphericalAging.StationaryBetaGammaAverage
