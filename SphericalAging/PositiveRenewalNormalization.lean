module

public import SphericalAging.PositiveRenewalSurvivalIdentity
public import Mathlib.MeasureTheory.Group.Integral

public section

/-! Genuine normalization of a positive renewal convolution by the
survival function, obtained by Tonelli and the proved survival identity. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalTailMean PositiveRenewalSurvivalIdentity AbsorptionCutoff.Renewal

@[expose] def nnAverage (μ : Measure ℝ) (Z : ℝ → ℝ≥0∞) (x : ℝ) :=
  ∫⁻ y,Z (x-y) ∂renewalMeasure μ

/-- The exact integrated normalization, with no renewal limit, moment
bound or assumed convolution identity. -/
theorem survival_nnAverage {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (Z : ℝ → ℝ≥0∞) (hZ : Measurable Z) (x : ℝ) :
    (∫⁻ t,ENNReal.ofReal (causalSurvival μ t)*nnAverage μ Z (x-t))=
      ∫⁻ s in Iic x,Z s := by
  let U := renewalMeasure μ
  let T : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (causalSurvival μ t)
  have hT : Measurable T := (causalSurvival_measurable μ).ennreal_ofReal
  let : SFinite U := by dsimp [U,renewalMeasure];infer_instance
  have hFirst : Measurable (fun p : ℝ×ℝ => T p.1*Z (x-p.1-p.2)) :=
    (hT.comp measurable_fst).mul
      (hZ.comp ((measurable_const.sub measurable_fst).sub measurable_snd))
  have hSecond : Measurable (fun p : ℝ×ℝ => Z p.2*T (x-p.1-p.2)) :=
    (hZ.comp measurable_snd).mul
      (hT.comp ((measurable_const.sub measurable_fst).sub measurable_snd))
  calc
    _=∫⁻ t,(∫⁻ y,T t*Z (x-t-y) ∂U) ∂volume := by
      apply lintegral_congr
      intro t
      exact (lintegral_const_mul (T t)
        (hZ.comp ((measurable_const.sub measurable_const).sub measurable_id))).symm
    _=∫⁻ y,(∫⁻ t,T t*Z (x-t-y) ∂volume) ∂U :=
      lintegral_lintegral_swap hFirst.aemeasurable
    _=∫⁻ y,(∫⁻ s,Z s*T (x-y-s) ∂volume) ∂U := by
      apply lintegral_congr
      intro y
      have hm : Measurable (fun s : ℝ => Z s*T (x-y-s)) :=
        hZ.mul (hT.comp (measurable_const.sub measurable_id))
      calc
        _=∫⁻ t,Z ((x-y)-t)*T (x-y-((x-y)-t)) := by
          apply lintegral_congr
          intro t
          rw [show x-t-y=(x-y)-t by ring,show x-y-((x-y)-t)=t by ring,mul_comm]
        _=∫⁻ s,Z s*T (x-y-s) := (volume.measurePreserving_sub_left (x-y)).lintegral_comp hm
    _=∫⁻ s,(∫⁻ y,Z s*T (x-y-s) ∂U) ∂volume :=
      lintegral_lintegral_swap hSecond.aemeasurable
    _=∫⁻ s,Z s*ENNReal.ofReal (causalUnit (x-s)) := by
      apply lintegral_congr
      intro s
      have hm : Measurable (fun y : ℝ => T (x-y-s)) :=
        hT.comp ((measurable_const.sub measurable_id).sub measurable_const)
      rw [lintegral_const_mul (Z s) hm]
      congr 1
      change (∫⁻ y,ENNReal.ofReal (causalSurvival μ (x-y-s)) ∂renewalMeasure μ)=_
      simp_rw [show ∀y : ℝ,x-y-s=(x-s)-y by intro y;ring]
      exact lintegral_survival_renewal hp (x-s)
    _=∫⁻ s in Iic x,Z s := by
      rw [←lintegral_indicator measurableSet_Iic]
      apply lintegral_congr
      intro s
      by_cases hs : s≤x
      · rw [show causalUnit (x-s)=1 from indicator_of_mem (sub_nonneg.mpr hs) _,
          ENNReal.ofReal_one,mul_one,indicator_of_mem (show s∈Iic x from hs)]
      · rw [show causalUnit (x-s)=0 from
          indicator_of_notMem (not_le.mpr (sub_neg.mpr (lt_of_not_ge hs))) _,
          ENNReal.ofReal_zero,mul_zero,indicator_of_notMem (show s∉Iic x from hs)]

end
end SphericalAging.PositiveRenewalNormalization
