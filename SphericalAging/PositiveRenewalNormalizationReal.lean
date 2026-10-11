module

public import SphericalAging.PositiveRenewalNormalization
public import SphericalAging.PositiveRenewalCompactKernel

public section

/-! Literal Bochner-integral survival normalization of actual nonnegative
compact-kernel renewal convolutions under exactly the finite first moment. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalNormalizationReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalNormalization PositiveRenewalTailMean PositiveRenewalCompactKernel
open AbsorptionCutoff.Renewal

theorem nonnegative_renewalConvolution {μ : Measure ℝ} {H : ℝ → ℝ}
    (hn : ∀t : ℝ,0≤H t) (x : ℝ) : 0≤renewalConvolution μ H x :=
  integral_nonneg (fun y => hn (x-y))

theorem nnAverage_ofReal_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {H : ℝ → ℝ} (hm : Measurable H)
    {R B : ℝ} (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (hn : ∀t : ℝ,0≤H t) (x : ℝ) :
    nnAverage μ (fun t => ENNReal.ofReal (H t)) x=ENNReal.ofReal (renewalConvolution μ H x) :=
  (ofReal_integral_eq_lintegral_ofReal (compact_kernel_integrable hp hm hs hb x)
    (Eventually.of_forall (fun y => hn (x-y)))).symm

/-- The actual survival-weighted renewal convolution has the actual
truncated integral of its kernel as mass. -/
theorem survival_renewalConvolution_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ)
    {H : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K H) {R B : ℝ}
    (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (hn : ∀t : ℝ,0≤H t) (x : ℝ) :
    (∫t,causalSurvival μ t*renewalConvolution μ H (x-t))=∫s in Iic x,H s := by
  let F := renewalConvolution μ H
  let T := causalSurvival μ
  have hFc : Continuous F := (compact_kernel_lipschitz hp hL hs hb).continuous
  have hFb := compact_kernel_uniform_bound hp hs hb
  have hTi : Integrable T := causalSurvival_integrable hp hi
  have hprod : Integrable (fun t : ℝ => T t*F (x-t)) :=
    hTi.mul_bdd ((hFc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall (fun t => hFb (x-t)))
  have hprodnn (t : ℝ) : 0≤T t*F (x-t) :=
    mul_nonneg (causalSurvival_nonnegative μ t) (nonnegative_renewalConvolution hn (x-t))
  have hHi : Integrable H := by
    exact hL.continuous.integrableOn_Icc.integrable_of_forall_notMem_eq_zero hs
  have hN := survival_nnAverage hp (fun t => ENNReal.ofReal (H t))
    hL.continuous.measurable.ennreal_ofReal x
  simp_rw [nnAverage_ofReal_eq hp hL.continuous.measurable hs hb hn] at hN
  have hLeft : ENNReal.ofReal (∫t,T t*F (x-t))=
      ∫⁻t,ENNReal.ofReal (T t)*ENNReal.ofReal (F (x-t)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hprod (Eventually.of_forall hprodnn)]
    apply lintegral_congr
    intro t
    exact ENNReal.ofReal_mul (causalSurvival_nonnegative μ t)
  have hRight : ENNReal.ofReal (∫s in Iic x,H s)=∫⁻s in Iic x,ENNReal.ofReal (H s) :=
    ofReal_integral_eq_lintegral_ofReal hHi.integrableOn (Eventually.of_forall hn)
  have hEq : ENNReal.ofReal (∫t,T t*F (x-t))=ENNReal.ofReal (∫s in Iic x,H s) :=
    hLeft.trans (hN.trans hRight.symm)
  have ht := congrArg ENNReal.toReal hEq
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hprodnn),
    ENNReal.toReal_ofReal (integral_nonneg hn)] using ht

/-- After the compact kernel has been crossed, the survival normalization
is exactly its full ordinary integral. -/
theorem survival_renewalConvolution_integral_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ)
    {H : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K H) {R B : ℝ}
    (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (hn : ∀t : ℝ,0≤H t) {x : ℝ} (hx : R≤x) :
    (∫t,causalSurvival μ t*renewalConvolution μ H (x-t))=∫s,H s := by
  rw [survival_renewalConvolution_integral hp hi hL hs hb hn]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hsx
  apply hs
  intro hsR
  exact hsx (hsR.2.trans hx)

end
end SphericalAging.PositiveRenewalNormalizationReal
