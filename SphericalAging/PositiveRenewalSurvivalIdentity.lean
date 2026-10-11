module

public import SphericalAging.PositiveRenewalTailMean
public import SphericalAging.RenewalRemainder
public import SphericalAging.PositiveRenewalCellBound

public section

/-! The genuine renewal survival identity. It follows from the actual
renewal equation for the causal constant function, finite telescoping and
the positive-support Chernoff estimate. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalSurvivalIdentity
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalTailMean RenewalRemainder AbsorptionCutoff.Renewal

@[expose] def causalUnit : ℝ → ℝ := (Ici 0).indicator (fun _ => 1)

theorem causalUnit_measurable : Measurable causalUnit :=
  measurable_const.indicator measurableSet_Ici

theorem causalUnit_bound (x : ℝ) : ‖causalUnit x‖≤1 := by
  by_cases hx : x∈Ici (0:ℝ)
  · simp [causalUnit,indicator_of_mem hx]
  · simp [causalUnit,indicator_of_notMem hx]

theorem causalUnit_nonnegative (x : ℝ) : 0≤causalUnit x :=
  indicator_nonneg (fun _ _ => zero_le_one) x

theorem causalUnit_atBot : Tendsto causalUnit atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  exact (indicator_of_notMem (show x∉Ici (0:ℝ) from not_le_of_gt hx) _).symm

theorem causalUnit_average (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    renewalAverage μ causalUnit 1 x=μ.real (Iic x) := by
  have heq : (fun y : ℝ => causalUnit (x-y))=(Iic x).indicator (fun _ => (1:ℝ)) := by
    funext y
    by_cases hy : y≤x
    · rw [indicator_of_mem (show y∈Iic x from hy)]
      exact indicator_of_mem (sub_nonneg.mpr hy) _
    · rw [indicator_of_notMem (show y∉Iic x from hy)]
      exact indicator_of_notMem (not_le.mpr (sub_neg.mpr (lt_of_not_ge hy))) _
  unfold renewalAverage
  rw [convPow_one,heq,integral_indicator measurableSet_Iic,integral_const]
  simp only [measureReal_restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul,mul_one]

theorem causalUnit_renewal_equation {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (x : ℝ) :
    causalUnit x-renewalAverage μ causalUnit 1 x=causalSurvival μ x := by
  rw [causalUnit_average]
  by_cases hx : 0≤x
  · rw [show causalUnit x=1 from indicator_of_mem hx _,
      show causalSurvival μ x=survival μ x from indicator_of_mem hx _]
    change 1-μ.real (Iic x)=μ.real (Ioi x)
    simpa only [compl_Iic] using
      (probReal_compl_eq_one_sub (μ:=μ) (s:=Iic x) measurableSet_Iic).symm
  · have hzero : μ.real (Iic x)=0 := by
      apply (measureReal_eq_zero_iff).mpr
      have hNot : ∀ᵐ y ∂μ,y∉Iic x := hp.mono (fun y hy =>
        not_le.mpr (lt_trans (lt_of_not_ge hx) hy))
      change μ {y : ℝ | y≤x}=0
      simpa only [not_not,mem_Iic] using ae_iff.mp hNot
    rw [show causalUnit x=0 from indicator_of_notMem hx _,
      show causalSurvival μ x=0 from indicator_of_notMem hx _,hzero]
    ring

/-- The actual infinite convolution series of survival probabilities
sums to one on the positive ray (and to zero at negative times). -/
theorem survival_renewal_hasSum {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (x : ℝ) :
    HasSum (fun n : ℕ => renewalAverage μ (causalSurvival μ) n x) (causalUnit x) := by
  have hBound : ∀y : ℝ,‖causalSurvival μ y‖≤1 := by
    intro y
    rw [Real.norm_eq_abs,abs_of_nonneg (causalSurvival_nonnegative μ y)]
    exact causalSurvival_le_one μ y
  have hEq := finite_renewal_iteration μ causalUnit (causalSurvival μ)
    causalUnit_measurable (causalSurvival_measurable μ) 1 1 causalUnit_bound hBound
    (causalUnit_renewal_equation hp)
  have hRem := renewalAverage_tendsto_zero μ 1 (by norm_num)
    (KeyRenewal.expTransform_lt_one_of_positive_support (by norm_num : (0:ℝ)<1) hp)
    causalUnit causalUnit_measurable 1 (by norm_num) causalUnit_bound causalUnit_atBot x
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n =>
    integral_nonneg (fun y => causalSurvival_nonnegative μ (x-y))) (causalUnit x)).mpr
  have hLim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => causalUnit x) atTop (𝓝 (causalUnit x))).sub hRem
  apply (show Tendsto (fun n : ℕ => causalUnit x-renewalAverage μ causalUnit n x) atTop
      (𝓝 (causalUnit x)) from by simpa only [sub_zero] using hLim).congr'
  exact Eventually.of_forall (fun n => by
    have he := hEq n x
    dsimp [renewalAverage] at he ⊢
    linarith)

/-- Literal integration against the actual renewal measure. -/
theorem lintegral_survival_renewal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (x : ℝ) :
    (∫⁻ y,ENNReal.ofReal (causalSurvival μ (x-y)) ∂renewalMeasure μ)=
      ENNReal.ofReal (causalUnit x) := by
  have hs := survival_renewal_hasSum hp x
  have hnn (n : ℕ) : 0≤renewalAverage μ (causalSurvival μ) n x :=
    integral_nonneg (fun y => causalSurvival_nonnegative μ (x-y))
  have hterm (n : ℕ) :
      ENNReal.ofReal (renewalAverage μ (causalSurvival μ) n x)=
        ∫⁻ y,ENNReal.ofReal (causalSurvival μ (x-y)) ∂convPow μ n := by
    apply ofReal_integral_eq_lintegral_ofReal
    · apply Integrable.of_bound
        ((causalSurvival_measurable μ).comp (measurable_const.sub measurable_id)).aestronglyMeasurable 1
      apply Eventually.of_forall
      intro y
      change ‖causalSurvival μ (x-y)‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg (causalSurvival_nonnegative μ (x-y))]
      exact causalSurvival_le_one μ (x-y)
    · exact Eventually.of_forall (fun y => causalSurvival_nonnegative μ (x-y))
  rw [lintegral_renewalMeasure]
  simp_rw [←hterm]
  rw [←ENNReal.ofReal_tsum_of_nonneg hnn hs.summable,hs.tsum_eq]

theorem lintegral_survival_renewal_eq_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {x : ℝ} (hx : 0≤x) :
    (∫⁻ y,ENNReal.ofReal (causalSurvival μ (x-y)) ∂renewalMeasure μ)=1 := by
  rw [lintegral_survival_renewal hp]
  rw [show causalUnit x=1 from indicator_of_mem (show x∈Ici (0:ℝ) from hx) _]
  exact ENNReal.ofReal_one

end
end SphericalAging.PositiveRenewalSurvivalIdentity
