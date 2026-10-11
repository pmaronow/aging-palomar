module

public import SphericalAging.LogBetaEnvelope
public import SphericalAging.StationaryConvolutionDerivative
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.WithDensity

public section

/-! Genuine scalar convolutions and beta estimates for positive-support
exponential-power envelopes. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SphericalAging.GammaEnvelopeConvolution
noncomputable section
open StationaryBetaConvolution StationaryNormalization StationaryConvolutionDerivative

@[expose] def scalarConvolution (F G : ℝ → ℝ) (t : ℝ) := ∫ s : ℝ,F s*G (t-s)

structure EnvelopeInput (F : ℝ → ℝ) (A α κ : ℝ) : Prop where
  measurable : Measurable F
  nonnegative : ∀t,0≤F t
  zero : ∀t≤0,F t=0
  bound : ∀t>0,F t≤A*t^(α-1)*Real.exp (-κ*t)

theorem scalarConvolution_measurable (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G) :
    Measurable (scalarConvolution F G) := by
  have hm : Measurable (fun z : ℝ×ℝ => F z.2*G (z.1-z.2)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem scalarConvolution_nonnegative (F G : ℝ → ℝ) (hF : ∀t,0≤F t) (hG : ∀t,0≤G t) :
    ∀t,0≤scalarConvolution F G t := by
  intro t
  exact integral_nonneg (fun s => mul_nonneg (hF s) (hG (t-s)))

theorem scalarConvolution_zero (F G : ℝ → ℝ) (hF : ∀t≤0,F t=0) (hG : ∀t≤0,G t=0)
    (t : ℝ) (ht : t≤0) : scalarConvolution F G t=0 := by
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall (fun s => by
    change F s*G (t-s)=0
    by_cases hs : s≤0
    · rw [hF s hs,zero_mul]
    · rw [hG (t-s) (by linarith),mul_zero])

theorem scalarConvolution_unit_interval (F G : ℝ → ℝ)
    (hF : ∀t≤0,F t=0) (hG : ∀t≤0,G t=0) (t : ℝ) (ht : 0<t) :
    scalarConvolution F G t=t*(∫ z in 0..1,F (t*z)*G (t*(1-z))) := by
  have heq : (fun s => F s*G (t-s))=(Icc 0 t).indicator (fun s => G (t-s)*F s) := by
    funext s
    by_cases hs : s∈Icc 0 t
    · simp only [indicator_of_mem hs];ring
    · rw [indicator_of_notMem hs]
      rcases not_and_or.mp hs with hl|hr
      · rw [hF s (by linarith),zero_mul]
      · rw [hG (t-s) (by linarith),mul_zero]
  unfold scalarConvolution
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le ht.le,←causalConvolution,causal_unit_interval]
  congr 1
  apply intervalIntegral.integral_congr
  intro z _
  ring

/-- Actual beta-kernel factorization of an exponential-power majorant on
positive unit-simplex arguments. -/
theorem unit_envelope_product (A B α ζ κ t z : ℝ) (ht : 0<t) (hz : z∈Ioo 0 1) :
    (A*(t*z)^(α-1)*Real.exp (-κ*(t*z)))*
      (B*(t*(1-z))^(ζ-1)*Real.exp (-κ*(t*(1-z))))=
      (A*B*t^(α+ζ-2)*Real.exp (-κ*t))*betaKernel (1-α) (1-ζ) z := by
  have hp : 0<1-z := by linarith [hz.2]
  rw [Real.mul_rpow ht.le hz.1.le,Real.mul_rpow ht.le hp.le]
  have he : Real.exp (-κ*(t*z))*Real.exp (-κ*(t*(1-z)))=Real.exp (-κ*t) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hr : t^(α-1)*t^(ζ-1)=t^(α+ζ-2) := by rw [←Real.rpow_add ht];congr 1;ring
  unfold betaKernel
  rw [show -(1-α)=α-1 by ring,show -(1-ζ)=ζ-1 by ring]
  calc
    _ = A*B*(t^(α-1)*t^(ζ-1))*(Real.exp (-κ*(t*z))*Real.exp (-κ*(t*(1-z))))*
      (z^(α-1)*(1-z)^(ζ-1)) := by ring
    _ = _ := by rw [he,hr]

theorem scalarConvolution_envelope (F G : ℝ → ℝ) (A B α ζ κ : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hα : 0<α) (hζ : 0<ζ)
    (hF : EnvelopeInput F A α κ) (hG : EnvelopeInput G B ζ κ) (t : ℝ) (ht : 0<t) :
    Integrable (fun s => F s*G (t-s)) ∧
    scalarConvolution F G t≤A*B*beta α ζ*t^(α+ζ-1)*Real.exp (-κ*t) := by
  let C := A*B*t^(α+ζ-2)*Real.exp (-κ*t)
  have hC : 0≤C := by dsimp [C];positivity
  have hb : IntervalIntegrable (betaKernel (1-α) (1-ζ)) volume 0 1 :=
    betaKernel_integrable_unit (1-α) (1-ζ) (by linarith) (by linarith)
  have hmajor (z : ℝ) (hz : z∈Ioo 0 1) :
      F (t*z)*G (t*(1-z))≤C*betaKernel (1-α) (1-ζ) z := by
    have hs : 0<t*z := mul_pos ht hz.1
    have hr : 0<t*(1-z) := mul_pos ht (by linarith [hz.2])
    exact (mul_le_mul (hF.bound _ hs) (hG.bound _ hr) (hG.nonnegative _) (by positivity)).trans_eq
      (unit_envelope_product A B α ζ κ t z ht hz)
  have hiUnit : IntervalIntegrable (fun z => F (t*z)*G (t*(1-z))) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr
    apply (((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp hb).const_mul C).mono'
    · exact ((hF.measurable.comp (by fun_prop)).mul (hG.measurable.comp (by fun_prop))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      change ‖F (t*z)*G (t*(1-z))‖≤C*betaKernel (1-α) (1-ζ) z
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hF.nonnegative _) (hG.nonnegative _))]
      exact hmajor z hz
  have hiScaled : IntervalIntegrable (fun s => F s*G (t-s)) volume 0 t := by
    apply (IntervalIntegrable.comp_mul_left_iff ht.ne' (a:=0) (b:=t)).mp
    convert hiUnit using 1
    · funext z
      congr 1
      ring
    · simp
    · simp [ht.ne']
  have hFull : Integrable (fun s => F s*G (t-s)) := by
    have hIoo := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hiScaled
    have hInd := (integrable_indicator_iff measurableSet_Ioo).mpr hIoo
    convert hInd using 1
    funext s
    by_cases hs : s∈Ioo 0 t
    · simp [hs]
    · rw [indicator_of_notMem hs]
      rcases not_and_or.mp hs with hl|hr
      · rw [hF.zero s (by linarith),zero_mul]
      · rw [hG.zero (t-s) (by linarith),mul_zero]
  refine ⟨hFull,?_⟩
  have hInt := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1) hiUnit (hb.const_mul C) hmajor
  rw [intervalIntegral.integral_const_mul,betaKernel_integral_unit (1-α) (1-ζ) (by linarith) (by linarith)] at hInt
  simp only [sub_sub_cancel] at hInt
  have hh := mul_le_mul_of_nonneg_left hInt ht.le
  rw [←scalarConvolution_unit_interval F G hF.zero hG.zero t ht] at hh
  have hr : t*t^(α+ζ-2)=t^(α+ζ-1) := by
    calc
      _ = t^(1:ℝ)*t^(α+ζ-2) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add ht];congr 1;ring
  convert hh using 1
  dsimp [C]
  calc
    _ = A*B*beta α ζ*(t*t^(α+ζ-2))*Real.exp (-κ*t) := by rw [hr]
    _ = _ := by ring

end
end SphericalAging.GammaEnvelopeConvolution
