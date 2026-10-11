module

public import SphericalAging.StationaryPowerProfiles
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Exact real beta-integral formula for the actual shifted-power convolution. -/

open Set MeasureTheory
open scoped Topology

namespace SphericalAging.StationaryBetaConvolution

noncomputable section

open StationaryPowerProfiles StationaryNormalization

@[expose] def betaKernel (α ζ y : ℝ) : ℝ := y ^ (-α) * (1 - y) ^ (-ζ)

@[expose] def truncatedBeta (α ζ x : ℝ) : ℝ := ∫ y in x..(1 - x), betaKernel α ζ y

/-- The affine substitution s=(t+2)y-1, with all base signs proved on
the actual interval. It remains valid for -1<t, so differentiating at zero
later requires no endpoint extension assumption. -/
theorem shifted_convolution_beta (α ζ t : ℝ) (ht : -1 < t) :
    causalConvolution (shiftedPower α) (shiftedPower ζ) t =
      (t + 2) ^ (1 - α - ζ) * truncatedBeta α ζ (1 / (t + 2)) := by
  let T := t + 2
  let x := 1 / T
  have hT : 0 < T := by dsimp [T]; linarith
  have hT1 : 1 < T := by dsimp [T]; linarith
  have hx0 : 0 < x := one_div_pos.mpr hT
  have hx1 : x < 1 := by
    have hh := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hT1
    simpa only [one_div_one] using hh
  have hend0 : T * x + (-1) = 0 := by dsimp only [x]; field_simp [hT.ne']; ring
  have hendt : T * (1 - x) + (-1) = t := by
    dsimp only [x]
    field_simp [hT.ne']
    dsimp [T]
    ring
  have hcomp := intervalIntegral.smul_integral_comp_mul_add
    (fun s => shiftedPower ζ (t - s) * shiftedPower α s) T (-1)
    (a := x) (b := 1 - x)
  simp only [smul_eq_mul, hend0, hendt] at hcomp
  have hintegrand (y : ℝ) (hy : y ∈ uIcc x (1 - x)) :
      shiftedPower ζ (t - (T * y + (-1))) * shiftedPower α (T * y + (-1)) =
      T ^ (-α - ζ) * betaKernel α ζ y := by
    have hy0 : 0 < y := by
      rcases mem_uIcc.mp hy with hy | hy <;> linarith
    have hy1 : y < 1 := by
      rcases mem_uIcc.mp hy with hy | hy <;> linarith
    have hbase1 : 1 + (t - (T * y + (-1))) = T * (1 - y) := by dsimp [T]; ring
    have hbase2 : 1 + (T * y + (-1)) = T * y := by ring
    unfold shiftedPower betaKernel
    rw [hbase1, hbase2, Real.mul_rpow hT.le (by linarith : 0 ≤ 1 - y),
      Real.mul_rpow hT.le hy0.le]
    rw [show -α - ζ = (-α) + (-ζ) by ring, Real.rpow_add hT]
    ring
  have hi : (∫ y in x..(1 - x),
      shiftedPower ζ (t - (T * y + (-1))) * shiftedPower α (T * y + (-1))) =
      T ^ (-α - ζ) * truncatedBeta α ζ x := by
    unfold truncatedBeta
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    exact hintegrand
  rw [hi] at hcomp
  have hpow : T * T ^ (-α - ζ) = T ^ (1 - α - ζ) := by
    rw [show 1 - α - ζ = 1 + (-α - ζ) by ring, Real.rpow_add hT, Real.rpow_one]
  rw [← mul_assoc, hpow] at hcomp
  rw [StationaryComparison.causalConvolution_comm]
  exact hcomp.symm

theorem betaKernel_hasDerivAt (α ζ x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (betaKernel α ζ)
      (-α * x ^ (-α - 1) * (1 - x) ^ (-ζ) +
        ζ * x ^ (-α) * (1 - x) ^ (-ζ - 1)) x := by
  have hd1 := (hasDerivAt_id x).rpow_const (p := -α) (Or.inl hx0.ne')
  have hd2 := ((hasDerivAt_id x).const_sub 1).rpow_const (p := -ζ)
    (Or.inl (by change 1 - x ≠ 0; linarith))
  convert hd1.mul hd2 using 1
  · rfl
  · simp only [id_eq]
    ring

theorem betaKernel_measurable (α ζ : ℝ) : Measurable (betaKernel α ζ) := by
  unfold betaKernel
  fun_prop

theorem betaKernel_intervalIntegrable (α ζ x y : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    IntervalIntegrable (betaKernel α ζ) volume x y := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  have hz0 : 0 < z := by rcases mem_uIcc.mp hz with hz | hz <;> linarith
  have hz1 : z < 1 := by rcases mem_uIcc.mp hz with hz | hz <;> linarith
  exact (betaKernel_hasDerivAt α ζ z hz0 hz1).continuousAt.continuousWithinAt

/-- The two actual moving beta-integral endpoints both contribute a
negative derivative in x. -/
theorem truncatedBeta_hasDerivAt (α ζ x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (truncatedBeta α ζ) (-betaKernel α ζ x - betaKernel α ζ (1 - x)) x := by
  let F := fun z => ∫ y in x..z, betaKernel α ζ y
  have hmeas (z : ℝ) : StronglyMeasurableAtFilter (betaKernel α ζ) (𝓝 z) volume :=
    (betaKernel_measurable α ζ).stronglyMeasurable.stronglyMeasurableAtFilter
  have hdx : HasDerivAt F (betaKernel α ζ x) x :=
    intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl)
      (hmeas x) (betaKernel_hasDerivAt α ζ x hx0 hx1).continuousAt
  have hd1 : HasDerivAt F (betaKernel α ζ (1 - x)) (1 - x) :=
    intervalIntegral.integral_hasDerivAt_right
      (betaKernel_intervalIntegrable α ζ x (1 - x) hx0 hx1 (by linarith) (by linarith))
      (hmeas (1 - x)) (betaKernel_hasDerivAt α ζ (1 - x) (by linarith) (by linarith)).continuousAt
  have hd := (hd1.comp x ((hasDerivAt_id x).const_sub 1)).sub hdx
  have hexpr : HasDerivAt (fun z => F (1 - z) - F z)
      (-betaKernel α ζ x - betaKernel α ζ (1 - x)) x := by
    convert hd using 1
    · rfl
    · ring
  have heq : truncatedBeta α ζ =ᶠ[𝓝 x] (fun z => F (1 - z) - F z) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with z hz
    have hixz := betaKernel_intervalIntegrable α ζ x z hx0 hx1 hz.1 hz.2
    have hiz1 := betaKernel_intervalIntegrable α ζ z (1 - z) hz.1 hz.2 (by linarith [hz.2]) (by linarith [hz.1])
    have hadd := intervalIntegral.integral_add_adjacent_intervals hixz hiz1
    dsimp [truncatedBeta, F]
    linarith
  exact hexpr.congr_of_eventuallyEq heq

/-- Differentiate the actual shifted convolution by its proved beta formula.
The formula holds on an open neighborhood even when t=0. -/
theorem shifted_convolution_hasDerivAt (α ζ t : ℝ) (ht : -1 < t) :
    HasDerivAt (causalConvolution (shiftedPower α) (shiftedPower ζ))
      ((t + 2) ^ (-α - ζ) * ((1 - α - ζ) * truncatedBeta α ζ (1 / (t + 2)) +
        (1 / (t + 2)) * betaKernel α ζ (1 / (t + 2)) +
        (1 / (t + 2)) * betaKernel α ζ (1 - 1 / (t + 2)))) t := by
  let T := t + 2
  let x := 1 / T
  have hT : 0 < T := by dsimp [T]; linarith
  have hT1 : 1 < T := by dsimp [T]; linarith
  have hx0 : 0 < x := one_div_pos.mpr hT
  have hx1 : x < 1 := by
    have hh := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hT1
    simpa only [one_div_one] using hh
  have hpow : HasDerivAt (fun z : ℝ => (z + 2) ^ (1 - α - ζ))
      ((1 - α - ζ) * T ^ (-α - ζ)) t := by
    have hd := ((hasDerivAt_id t).add_const 2).rpow_const
      (p := 1 - α - ζ) (Or.inl hT.ne')
    convert hd using 1
    · rfl
    · simp only [one_mul, id_eq]
      rw [show 1 - α - ζ - 1 = -α - ζ by ring]
  have hinv : HasDerivAt (fun z : ℝ => 1 / (z + 2)) (-1 / T ^ 2) t := by
    have hd := ((hasDerivAt_id t).add_const 2).inv hT.ne'
    convert hd using 1
    · funext z
      simp only [one_div, Pi.inv_apply, id_eq]
    · rfl
  have hbeta := (truncatedBeta_hasDerivAt α ζ x hx0 hx1).comp t hinv
  have hd := hpow.mul hbeta
  have hext : HasDerivAt (fun z : ℝ => (z + 2) ^ (1 - α - ζ) *
      truncatedBeta α ζ (1 / (z + 2)))
      (T ^ (-α - ζ) * ((1 - α - ζ) * truncatedBeta α ζ x +
        x * betaKernel α ζ x + x * betaKernel α ζ (1 - x))) t := by
    convert hd using 1
    · rfl
    · have hp : T ^ (1 - α - ζ) = T * T ^ (-α - ζ) := by
        rw [show 1 - α - ζ = 1 + (-α - ζ) by ring, Real.rpow_add hT, Real.rpow_one]
      simp only [Function.comp_apply]
      rw [show t + 2 = T by rfl, hp]
      dsimp only [x]
      field_simp [hT.ne']
      ring
  have heq : causalConvolution (shiftedPower α) (shiftedPower ζ) =ᶠ[𝓝 t]
      (fun z => (z + 2) ^ (1 - α - ζ) * truncatedBeta α ζ (1 / (z + 2))) := by
    filter_upwards [Ioi_mem_nhds ht] with z hz
    exact shifted_convolution_beta α ζ z hz
  exact hext.congr_of_eventuallyEq heq

/-- The exact derivative display in Step1 of Lemma16.5, with the two
positive boundary powers written explicitly. -/
theorem shifted_convolution_derivative (α ζ t : ℝ) (ht : -1 < t) :
    deriv (causalConvolution (shiftedPower α) (shiftedPower ζ)) t =
      (t + 2) ^ (-α - ζ) * ((1 - α - ζ) * truncatedBeta α ζ (1 / (t + 2)) +
        (1 / (t + 2)) ^ (1 - α) * (1 - 1 / (t + 2)) ^ (-ζ) +
        (1 / (t + 2)) ^ (1 - ζ) * (1 - 1 / (t + 2)) ^ (-α)) := by
  rw [(shifted_convolution_hasDerivAt α ζ t ht).deriv]
  have hx : 0 < 1 / (t + 2) := one_div_pos.mpr (by linarith)
  have hpower (b : ℝ) : (1 / (t + 2)) ^ (1 - b) =
      (1 / (t + 2)) * (1 / (t + 2)) ^ (-b) := by
    rw [show 1 - b = 1 + (-b) by ring, Real.rpow_add hx, Real.rpow_one]
  simp only [betaKernel, sub_sub_cancel, hpower]
  ring

/-- The complex integrand underlying Mathlib's proved beta integral. -/
@[expose] def complexBetaKernel (α ζ : ℝ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (((1 - α : ℝ) : ℂ) - 1) *
    (1 - (y : ℂ)) ^ (((1 - ζ : ℝ) : ℂ) - 1)

theorem complexBetaKernel_eq_ofReal (α ζ y : ℝ) (hy : y ∈ Icc 0 1) :
    complexBetaKernel α ζ y = (betaKernel α ζ y : ℂ) := by
  have hα : (((1 - α : ℝ) : ℂ) - 1) = ((-α : ℝ) : ℂ) := by push_cast; ring
  have hζ : (((1 - ζ : ℝ) : ℂ) - 1) = ((-ζ : ℝ) : ℂ) := by push_cast; ring
  unfold complexBetaKernel betaKernel
  rw [hα, hζ, show 1 - (y : ℂ) = ((1 - y : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hy.1, ← Complex.ofReal_cpow (sub_nonneg.mpr hy.2),
    ← Complex.ofReal_mul]

theorem betaKernel_integrable_unit (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    IntervalIntegrable (betaKernel α ζ) volume 0 1 := by
  have hC : IntervalIntegrable (complexBetaKernel α ζ) volume 0 1 :=
    Complex.betaIntegral_convergent (by simpa using (show 0 < 1 - α by linarith))
      (by simpa using (show 0 < 1 - ζ by linarith))
  have hR : IntervalIntegrable (fun y => (complexBetaKernel α ζ y).re) volume 0 1 :=
    ⟨Complex.reCLM.integrable_comp hC.1, Complex.reCLM.integrable_comp hC.2⟩
  apply hR.congr
  intro y hy
  have hy' : y ∈ Icc 0 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc hy
  change (complexBetaKernel α ζ y).re = betaKernel α ζ y
  rw [complexBetaKernel_eq_ofReal α ζ y hy']
  simp

/-- The real beta integral is the proved Gamma ratio in Mathlib. -/
theorem betaKernel_integral_unit (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    (∫ y in 0..1, betaKernel α ζ y) = ProbabilityTheory.beta (1 - α) (1 - ζ) := by
  have hC : IntervalIntegrable (complexBetaKernel α ζ) volume 0 1 :=
    Complex.betaIntegral_convergent (by simpa using (show 0 < 1 - α by linarith))
      (by simpa using (show 0 < 1 - ζ by linarith))
  rw [ProbabilityTheory.beta_eq_betaIntegralReal (1 - α) (1 - ζ) (by linarith) (by linarith)]
  unfold Complex.betaIntegral
  change (∫ y in 0..1, betaKernel α ζ y) = (∫ y in 0..1, complexBetaKernel α ζ y).re
  have hi : (∫ y in 0..1, (complexBetaKernel α ζ y).re) =
      (∫ y in 0..1, complexBetaKernel α ζ y).re := by
    convert intervalIntegral.intervalIntegral_re hC using 1
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc 0 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  change betaKernel α ζ y = (complexBetaKernel α ζ y).re
  rw [complexBetaKernel_eq_ofReal α ζ y hy']
  simp

/-- The truncated beta integral extends continuously to both endpoints,
using actual L¹ integrability of the singular beta kernel. -/
theorem truncatedBeta_continuousOn_unit (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    ContinuousOn (truncatedBeta α ζ) (Icc 0 1) := by
  let F := fun z => ∫ y in 0..z, betaKernel α ζ y
  have hi := betaKernel_integrable_unit α ζ hα hζ
  have hFc : ContinuousOn F (Icc 0 1) := by
    have hc := intervalIntegral.continuousOn_primitive_interval' hi (a := 0) left_mem_uIcc
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
  have hreflect : MapsTo (fun z : ℝ => 1 - z) (Icc 0 1) (Icc 0 1) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  have hc : ContinuousOn (fun z => F (1 - z) - F z) (Icc 0 1) :=
    (hFc.comp (continuous_const.sub continuous_id).continuousOn hreflect).sub hFc
  apply hc.congr
  intro z hz
  have h0z : uIcc 0 z ⊆ uIcc 0 1 := by
    rw [uIcc_of_le hz.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hz.2
  have hz1z : uIcc z (1 - z) ⊆ uIcc 0 1 := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rcases mem_uIcc.mp hy with hy | hy <;> constructor <;> linarith [hz.1, hz.2]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi.mono_set h0z) (hi.mono_set hz1z)
  dsimp [F, truncatedBeta]
  linarith

theorem truncatedBeta_zero (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    truncatedBeta α ζ 0 = ProbabilityTheory.beta (1 - α) (1 - ζ) := by
  simpa only [truncatedBeta, sub_zero] using betaKernel_integral_unit α ζ hα hζ

end
end SphericalAging.StationaryBetaConvolution
