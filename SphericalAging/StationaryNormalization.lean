module

public import SphericalAging.CriticalEndpoint
public import SphericalAging.SpectralLaplace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Map

public section

/-!
# Normalizing the stationary scalar equation

This file proves the change of time and profile in Lemma 16.3 of the manuscript.
The hypotheses below are the actual stationary-profile facts used in that lemma:
continuous differentiability, `c' = -r`, `c(0)=1`, the scalar memory equation,
and the plateau identity. They are not assertions that the normalized equation
already holds. Derivatives at zero are derivatives within the nonnegative ray.
-/

open MeasureTheory Set
open scoped Topology

namespace SphericalAging.StationaryNormalization

noncomputable section

/-- Profile after the change to normalized time. -/
@[expose] def normalizedProfile (q : ℝ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  (c ((1 - q) * z) - q) / (1 - q)

/-- Positive normalized response, the negative derivative of the profile. -/
@[expose] def normalizedResponse (q : ℝ) (r : ℝ → ℝ) (z : ℝ) : ℝ := r ((1 - q) * z)

/-- Memory after subtraction of its plateau value. -/
@[expose] def normalizedMemory (q : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 - q) * (φ (q + (1 - q) * y) - φ q)

/-- Causal convolution on the nonnegative time ray. -/
@[expose] def causalConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in 0..t, f (t - s) * g s

theorem normalizedProfile_reconstruct (q : ℝ) (hq : q < 1) (c : ℝ → ℝ) (z : ℝ) :
    q + (1 - q) * normalizedProfile q c z = c ((1 - q) * z) := by
  unfold normalizedProfile
  have hd : 1 - q ≠ 0 := by linarith
  field_simp
  ring

theorem normalizedProfile_zero (q : ℝ) (hq : q < 1) (c : ℝ → ℝ) (hc0 : c 0 = 1) :
    normalizedProfile q c 0 = 1 := by
  unfold normalizedProfile
  have hd : 1 - q ≠ 0 := by linarith
  simp [hc0, hd]

theorem scale_maps_nonnegative (q : ℝ) (hq : q < 1) :
    MapsTo (fun z : ℝ => (1 - q) * z) (Ici 0) (Ici 0) := by
  intro z hz
  exact mul_nonneg (le_of_lt (sub_pos.mpr hq)) hz

theorem normalizedProfile_continuousOn (q : ℝ) (hq : q < 1) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0)) : ContinuousOn (normalizedProfile q c) (Ici 0) := by
  unfold normalizedProfile
  exact ((hc.comp (continuous_const.mul continuous_id).continuousOn
    (scale_maps_nonnegative q hq)).sub continuousOn_const).div_const _

theorem normalizedResponse_continuousOn (q : ℝ) (hq : q < 1) (r : ℝ → ℝ)
    (hr : ContinuousOn r (Ici 0)) : ContinuousOn (normalizedResponse q r) (Ici 0) := by
  exact hr.comp (continuous_const.mul continuous_id).continuousOn (scale_maps_nonnegative q hq)

theorem normalizedProfile_contDiffOn (q : ℝ) (hq : q < 1) (c : ℝ → ℝ)
    (hc : ContDiffOn ℝ 1 c (Ici 0)) : ContDiffOn ℝ 1 (normalizedProfile q c) (Ici 0) := by
  unfold normalizedProfile
  exact ((hc.comp (contDiff_const.mul contDiff_id).contDiffOn
    (scale_maps_nonnegative q hq)).sub contDiffOn_const).div_const _

theorem normalizedProfile_hasDerivWithinAt (q : ℝ) (hq : q < 1) (c r : ℝ → ℝ)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (z : ℝ) (hz : 0 ≤ z) :
    HasDerivWithinAt (normalizedProfile q c) (-normalizedResponse q r z) (Ici 0) z := by
  have hd : 1 - q ≠ 0 := by linarith
  have hdpos : 0 < 1 - q := sub_pos.mpr hq
  have hcz := hderiv ((1 - q) * z) (mul_nonneg hdpos.le hz)
  have hs : HasDerivWithinAt (fun z : ℝ => (1 - q) * z) (1 - q) (Ici 0) z :=
    by simpa using ((hasDerivAt_id z).const_mul (1 - q)).hasDerivWithinAt
  have h := ((hcz.comp z hs (scale_maps_nonnegative q hq)).sub_const q).div_const (1 - q)
  convert h using 1
  · rfl
  · unfold normalizedResponse
    field_simp

theorem normalizedProfile_derivWithin (q : ℝ) (hq : q < 1) (c r : ℝ → ℝ)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (z : ℝ) (hz : 0 ≤ z) :
    derivWithin (normalizedProfile q c) (Ici 0) z = -normalizedResponse q r z := by
  exact (normalizedProfile_hasDerivWithinAt q hq c r hderiv z hz).derivWithin
    ((uniqueDiffWithinAt_Ici z).mono (Ici_subset_Ici.mpr hz))

theorem normalizedResponse_pos (q : ℝ) (hq : q < 1) (r : ℝ → ℝ)
    (hr : ∀ t : ℝ, 0 ≤ t → 0 < r t) (z : ℝ) (hz : 0 ≤ z) :
    0 < normalizedResponse q r z := by
  exact hr _ (mul_nonneg (le_of_lt (sub_pos.mpr hq)) hz)

theorem normalizedResponse_zero (q : ℝ) (r : ℝ → ℝ) (hr0 : r 0 = 1) :
    normalizedResponse q r 0 = 1 := by simp [normalizedResponse, hr0]

/-- A change of variables for the causal scalar memory integral. -/
theorem scalar_memory_change_of_variables (q : ℝ) (hq : q < 1) (c r φ : ℝ → ℝ) (z : ℝ) :
    (∫ s in 0..((1 - q) * z), φ (c ((1 - q) * z - s)) * r s) =
      (1 - q) * ∫ s in 0..z,
        φ (q + (1 - q) * normalizedProfile q c (z - s)) * normalizedResponse q r s := by
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (fun s : ℝ => φ (c ((1 - q) * z - s)) * r s) (a := 0) (b := z) (1 - q)
  simp only [smul_eq_mul, mul_zero] at hscale
  rw [← hscale]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [normalizedProfile_reconstruct q hq]
  unfold normalizedResponse
  rw [show (1 - q) * z - (1 - q) * s = (1 - q) * (z - s) by ring]

/-- The plateau relation removes the constant memory coefficient. -/
theorem normalizedMemory_plateau (q : ℝ) (φ : ℝ → ℝ)
    (hplateau : φ q * (1 - q) = 1) (y : ℝ) :
    (1 - q) * φ (q + (1 - q) * y) = 1 + normalizedMemory q φ y := by
  unfold normalizedMemory
  nlinarith

/-- Fundamental theorem of calculus after the rescaling. -/
theorem normalizedResponse_integral (q : ℝ) (hq : q < 1) (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0))
    (hc0 : c 0 = 1)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (z : ℝ) (hz : 0 ≤ z) :
    (∫ s in 0..z, normalizedResponse q r s) = 1 - normalizedProfile q c z := by
  have hu := normalizedProfile_continuousOn q hq c hc
  have hv := normalizedResponse_continuousOn q hq r hr
  have hint : IntervalIntegrable (fun s => -normalizedResponse q r s) volume 0 z :=
    (hv.neg.mono (by rw [uIcc_of_le hz]; exact Icc_subset_Ici_self)).intervalIntegrable
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz
    (hu.mono Icc_subset_Ici_self)
    (fun s hs => (normalizedProfile_hasDerivWithinAt q hq c r hderiv s hs.1.le).hasDerivAt
      (Ici_mem_nhds hs.1)) hint
  rw [intervalIntegral.integral_neg, normalizedProfile_zero q hq c hc0] at heq
  linarith

/-- The complete rescaled Volterra equation from the unscaled scalar equation.
No normalized equation is included among the hypotheses. -/
theorem normalized_equation (q : ℝ) (hq : q < 1) (c r φ : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0)) (hφ : Continuous φ)
    (hc0 : c 0 = 1)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hplateau : φ q * (1 - q) = 1)
    (hmemory : ∀ t : ℝ, 0 ≤ t → -r t =
      -1 + ∫ s in 0..t, φ (c (t - s)) * r s)
    (z : ℝ) (hz : 0 ≤ z) :
    derivWithin (normalizedProfile q c) (Ici 0) z + normalizedProfile q c z +
      causalConvolution (fun t => normalizedMemory q φ (normalizedProfile q c t))
        (fun t => derivWithin (normalizedProfile q c) (Ici 0) t) z = 0 := by
  have hdpos : 0 < 1 - q := sub_pos.mpr hq
  have hu := normalizedProfile_continuousOn q hq c hc
  have hv := normalizedResponse_continuousOn q hq r hr
  have hvint : IntervalIntegrable (normalizedResponse q r) volume 0 z :=
    (hv.mono (by rw [uIcc_of_le hz]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hM : Continuous (normalizedMemory q φ) := by
    unfold normalizedMemory
    fun_prop
  have hMu : ContinuousOn (fun s : ℝ => normalizedMemory q φ (normalizedProfile q c (z - s)))
      (Icc 0 z) := by
    apply hM.continuousOn.comp
    · exact hu.comp (continuous_const.sub continuous_id).continuousOn
        (fun s hs => sub_nonneg.mpr hs.2)
    · exact mapsTo_univ _ _
  have hMint : IntervalIntegrable (fun s : ℝ =>
      normalizedMemory q φ (normalizedProfile q c (z - s)) * normalizedResponse q r s)
      volume 0 z := by
    exact ((hMu.mul (hv.mono Icc_subset_Ici_self)).mono (by simp [uIcc_of_le hz])).intervalIntegrable
  have hm := hmemory ((1 - q) * z) (mul_nonneg hdpos.le hz)
  rw [scalar_memory_change_of_variables q hq] at hm
  have hscaled : (1 - q) * (∫ s in 0..z,
      φ (q + (1 - q) * normalizedProfile q c (z - s)) * normalizedResponse q r s) =
      (∫ s in 0..z, normalizedResponse q r s) +
      causalConvolution (fun t => normalizedMemory q φ (normalizedProfile q c t))
        (normalizedResponse q r) z := by
    rw [← intervalIntegral.integral_const_mul]
    unfold causalConvolution
    rw [← intervalIntegral.integral_add hvint hMint]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [← mul_assoc, normalizedMemory_plateau q φ hplateau]
    ring
  rw [hscaled] at hm
  change -normalizedResponse q r z = _ at hm
  rw [normalizedResponse_integral q hq c r hc hr hc0 hderiv z hz] at hm
  rw [normalizedProfile_derivWithin q hq c r hderiv z hz]
  have hconv : causalConvolution (fun t => normalizedMemory q φ (normalizedProfile q c t))
      (fun t => derivWithin (normalizedProfile q c) (Ici 0) t) z =
      -causalConvolution (fun t => normalizedMemory q φ (normalizedProfile q c t))
        (normalizedResponse q r) z := by
    unfold causalConvolution
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [normalizedProfile_derivWithin q hq c r hderiv s
      (show 0 ≤ s from (mem_uIcc.mp hs).elim (fun h => h.1) (fun h => by linarith))]
    ring
  rw [hconv]
  linarith

/-- The pure-model memory function before normalization. -/
@[expose] def purePhi (p : ℕ) (b γ y : ℝ) : ℝ := γ + b * (p : ℝ) * y ^ (p - 1)

/-- Coefficients obtained directly from the binomial expansion. -/
@[expose] def rawMemoryCoefficient (p : ℕ) (b q : ℝ) (j : ℕ) : ℝ :=
  b * (p : ℝ) * ((p - 1).choose j : ℝ) * q ^ (p - 1 - j) * (1 - q) ^ (j + 1)

/-- Coefficients after imposing marginality; this is equation (16.8). -/
@[expose] def memoryCoefficient (p : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (1 / ((p : ℝ) - 1)) * ((p - 1).choose j : ℝ) * ((1 - q) / q) ^ (j - 1)

theorem normalizedMemory_pure (p : ℕ) (b γ q y : ℝ) :
    normalizedMemory q (purePhi p b γ) y =
      (1 - q) * b * (p : ℝ) * ((q + (1 - q) * y) ^ (p - 1) - q ^ (p - 1)) := by
  unfold normalizedMemory purePhi
  ring

/-- The complete binomial expansion of the normalized memory. -/
theorem normalizedMemory_binomial (p : ℕ) (b γ q y : ℝ) :
    normalizedMemory q (purePhi p b γ) y =
      ∑ j ∈ Finset.range (p - 1), rawMemoryCoefficient p b q (j + 1) * y ^ (j + 1) := by
  rw [normalizedMemory_pure]
  have hbin := add_pow ((1 - q) * y) q (p - 1)
  rw [Finset.sum_range_succ'] at hbin
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at hbin
  rw [add_comm q, hbin]
  rw [add_sub_cancel_right]
  rw [Finset.mul_sum, Finset.sum_congr rfl]
  intro j hj
  unfold rawMemoryCoefficient
  rw [mul_pow, pow_succ (1 - q) (j + 1)]
  ring

/-- The raw coefficient times its common denominator is exactly the
marginality expression times the remaining binomial factor. -/
theorem rawMemoryCoefficient_normalization (p : ℕ) (hp : 3 ≤ p) (b q : ℝ)
    (hm : CriticalEndpoint.marginality p b q = 1) (j : ℕ)
    (hj0 : 1 ≤ j) (hjp : j ≤ p - 1) :
    rawMemoryCoefficient p b q j * (((p : ℝ) - 1) * q ^ (j - 1)) =
      ((p - 1).choose j : ℝ) * (1 - q) ^ (j - 1) := by
  have hexp : (p - 1 - j) + (j - 1) = p - 2 := by omega
  have hdexp : j + 1 = (j - 1) + 2 := by omega
  have hpow : q ^ (p - 1 - j) * q ^ (j - 1) = q ^ (p - 2) := by rw [← pow_add, hexp]
  calc
    rawMemoryCoefficient p b q j * (((p : ℝ) - 1) * q ^ (j - 1)) =
      ((p - 1).choose j : ℝ) * (1 - q) ^ (j - 1) *
        CriticalEndpoint.marginality p b q := by
      unfold rawMemoryCoefficient CriticalEndpoint.marginality
      rw [hdexp, pow_add]
      calc
        b * (p : ℝ) * ((p - 1).choose j : ℝ) * q ^ (p - 1 - j) *
            ((1 - q) ^ (j - 1) * (1 - q) ^ 2) * (((p : ℝ) - 1) * q ^ (j - 1)) =
          b * (p : ℝ) * ((p - 1).choose j : ℝ) *
            (q ^ (p - 1 - j) * q ^ (j - 1)) *
            ((1 - q) ^ (j - 1) * (1 - q) ^ 2) * ((p : ℝ) - 1) := by ring
        _ = _ := by rw [hpow]; ring
    _ = _ := by rw [hm]; ring

theorem rawMemoryCoefficient_eq (p : ℕ) (hp : 3 ≤ p) (b q : ℝ)
    (hq : 0 < q) (hm : CriticalEndpoint.marginality p b q = 1) (j : ℕ)
    (hj0 : 1 ≤ j) (hjp : j ≤ p - 1) :
    rawMemoryCoefficient p b q j = memoryCoefficient p q j := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn : (p : ℝ) - 1 ≠ 0 := by linarith
  have hqn : q ≠ 0 := hq.ne'
  have hden : ((p : ℝ) - 1) * q ^ (j - 1) ≠ 0 := by positivity
  apply mul_right_cancel₀ hden
  rw [rawMemoryCoefficient_normalization p hp b q hm j hj0 hjp]
  unfold memoryCoefficient
  rw [div_pow]
  field_simp

/-- Marginality fixes the linear memory coefficient to one. -/
theorem memoryCoefficient_one (p : ℕ) (hp : 3 ≤ p) (q : ℝ) :
    memoryCoefficient p q 1 = 1 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp1 : 1 ≤ p := by omega
  simp only [memoryCoefficient, Nat.choose_one_right, Nat.cast_sub hp1, Nat.cast_one,
    Nat.sub_self, pow_zero, mul_one]
  field_simp

/-- The normalized pure-model memory has exactly the coefficients in the
manuscript, for all integer `p ≥ 3`. -/
theorem normalizedMemory_coefficients (p : ℕ) (hp : 3 ≤ p) (b γ q y : ℝ)
    (hq : 0 < q) (hm : CriticalEndpoint.marginality p b q = 1) :
    normalizedMemory q (purePhi p b γ) y =
      y + ∑ j ∈ Finset.range (p - 2), memoryCoefficient p q (j + 2) * y ^ (j + 2) := by
  rw [normalizedMemory_binomial]
  have hsum : (∑ j ∈ Finset.range (p - 1), rawMemoryCoefficient p b q (j + 1) * y ^ (j + 1)) =
      ∑ j ∈ Finset.range (p - 1), memoryCoefficient p q (j + 1) * y ^ (j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [rawMemoryCoefficient_eq p hp b q hq hm (j + 1) (by omega)
      (by have := Finset.mem_range.mp hj; omega)]
  rw [hsum]
  have hcount : p - 1 = (p - 2) + 1 := by omega
  rw [hcount, Finset.sum_range_succ']
  simp only [Nat.zero_add, pow_one, memoryCoefficient_one p hp, one_mul]
  rw [add_comm]

/-- Every higher memory coefficient is nonnegative on physical plateaux. -/
theorem memoryCoefficient_nonnegative (p : ℕ) (hp : 3 ≤ p) (q : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (j : ℕ) : 0 ≤ memoryCoefficient p q j := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn : 0 < (p : ℝ) - 1 := by linarith
  have hqn : 0 < 1 - q := sub_pos.mpr hq1
  unfold memoryCoefficient
  positivity

/-- The quadratic coefficient is exactly the critical exponent parameter. -/
theorem memoryCoefficient_two (p : ℕ) (hp : 3 ≤ p) (q : ℝ) (hq : 0 < q) :
    memoryCoefficient p q 2 = CriticalEndpoint.relaxationParameter p q := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : 1 ≤ p := by omega
  have hpn : (p : ℝ) - 1 ≠ 0 := by linarith
  have hqn : q ≠ 0 := hq.ne'
  unfold memoryCoefficient CriticalEndpoint.relaxationParameter
  rw [Nat.cast_choose_two]
  simp only [Nat.cast_sub hp1, Nat.cast_one]
  norm_num
  field_simp
  ring

/-- The normalized profile tends to zero, by rescaling the stationary limit. -/
theorem normalizedProfile_tendsto_zero (q : ℝ) (hq : q < 1) (c : ℝ → ℝ)
    (hlim : Filter.Tendsto c Filter.atTop (𝓝 q)) :
    Filter.Tendsto (normalizedProfile q c) Filter.atTop (𝓝 0) := by
  have hscale : Filter.Tendsto (fun z : ℝ => (1 - q) * z) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos (sub_pos.mpr hq)).mpr Filter.tendsto_id
  change Filter.Tendsto (fun z => (c ((1 - q) * z) - q) / (1 - q)) Filter.atTop (𝓝 0)
  simpa only [Function.comp_apply, sub_self, zero_div] using ((hlim.comp hscale).sub_const q).div_const (1 - q)

/-- The response is integrable on the whole normalized time ray. -/
theorem normalizedResponse_integrableOn (q : ℝ) (hq : q < 1) (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0))
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀ t : ℝ, 0 ≤ t → 0 < r t)
    (hlim : Filter.Tendsto c Filter.atTop (𝓝 q)) :
    IntegrableOn (normalizedResponse q r) (Ioi 0) := by
  have hu := normalizedProfile_continuousOn q hq c hc
  have hu0 := normalizedProfile_tendsto_zero q hq c hlim
  apply integrableOn_Ioi_deriv_of_nonneg
    (g := fun z => -normalizedProfile q c z) (l := 0)
    (hu.neg 0 (mem_Ici.mpr le_rfl))
  · intro z hz
    convert ((normalizedProfile_hasDerivWithinAt q hq c r hderiv z hz.le).hasDerivAt
        (Ici_mem_nhds hz)).neg using 1; simp only [neg_neg]
  · intro z hz
    exact (normalizedResponse_pos q hq r hrpos z hz.le).le
  · simpa only [neg_zero] using hu0.neg

/-- The normalized response has total integral one. -/
theorem normalizedResponse_total_integral (q : ℝ) (hq : q < 1) (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0)) (hc0 : c 0 = 1)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀ t : ℝ, 0 ≤ t → 0 < r t)
    (hlim : Filter.Tendsto c Filter.atTop (𝓝 q)) :
    (∫ z in Ioi 0, normalizedResponse q r z) = 1 := by
  have hu := normalizedProfile_continuousOn q hq c hc
  have hu0 := normalizedProfile_tendsto_zero q hq c hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun z => -normalizedProfile q c z) (g' := normalizedResponse q r) (l := 0)
    (hu.neg 0 (mem_Ici.mpr le_rfl))
    (fun z hz => by
      convert ((normalizedProfile_hasDerivWithinAt q hq c r hderiv z hz.le).hasDerivAt
        (Ici_mem_nhds hz)).neg using 1; simp only [neg_neg])
    (fun z hz => (normalizedResponse_pos q hq r hrpos z hz.le).le)
    (by simpa only [neg_zero] using hu0.neg)
  simpa [normalizedProfile_zero q hq c hc0] using heq

/-- Strict positivity of the response forces the stationary correlation to
decrease strictly on the nonnegative ray. -/
theorem stationaryProfile_strictAntiOn (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0))
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀ t : ℝ, 0 ≤ t → 0 < r t) : StrictAntiOn c (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) hc
  intro t ht
  have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
  rw [((hderiv t ht0.le).hasDerivAt (Ici_mem_nhds ht0)).deriv]
  exact neg_neg_of_pos (hrpos t ht0.le)

/-- Every finite-time correlation is strictly above its plateau. -/
theorem stationaryProfile_above_plateau (q : ℝ) (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0))
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀ t : ℝ, 0 ≤ t → 0 < r t)
    (hlim : Filter.Tendsto c Filter.atTop (𝓝 q)) (t : ℝ) (ht : 0 ≤ t) : q < c t := by
  have hanti := stationaryProfile_strictAntiOn c r hc hderiv hrpos
  have ht1 : 0 ≤ t + 1 := by linarith
  have hstrict : c (t + 1) < c t := hanti ht ht1 (by linarith)
  have hbound : q ≤ c (t + 1) := by
    apply le_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop (t + 1)] with s hs
    exact hanti.antitoneOn ht1 (show 0 ≤ s by linarith) hs
  exact lt_of_le_of_lt hbound hstrict

/-- The normalized profile is strictly positive at every finite time. -/
theorem normalizedProfile_pos (q : ℝ) (hq : q < 1) (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0))
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀ t : ℝ, 0 ≤ t → 0 < r t)
    (hlim : Filter.Tendsto c Filter.atTop (𝓝 q)) (z : ℝ) (hz : 0 ≤ z) :
    0 < normalizedProfile q c z := by
  have hcz := stationaryProfile_above_plateau q c r hc hderiv hrpos hlim
    ((1 - q) * z) (mul_nonneg (sub_pos.mpr hq).le hz)
  unfold normalizedProfile
  exact div_pos (sub_pos.mpr hcz) (sub_pos.mpr hq)

/-- Remove the zero spectral atom and normalize its remaining mass. -/
@[expose] def positiveSpectralMeasure (q : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (1 - q)) • ν.restrict (Ioi 0)

/-- Push the positive spectrum forward by the normalized time scale. -/
@[expose] def normalizedSpectralMeasure (q : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ => (1 - q) * x) (positiveSpectralMeasure q ν)

/-- Removing the atom at zero leaves mass `1-q`. -/
theorem positive_spectral_mass (q : ℝ) (hq0 : 0 ≤ q) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q) :
    ν (Ioi 0) = ENNReal.ofReal (1 - q) := by
  have hzero : ν (Iic 0) = ENNReal.ofReal q := by
    rw [← Iio_union_right, measure_union (by simp) (measurableSet_singleton 0), hneg, hatom]
    simp
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top ν (Iic 0)), hzero]
  simpa only [measure_univ, ← ENNReal.ofReal_one] using (ENNReal.ofReal_sub 1 hq0).symm

/-- The constructed positive spectral measure is a probability measure. -/
theorem positiveSpectralMeasure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q) :
    IsProbabilityMeasure (positiveSpectralMeasure q ν) := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  constructor
  unfold positiveSpectralMeasure
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter, smul_eq_mul]
  rw [positive_spectral_mass q hq0 ν hneg hatom]
  rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hd.le)]
  simp [hd.ne']

/-- The normalized spectral law is a probability law supported in `(0,∞)`. -/
theorem normalizedSpectralMeasure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q) :
    IsProbabilityMeasure (normalizedSpectralMeasure q ν) := by
  have := positiveSpectralMeasure_probability q hq0 hq1 ν hneg hatom
  unfold normalizedSpectralMeasure
  infer_instance

theorem normalizedSpectralMeasure_positive_support (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q) :
    normalizedSpectralMeasure q ν (Ioi 0) = 1 := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  have := positiveSpectralMeasure_probability q hq0 hq1 ν hneg hatom
  unfold normalizedSpectralMeasure
  have hmap : Measurable (fun x : ℝ => (1 - q) * x) := by fun_prop
  rw [Measure.map_apply hmap measurableSet_Ioi]
  have hpre : (fun x : ℝ => (1 - q) * x) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left hd]
  rw [hpre]
  unfold positiveSpectralMeasure
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi]
  simp only [inter_self, smul_eq_mul]
  rw [positive_spectral_mass q hq0 ν hneg hatom, ← ENNReal.ofReal_mul (one_div_nonneg.mpr hd.le)]
  simp [hd.ne']

/-- Spectral support gives integrability of the Laplace kernel for every
nonnegative time, despite possible unbounded behavior on negative frequencies. -/
theorem spectralKernel_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x : ℝ => Real.exp (-x * t)) ν := by
  have hae : ∀ᵐ x : ℝ ∂ν, 0 ≤ x := by
    rw [ae_iff]
    simpa only [not_le, Iio] using hneg
  apply (integrable_const (1 : ℝ)).mono'
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x * t))).aestronglyMeasurable
  · filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)

/-- The correlation is the zero atom plus the Laplace transform of its
positive spectrum. -/
theorem spectral_atom_decomposition (q : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q) (hq0 : 0 ≤ q)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : ℝ, Real.exp (-x * t) ∂ν) = q + ∫ x in Ioi 0, Real.exp (-x * t) ∂ν := by
  have hrestr : ν.restrict (Iic 0) = ν.restrict {0} := by
    rw [← Iio_union_right, Measure.restrict_union (by simp) (measurableSet_singleton 0),
      Measure.restrict_eq_zero.mpr hneg, zero_add]
  have heq := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic (spectralKernel_integrable ν hneg t ht)
  rw [compl_Iic] at heq
  rw [hrestr, integral_singleton] at heq
  simp only [neg_zero, zero_mul, Real.exp_zero, smul_eq_mul, mul_one, measureReal_def,
    hatom, ENNReal.toReal_ofReal hq0] at heq
  exact heq.symm

/-- Exact pushforward identity for the Laplace transform of the normalized law. -/
theorem normalizedSpectralMeasure_laplace (q : ℝ) (hq1 : q < 1) (ν : Measure ℝ) (z : ℝ) :
    (∫ η : ℝ, Real.exp (-η * z) ∂normalizedSpectralMeasure q ν) =
      (1 / (1 - q)) * ∫ x in Ioi 0, Real.exp (-x * ((1 - q) * z)) ∂ν := by
  unfold normalizedSpectralMeasure
  have hmap : Measurable (fun x : ℝ => (1 - q) * x) := by fun_prop
  rw [integral_map_of_stronglyMeasurable hmap
    (by fun_prop : Continuous (fun η : ℝ => Real.exp (-η * z))).stronglyMeasurable]
  unfold positiveSpectralMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal (one_div_nonneg.mpr (sub_pos.mpr hq1).le)]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [show -((1 - q) * x) * z = -x * ((1 - q) * z) by ring]

/-- The explicit normalized law represents the actual normalized profile.
This is the spectral probability representation in Lemma 16.3. -/
theorem normalizedProfile_spectral_representation (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c : ℝ → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q)
    (hrep : ∀ t : ℝ, 0 ≤ t → c t = ∫ x : ℝ, Real.exp (-x * t) ∂ν)
    (z : ℝ) (hz : 0 ≤ z) :
    normalizedProfile q c z = ∫ η : ℝ, Real.exp (-η * z) ∂normalizedSpectralMeasure q ν := by
  rw [normalizedSpectralMeasure_laplace q hq1]
  unfold normalizedProfile
  rw [hrep ((1 - q) * z) (mul_nonneg (sub_pos.mpr hq1).le hz),
    spectral_atom_decomposition q ν hneg hatom hq0 _ (mul_nonneg (sub_pos.mpr hq1).le hz)]
  ring

/-- The constructed spectrum has positive frequencies almost everywhere. -/
theorem normalizedSpectralMeasure_ae_positive (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q) :
    ∀ᵐ η : ℝ ∂normalizedSpectralMeasure q ν, 0 < η := by
  have := normalizedSpectralMeasure_probability q hq0 hq1 ν hneg hatom
  have hsupport := normalizedSpectralMeasure_positive_support q hq0 hq1 ν hneg hatom
  rw [ae_iff]
  change normalizedSpectralMeasure q ν (Ioi 0)ᶜ = 0
  rw [measure_compl measurableSet_Ioi (measure_ne_top _ _), hsupport, measure_univ]
  simp

/-- All fixed derivatives of the normalized profile have strictly alternating
signs. This supplies the complete monotonicity clause of Lemma 16.3. -/
theorem normalizedProfile_completeMonotonicity (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c : ℝ → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q)
    (hrep : ∀ t : ℝ, 0 ≤ t → c t = ∫ x : ℝ, Real.exp (-x * t) ∂ν)
    (n : ℕ) (z : ℝ) (hz : 0 < z) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n (normalizedProfile q c) z := by
  have := normalizedSpectralMeasure_probability q hq0 hq1 ν hneg hatom
  exact SpectralLaplace.spectralProfile_completeMonotonicity
    (normalizedSpectralMeasure q ν)
    (normalizedSpectralMeasure_ae_positive q hq0 hq1 ν hneg hatom)
    (normalizedProfile q c)
    (fun t ht => normalizedProfile_spectral_representation q hq0 hq1 c ν hneg hatom hrep t ht.le)
    n z hz

/-- The positive-time normalized response is the first damped spectral moment. -/
theorem normalizedResponse_spectralMoment (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c r : ℝ → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q)
    (hrep : ∀ t : ℝ, 0 ≤ t → c t = ∫ x : ℝ, Real.exp (-x * t) ∂ν)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (z : ℝ) (hz : 0 < z) :
    normalizedResponse q r z = SpectralLaplace.laplaceMoment (normalizedSpectralMeasure q ν) 1 z := by
  have := normalizedSpectralMeasure_probability q hq0 hq1 ν hneg hatom
  have hu := (normalizedProfile_hasDerivWithinAt q hq1 c r hderiv z hz.le).hasDerivAt (Ici_mem_nhds hz)
  have hs := SpectralLaplace.spectralProfile_hasDerivAt
    (normalizedSpectralMeasure q ν)
    (normalizedSpectralMeasure_ae_positive q hq0 hq1 ν hneg hatom)
    (normalizedProfile q c)
    (fun t ht => normalizedProfile_spectral_representation q hq0 hq1 c ν hneg hatom hrep t ht.le)
    z hz
  have heq := hu.unique hs
  linarith

/-- The normalized response decreases strictly, including its continuous
extension at zero; the manuscript requires only that it be nonincreasing. -/
theorem normalizedResponse_strictAntiOn (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c r : ℝ → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hr : ContinuousOn r (Ici 0))
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q)
    (hrep : ∀ t : ℝ, 0 ≤ t → c t = ∫ x : ℝ, Real.exp (-x * t) ∂ν)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t) :
    StrictAntiOn (normalizedResponse q r) (Ici 0) := by
  have := normalizedSpectralMeasure_probability q hq0 hq1 ν hneg hatom
  have hpositive := normalizedSpectralMeasure_ae_positive q hq0 hq1 ν hneg hatom
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) (normalizedResponse_continuousOn q hq1 r hr)
  intro z hz
  have hz0 : 0 < z := by simpa only [interior_Ici, mem_Ioi] using hz
  have hlocal : normalizedResponse q r =ᶠ[𝓝 z]
      SpectralLaplace.laplaceMoment (normalizedSpectralMeasure q ν) 1 := by
    filter_upwards [Ioi_mem_nhds hz0] with t ht
    exact normalizedResponse_spectralMoment q hq0 hq1 c r ν hneg hatom hrep hderiv t ht
  have hd := (SpectralLaplace.laplaceMoment_hasDerivAt
    (normalizedSpectralMeasure q ν) hpositive 1 z hz0).congr_of_eventuallyEq hlocal
  rw [hd.deriv]
  exact neg_neg_of_pos (SpectralLaplace.laplaceMoment_pos
    (normalizedSpectralMeasure q ν) hpositive 2 z hz0)

/-- All conclusions of the manuscript's normalized-equation lemma, with
smoothness on the positive ray stated separately from C1 at its endpoint. -/
structure NormalizedStationaryConclusions (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ) : Prop where
  profile_C1 : ContDiffOn ℝ 1 (normalizedProfile q c) (Ici 0)
  derivative : ∀ z : ℝ, 0 ≤ z →
    derivWithin (normalizedProfile q c) (Ici 0) z = -normalizedResponse q r z
  equation : ∀ z : ℝ, 0 ≤ z →
    derivWithin (normalizedProfile q c) (Ici 0) z + normalizedProfile q c z +
      causalConvolution (fun t => normalizedMemory q (purePhi p (β ^ 2) γ) (normalizedProfile q c t))
        (fun t => derivWithin (normalizedProfile q c) (Ici 0) t) z = 0
  initial_profile : normalizedProfile q c 0 = 1
  memory_expansion : ∀ y : ℝ, normalizedMemory q (purePhi p (β ^ 2) γ) y =
    y + ∑ j ∈ Finset.range (p - 2), memoryCoefficient p q (j + 2) * y ^ (j + 2)
  quadratic_coefficient : memoryCoefficient p q 2 = CriticalEndpoint.relaxationParameter p q
  coefficients_nonnegative : ∀ j : ℕ, 0 ≤ memoryCoefficient p q j
  spectral_probability : ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Ioi 0) = 1 ∧
    ∀ z : ℝ, 0 ≤ z → normalizedProfile q c z = ∫ η : ℝ, Real.exp (-η * z) ∂μ
  profile_positive : ∀ z : ℝ, 0 ≤ z → 0 < normalizedProfile q c z
  profile_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (normalizedProfile q c) (Ioi 0)
  complete_monotonicity : ∀ n : ℕ, ∀ z : ℝ, 0 < z →
    0 < (-1 : ℝ) ^ n * iteratedDeriv n (normalizedProfile q c) z
  profile_limit : Filter.Tendsto (normalizedProfile q c) Filter.atTop (𝓝 0)
  response_continuous : ContinuousOn (normalizedResponse q r) (Ici 0)
  response_positive : ∀ z : ℝ, 0 ≤ z → 0 < normalizedResponse q r z
  response_nonincreasing : AntitoneOn (normalizedResponse q r) (Ici 0)
  initial_response : normalizedResponse q r 0 = 1
  response_integrable : IntegrableOn (normalizedResponse q r) (Ioi 0)
  response_mass : (∫ z in Ioi 0, normalizedResponse q r z) = 1

/-- Lemma 16.3, including its spectral and complete-monotonicity clauses.
All assumptions are stationary-profile inputs (S1)--(S4) used in the text;
none is a normalized equation or a normalized spectral conclusion. -/
theorem normalized_stationary_profile (p : ℕ) (hp : 3 ≤ p) (β γ q : ℝ) (c r : ℝ → ℝ)
    (hc1 : ContDiffOn ℝ 1 c (Ici 0)) (hr1 : ContDiffOn ℝ 1 r (Ici 0))
    (hc0 : c 0 = 1) (hr0 : r 0 = 1)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t)
    (hrpos : ∀ t : ℝ, 0 ≤ t → 0 < r t)
    (hlim : Filter.Tendsto c Filter.atTop (𝓝 q))
    (hmemory : ∀ t : ℝ, 0 ≤ t → -r t =
      -1 + ∫ s in 0..t, purePhi p (β ^ 2) γ (c (t - s)) * r s)
    (hplateau : purePhi p (β ^ 2) γ q * (1 - q) = 1)
    (hqd : CriticalEndpoint.dynamicalPlateau p ≤ q) (hq1 : q < 1)
    (hm : CriticalEndpoint.marginality p (β ^ 2) q = 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hneg : ν (Iio 0) = 0) (hatom : ν {0} = ENNReal.ofReal q)
    (hrep : ∀ t : ℝ, 0 ≤ t → c t = ∫ x : ℝ, Real.exp (-x * t) ∂ν) :
    NormalizedStationaryConclusions p β γ q c r := by
  have hq : 0 < q := lt_of_lt_of_le (CriticalEndpoint.dynamicalPlateau_pos p hp) hqd
  have hc := hc1.continuousOn
  have hr := hr1.continuousOn
  have := normalizedSpectralMeasure_probability q hq.le hq1 ν hneg hatom
  have hpositive := normalizedSpectralMeasure_ae_positive q hq.le hq1 ν hneg hatom
  have hspectral : ∀ z : ℝ, 0 ≤ z → normalizedProfile q c z =
      ∫ η : ℝ, Real.exp (-η * z) ∂normalizedSpectralMeasure q ν :=
    normalizedProfile_spectral_representation q hq.le hq1 c ν hneg hatom hrep
  refine ⟨normalizedProfile_contDiffOn q hq1 c hc1,
    normalizedProfile_derivWithin q hq1 c r hderiv,
    normalized_equation q hq1 c r (purePhi p (β ^ 2) γ) hc hr
      (by unfold purePhi; fun_prop) hc0 hderiv hplateau hmemory,
    normalizedProfile_zero q hq1 c hc0,
    fun y => normalizedMemory_coefficients p hp (β ^ 2) γ q y hq hm,
    memoryCoefficient_two p hp q hq,
    memoryCoefficient_nonnegative p hp q hq hq1,
    ⟨normalizedSpectralMeasure q ν, inferInstance,
      normalizedSpectralMeasure_positive_support q hq.le hq1 ν hneg hatom, hspectral⟩,
    normalizedProfile_pos q hq1 c r hc hderiv hrpos hlim,
    SpectralLaplace.spectralProfile_contDiffOn (normalizedSpectralMeasure q ν) hpositive
      (normalizedProfile q c) (fun t ht => hspectral t ht.le),
    normalizedProfile_completeMonotonicity q hq.le hq1 c ν hneg hatom hrep,
    normalizedProfile_tendsto_zero q hq1 c hlim,
    normalizedResponse_continuousOn q hq1 r hr,
    normalizedResponse_pos q hq1 r hrpos,
    (normalizedResponse_strictAntiOn q hq.le hq1 c r ν hr hneg hatom hrep hderiv).antitoneOn,
    normalizedResponse_zero q r hr0,
    normalizedResponse_integrableOn q hq1 c r hc hderiv hrpos hlim,
    normalizedResponse_total_integral q hq1 c r hc hc0 hderiv hrpos hlim⟩

end
end SphericalAging.StationaryNormalization
