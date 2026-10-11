module

public import SphericalAging.StationaryPowerAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

/-! Quantitative decay of the actual positive shifted-power residual. -/

open Set MeasureTheory Filter Asymptotics
open scoped Topology

namespace SphericalAging.StationaryQuadraticDecay

noncomputable section

open StationaryPowerProfiles StationaryBetaConvolution StationaryNormalization StationaryShiftedResidual

theorem truncatedBeta_le_complete (a x : ℝ) (ha : a < 1) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    truncatedBeta a a x ≤ ProbabilityTheory.beta (1 - a) (1 - a) := by
  have hnon : 0 ≤ᵐ[volume.restrict (Ioc 0 1)] betaKernel a a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact mul_nonneg (Real.rpow_nonneg hy.1.le _) (Real.rpow_nonneg (sub_nonneg.mpr hy.2) _)
  have hb := intervalIntegral.integral_mono_interval hx0 (by linarith : x ≤ 1 - x)
    (by linarith : 1 - x ≤ 1) hnon (betaKernel_integrable_unit a a ha ha)
  rw [betaKernel_integral_unit a a ha ha] at hb
  exact hb

/-- Positivity allows dropping both negative terms in the exact quadratic
balance, giving a global quantitative estimate without a beta-tail asymptotic. -/
theorem quadraticResidual_global_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    ∀ t ≥ 0, |quadraticResidual a t| ≤
      (2 * (1 / 2 : ℝ) ^ (-a)) * (1 + t) ^ (-a - 1) := by
  intro t ht
  let T := t + 2
  let x := 1 / T
  let θ := CriticalEndpoint.exponentCoefficient a
  have hT : 0 < T := by dsimp [T]; linarith
  have hx0 : 0 < x := one_div_pos.mpr hT
  have hxhalf : x ≤ 1 / 2 := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 2) (by dsimp [T]; linarith)
  have hx1 : x < 1 := by linarith
  have hTp := Real.rpow_pos_of_pos hT (-2 * a)
  have hθ : 0 < θ := CriticalEndpoint.exponentCoefficient_pos a ha1
  have hB := truncatedBeta_le_complete a x (by linarith) hx0.le hxhalf
  have hBJ := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ 1 - 2 * a)
  rw [CriticalEndpoint.beta_gamma_balance a ha1] at hBJ
  have hJ : J a x ≤ θ + 2 * x * betaKernel a a x := by
    unfold J
    dsimp [θ]
    linarith
  have hderiv : deriv (causalConvolution (shiftedPower a) (shiftedPower a)) t =
      T ^ (-2 * a) * J a x := by
    rw [(shifted_convolution_hasDerivAt a a t (by linarith)).deriv]
    change T ^ (-a - a) * ((1 - a - a) * truncatedBeta a a x +
      x * betaKernel a a x + x * betaKernel a a (1 - x)) = T ^ (-2 * a) * J a x
    rw [symmetric_kernel, show -a - a = -2 * a by ring]
    unfold J
    ring
  have hgpow : shiftedPower a t ^ 2 = (1 + t) ^ (-2 * a) := by
    unfold shiftedPower
    rw [← Real.rpow_mul_natCast (show 0 ≤ 1 + t by linarith) (-a) 2]
    congr 1
    norm_num
    ring
  have hgsq : T ^ (-2 * a) ≤ shiftedPower a t ^ 2 := by
    rw [hgpow]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by dsimp [T]; linarith) (by linarith)
  have hDbound : quadraticResidual a t ≤ 2 * T ^ (-2 * a) * (x * betaKernel a a x) := by
    have hderivb := mul_le_mul_of_nonneg_left hJ hTp.le
    have hθb := mul_le_mul_of_nonneg_left hgsq hθ.le
    unfold quadraticResidual
    rw [hderiv]
    dsimp [θ] at hderivb hθb
    nlinarith
  have hboundary := boundary_kernel_power a x (by linarith) hx0.le hx1
  have h1power : (1 - x) ^ (-a) ≤ (1 / 2 : ℝ) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hboundaryb : x * betaKernel a a x ≤ x ^ (1 - a) * (1 / 2 : ℝ) ^ (-a) := by
    rw [hboundary]
    exact mul_le_mul_of_nonneg_left h1power (Real.rpow_pos_of_pos hx0 _).le
  have hp : T ^ (-2 * a) * x ^ (1 - a) = T ^ (-a - 1) := by
    dsimp [x]
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow T (1 - a), ← Real.rpow_add hT]
    congr 1
    ring
  have hlag : T ^ (-a - 1) ≤ (1 + t) ^ (-a - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by dsimp [T]; linarith) (by linarith)
  rw [abs_of_pos (quadraticResidual_pos a t ha0 ha1 ht)]
  calc
    quadraticResidual a t ≤ 2 * T ^ (-2 * a) * (x * betaKernel a a x) := hDbound
    _ ≤ 2 * T ^ (-2 * a) * (x ^ (1 - a) * (1 / 2 : ℝ) ^ (-a)) :=
      mul_le_mul_of_nonneg_left hboundaryb (by positivity)
    _ = (2 * (1 / 2 : ℝ) ^ (-a)) * T ^ (-a - 1) := by
      rw [← hp]
      ring
    _ ≤ (2 * (1 / 2 : ℝ) ^ (-a)) * (1 + t) ^ (-a - 1) :=
      mul_le_mul_of_nonneg_left hlag (by positivity)

/-- The exact big-O assertion of Lemma16.5. -/
theorem quadraticResidual_isBigO (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    (quadraticResidual a) =O[atTop] (fun t : ℝ => (1 + t) ^ (-a - 1)) := by
  apply IsBigO.of_bound (2 * (1 / 2 : ℝ) ^ (-a))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith : 0 < 1 + t) _)]
    using quadraticResidual_global_bound a ha0 ha1 t ht

/-- The exact o(g³) assertion follows from the positive exponent 1-2a. -/
theorem quadraticResidual_isLittleO_cube (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    (quadraticResidual a) =o[atTop] (fun t => shiftedPower a t ^ 3) := by
  let C := 2 * (1 / 2 : ℝ) ^ (-a)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlag : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  have hlim : Tendsto (fun t : ℝ => C * (1 + t) ^ (-(1 - 2 * a))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := C)).mul ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - 2 * a)).comp hlag)
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop (0 : ℝ), hlim.eventually (Iio_mem_nhds hε)] with t ht hεt
  have hp : (1 + t) ^ (-a - 1) = (1 + t) ^ (-(1 - 2 * a)) * shiftedPower a t ^ 3 := by
    rw [← StationaryPowerAsymptotics.shiftedPower_nat a t 3 (by linarith)]
    unfold shiftedPower
    rw [← Real.rpow_add (show 0 < 1 + t by linarith)]
    congr 1
    norm_num
    ring
  have hg := pow_pos (shiftedPower_pos a t ht) 3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hg]
  calc
    |quadraticResidual a t| ≤ C * (1 + t) ^ (-a - 1) := quadraticResidual_global_bound a ha0 ha1 t ht
    _ = (C * (1 + t) ^ (-(1 - 2 * a))) * shiftedPower a t ^ 3 := by rw [hp]; ring
    _ ≤ ε * shiftedPower a t ^ 3 := mul_le_mul_of_nonneg_right hεt.le hg.le

end
end SphericalAging.StationaryQuadraticDecay
