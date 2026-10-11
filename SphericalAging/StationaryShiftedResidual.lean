module

public import SphericalAging.StationaryBetaConvolution

public section

/-! Positivity of the actual critical shifted-power quadratic residual. -/

open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.StationaryShiftedResidual

noncomputable section

open StationaryPowerProfiles StationaryBetaConvolution StationaryNormalization

@[expose] def J (a x : ℝ) : ℝ := (1 - 2 * a) * truncatedBeta a a x + 2 * x * betaKernel a a x

@[expose] def L (a x : ℝ) : ℝ := (1 - 2 * x) * betaKernel a a x - (1 - 2 * a) * truncatedBeta a a x

@[expose] def quadraticQuotient (a x : ℝ) : ℝ := (1 - x) ^ (2 * a) * J a x

@[expose] def quadraticResidual (a t : ℝ) : ℝ :=
  deriv (causalConvolution (shiftedPower a) (shiftedPower a)) t -
    CriticalEndpoint.exponentCoefficient a * shiftedPower a t ^ 2

theorem betaKernel_pos (α ζ x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    0 < betaKernel α ζ x :=
  mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.rpow_pos_of_pos (by linarith) _)

theorem symmetric_kernel (a x : ℝ) : betaKernel a a (1 - x) = betaKernel a a x := by
  simp only [betaKernel, sub_sub_cancel]
  ring

theorem symmetric_kernel_hasDerivAt (a x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (betaKernel a a)
      (-a * (1 - 2 * x) * betaKernel a a x / (x * (1 - x))) x := by
  convert betaKernel_hasDerivAt a a x hx0 hx1 using 1
  unfold betaKernel
  rw [Real.rpow_sub_one hx0.ne', Real.rpow_sub_one (by linarith : 1 - x ≠ 0)]
  field_simp [hx0.ne', show 1 - x ≠ 0 by linarith]
  ring

theorem J_hasDerivAt (a x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (J a) (2 * a * betaKernel a a x / (1 - x)) x := by
  have hB := truncatedBeta_hasDerivAt a a x hx0 hx1
  rw [symmetric_kernel] at hB
  have hω := symmetric_kernel_hasDerivAt a x hx0 hx1
  have hlin : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1
    · rfl
    · ring
  have hd := (hB.const_mul (1 - 2 * a)).add (hlin.mul hω)
  convert hd using 1
  · rfl
  · field_simp [hx0.ne', show 1 - x ≠ 0 by linarith]
    ring

theorem L_hasDerivAt (a x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (L a) (-a * betaKernel a a x / (x * (1 - x))) x := by
  have hB := truncatedBeta_hasDerivAt a a x hx0 hx1
  rw [symmetric_kernel] at hB
  have hω := symmetric_kernel_hasDerivAt a x hx0 hx1
  have hlin : HasDerivAt (fun z : ℝ => 1 - 2 * z) (-2) x := by
    convert ((hasDerivAt_id x).const_mul 2).const_sub 1 using 1 <;> simp
  have hd := (hlin.mul hω).sub (hB.const_mul (1 - 2 * a))
  convert hd using 1
  · rfl
  · field_simp [hx0.ne', show 1 - x ≠ 0 by linarith]
    ring

theorem L_half (a : ℝ) : L a (1 / 2) = 0 := by
  norm_num [L, truncatedBeta]

theorem L_pos (a x : ℝ) (ha : 0 < a) (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    0 < L a x := by
  have hanti : StrictAntiOn (L a) (Ioc 0 (1 / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (1 / 2))
    · intro z hz
      exact (L_hasDerivAt a z hz.1 (by linarith [hz.2])).continuousAt.continuousWithinAt
    · intro z hz
      have hz' : z ∈ Ioo 0 (1 / 2) := by simpa only [interior_Ioc] using hz
      rw [(L_hasDerivAt a z hz'.1 (by linarith [hz'.2])).deriv]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) (betaKernel_pos a a z hz'.1 (by linarith [hz'.2])))
        (mul_pos hz'.1 (by linarith [hz'.2]))
  have hlt := hanti (show x ∈ Ioc 0 (1 / 2) from ⟨hx0, hx1.le⟩)
    (show (1 / 2 : ℝ) ∈ Ioc 0 (1 / 2) by norm_num) hx1
  rw [L_half] at hlt
  exact hlt

theorem quadraticQuotient_hasDerivAt (a x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (quadraticQuotient a)
      (2 * a * (1 - x) ^ (2 * a - 1) * L a x) x := by
  have hpow := ((hasDerivAt_id x).const_sub 1).rpow_const (p := 2 * a)
    (Or.inl (by change 1 - x ≠ 0; linarith))
  have hd := hpow.mul (J_hasDerivAt a x hx0 hx1)
  convert hd using 1
  · rfl
  · simp only [id_eq, Real.rpow_sub_one (by linarith : 1 - x ≠ 0)]
    unfold L J
    field_simp [show 1 - x ≠ 0 by linarith]
    ring

theorem quadraticQuotient_strictMonoOn (a : ℝ) (ha : 0 < a) :
    StrictMonoOn (quadraticQuotient a) (Ioc 0 (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (1 / 2))
  · intro x hx
    exact (quadraticQuotient_hasDerivAt a x hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 (1 / 2) := by simpa only [interior_Ioc] using hx
    rw [(quadraticQuotient_hasDerivAt a x hx'.1 (by linarith [hx'.2])).deriv]
    exact mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith [hx'.2]) _))
      (L_pos a x ha hx'.1 hx'.2)

/-- The apparently singular boundary product has a genuine continuous
power representation through zero for a<1. -/
theorem boundary_kernel_power (a x : ℝ) (ha : a < 1) (hx0 : 0 ≤ x) (_hx1 : x < 1) :
    x * betaKernel a a x = x ^ (1 - a) * (1 - x) ^ (-a) := by
  rcases hx0.eq_or_lt with hx | hx
  · rw [← hx]
    simp only [zero_mul, Real.zero_rpow (show 1 - a ≠ 0 by linarith)]
  · unfold betaKernel
    rw [show 1 - a = 1 + (-a) by ring, Real.rpow_add hx, Real.rpow_one]
    ring

theorem quadraticQuotient_continuousOn_closed (a : ℝ) (ha : a < 1) :
    ContinuousOn (quadraticQuotient a) (Icc 0 (1 / 2)) := by
  have hB : ContinuousOn (truncatedBeta a a) (Icc 0 (1 / 2)) :=
    (truncatedBeta_continuousOn_unit a a ha ha).mono
      (Icc_subset_Icc le_rfl (by norm_num))
  have hxp : ContinuousOn (fun x : ℝ => x ^ (1 - a)) (Icc 0 (1 / 2)) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ 1 - a)).continuousOn
  have h1p (b : ℝ) : ContinuousOn (fun x : ℝ => (1 - x) ^ b) (Icc 0 (1 / 2)) :=
    (continuous_const.sub continuous_id).continuousOn.rpow_const
      (fun x hx => Or.inl (by change 1 - x ≠ 0; linarith [hx.2]))
  have hboundary : ContinuousOn (fun x => x * betaKernel a a x) (Icc 0 (1 / 2)) := by
    apply (hxp.mul (h1p (-a))).congr
    intro x hx
    change x * betaKernel a a x = x ^ (1 - a) * (1 - x) ^ (-a)
    exact boundary_kernel_power a x ha hx.1 (by linarith [hx.2])
  have hJ : ContinuousOn (J a) (Icc 0 (1 / 2)) := by
    have hc : ContinuousOn (fun x => (1 - 2 * a) * truncatedBeta a a x +
        2 * (x * betaKernel a a x)) (Icc 0 (1 / 2)) :=
      (continuousOn_const.mul hB).add (continuousOn_const.mul hboundary)
    convert hc using 1
    funext x
    unfold J
    ring
  exact (h1p (2 * a)).mul hJ

theorem quadraticQuotient_zero (a : ℝ) (ha : a < 1 / 2) :
    quadraticQuotient a 0 = CriticalEndpoint.exponentCoefficient a := by
  unfold quadraticQuotient J
  rw [truncatedBeta_zero a a (by linarith) (by linarith)]
  simp only [sub_zero, Real.one_rpow, mul_zero, zero_mul, add_zero, one_mul]
  exact CriticalEndpoint.beta_gamma_balance a ha

theorem quadraticQuotient_strictMonoOn_closed (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    StrictMonoOn (quadraticQuotient a) (Icc 0 (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2))
    (quadraticQuotient_continuousOn_closed a (by linarith))
  intro x hx
  have hx' : x ∈ Ioo 0 (1 / 2) := by simpa only [interior_Icc] using hx
  rw [(quadraticQuotient_hasDerivAt a x hx'.1 (by linarith [hx'.2])).deriv]
  exact mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith [hx'.2]) _))
    (L_pos a x ha0 hx'.1 hx'.2)

/-- The exact actual convolution-to-square quotient used for positivity. -/
theorem shifted_convolution_quotient (a t : ℝ) (ht : 0 ≤ t) :
    deriv (causalConvolution (shiftedPower a) (shiftedPower a)) t /
      shiftedPower a t ^ 2 = quadraticQuotient a (1 / (t + 2)) := by
  let T := t + 2
  let x := 1 / T
  have hT : 0 < T := by dsimp [T]; linarith
  have hx0 : 0 < x := one_div_pos.mpr hT
  have hx1 : x < 1 := by
    have hh := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
      (show 1 < T by dsimp [T]; linarith)
    simpa only [one_div_one] using hh
  have h1x : 0 < 1 - x := by linarith
  have hbase : 1 + t = T * (1 - x) := by
    dsimp only [x]
    field_simp [hT.ne']
    dsimp [T]
    ring
  have hgsq : shiftedPower a t ^ 2 = T ^ (-2 * a) * (1 - x) ^ (-2 * a) := by
    unfold shiftedPower
    rw [← Real.rpow_mul_natCast (show 0 ≤ 1 + t by linarith) (-a) 2]
    rw [show (-a) * (2 : ℕ) = -2 * a by norm_num; ring, hbase,
      Real.mul_rpow hT.le h1x.le]
  have hderiv : deriv (causalConvolution (shiftedPower a) (shiftedPower a)) t =
      T ^ (-2 * a) * J a x := by
    rw [(shifted_convolution_hasDerivAt a a t (by linarith)).deriv]
    change T ^ (-a - a) * ((1 - a - a) * truncatedBeta a a x +
      x * betaKernel a a x + x * betaKernel a a (1 - x)) = T ^ (-2 * a) * J a x
    rw [symmetric_kernel, show -a - a = -2 * a by ring]
    unfold J
    ring
  rw [hderiv, hgsq]
  rw [mul_div_mul_left (J a x) ((1 - x) ^ (-2 * a))
    (Real.rpow_pos_of_pos hT (-2 * a)).ne']
  change J a x / (1 - x) ^ (-2 * a) = quadraticQuotient a x
  unfold quadraticQuotient
  rw [show -2 * a = -(2 * a) by ring, Real.rpow_neg h1x.le, div_inv_eq_mul]
  ring

/-- The critical shifted-power quadratic residual is strictly positive
for every nonnegative time, including t=0, as in Lemma16.5. -/
theorem quadraticResidual_pos (a t : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) (ht : 0 ≤ t) :
    0 < quadraticResidual a t := by
  have hx0 : 0 < 1 / (t + 2) := one_div_pos.mpr (by linarith)
  have hxhalf : 1 / (t + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith)
  have hq := quadraticQuotient_strictMonoOn_closed a ha0 ha1
    (show (0 : ℝ) ∈ Icc 0 (1 / 2) by norm_num)
    (show 1 / (t + 2) ∈ Icc 0 (1 / 2) from ⟨hx0.le, hxhalf⟩) hx0
  rw [quadraticQuotient_zero a ha1, ← shifted_convolution_quotient a t ht] at hq
  have hg : 0 < shiftedPower a t ^ 2 := pow_pos (shiftedPower_pos a t ht) 2
  have hh := (lt_div_iff₀ hg).mp hq
  unfold quadraticResidual
  linarith

end
end SphericalAging.StationaryShiftedResidual
