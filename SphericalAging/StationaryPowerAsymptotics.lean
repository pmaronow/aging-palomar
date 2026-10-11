module

public import SphericalAging.StationaryShiftedResidual

public section

/-! Actual limits of derivatives of shifted-power convolutions. -/

open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.StationaryPowerAsymptotics

noncomputable section

open StationaryPowerProfiles StationaryBetaConvolution StationaryNormalization

@[expose] def normalizedConvolutionQuotient (α ζ x : ℝ) : ℝ :=
  (1 - x) ^ (α + ζ) * ((1 - α - ζ) * truncatedBeta α ζ x +
    x ^ (1 - α) * (1 - x) ^ (-ζ) + x ^ (1 - ζ) * (1 - x) ^ (-α))

theorem normalizedConvolutionQuotient_continuousOn (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    ContinuousOn (normalizedConvolutionQuotient α ζ) (Icc 0 (1 / 2)) := by
  have hB := (truncatedBeta_continuousOn_unit α ζ hα hζ).mono
    (Icc_subset_Icc le_rfl (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have h1p (b : ℝ) : ContinuousOn (fun x : ℝ => (1 - x) ^ b) (Icc 0 (1 / 2)) :=
    (continuous_const.sub continuous_id).continuousOn.rpow_const
      (fun x hx => Or.inl (by change 1 - x ≠ 0; linarith [hx.2]))
  have hxα : ContinuousOn (fun x : ℝ => x ^ (1 - α)) (Icc 0 (1 / 2)) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ 1 - α)).continuousOn
  have hxζ : ContinuousOn (fun x : ℝ => x ^ (1 - ζ)) (Icc 0 (1 / 2)) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ 1 - ζ)).continuousOn
  exact (h1p (α + ζ)).mul (((continuousOn_const.mul hB).add (hxα.mul (h1p (-ζ)))).add
    (hxζ.mul (h1p (-α))))

theorem normalizedConvolutionQuotient_zero (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    normalizedConvolutionQuotient α ζ 0 =
      (1 - α - ζ) * ProbabilityTheory.beta (1 - α) (1 - ζ) := by
  unfold normalizedConvolutionQuotient
  rw [truncatedBeta_zero α ζ hα hζ]
  simp only [sub_zero, Real.one_rpow, one_mul,
    Real.zero_rpow (show 1 - α ≠ 0 by linarith), Real.zero_rpow (show 1 - ζ ≠ 0 by linarith),
    zero_mul, add_zero]

theorem shifted_convolution_product_quotient (α ζ t : ℝ) (ht : 0 ≤ t) :
    deriv (causalConvolution (shiftedPower α) (shiftedPower ζ)) t /
      (shiftedPower α t * shiftedPower ζ t) =
      normalizedConvolutionQuotient α ζ (1 / (t + 2)) := by
  let T := t + 2
  let x := 1 / T
  have hT : 0 < T := by dsimp [T]; linarith
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
  have hprod : shiftedPower α t * shiftedPower ζ t =
      T ^ (-α - ζ) * (1 - x) ^ (-α - ζ) := by
    unfold shiftedPower
    rw [← Real.rpow_add (show 0 < 1 + t by linarith),
      show -α + -ζ = -α - ζ by ring, hbase, Real.mul_rpow hT.le h1x.le]
  rw [shifted_convolution_derivative α ζ t (by linarith), hprod]
  rw [mul_div_mul_left _ ((1 - x) ^ (-α - ζ))
    (Real.rpow_pos_of_pos hT (-α - ζ)).ne']
  change _ / (1 - x) ^ (-α - ζ) = normalizedConvolutionQuotient α ζ x
  rw [show -α - ζ = -(α + ζ) by ring, Real.rpow_neg h1x.le (α + ζ), div_inv_eq_mul]
  unfold normalizedConvolutionQuotient
  ring

theorem beta_coordinate_tendsto :
    Tendsto (fun t : ℝ => 1 / (t + 2)) atTop (𝓝[ Icc 0 (1 / 2)] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have ht : Tendsto (fun t : ℝ => t + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_id
    convert tendsto_inv_atTop_zero.comp ht using 1
    funext t
    simp only [Function.comp_apply, one_div]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    refine ⟨(one_div_pos.mpr (by linarith : 0 < t + 2)).le, ?_⟩
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith)

/-- The actual shifted convolution derivative has the beta balance limit,
without differentiating any asymptotic equivalence. -/
theorem shifted_convolution_product_quotient_tendsto (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    Tendsto (fun t => deriv (causalConvolution (shiftedPower α) (shiftedPower ζ)) t /
      (shiftedPower α t * shiftedPower ζ t)) atTop
      (𝓝 ((1 - α - ζ) * ProbabilityTheory.beta (1 - α) (1 - ζ))) := by
  have ht := ((normalizedConvolutionQuotient_continuousOn α ζ hα hζ)
    0 (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 2))).tendsto.comp beta_coordinate_tendsto
  rw [normalizedConvolutionQuotient_zero α ζ hα hζ] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t htime
  exact (shifted_convolution_product_quotient α ζ t htime).symm

theorem shiftedPower_nat (a t : ℝ) (n : ℕ) (ht : -1 < t) :
    shiftedPower ((n : ℝ) * a) t = shiftedPower a t ^ n := by
  unfold shiftedPower
  rw [← Real.rpow_mul_natCast (show 0 ≤ 1 + t by linarith) (-a) n]
  congr 1
  ring

/-- Natural powers in both factors are identified inside the actual causal
integral on its precise domain. -/
theorem power_convolution_eq (a t : ℝ) (n m : ℕ) (ht : -1 < t) :
    causalConvolution (fun s => shiftedPower a s ^ n) (fun s => shiftedPower a s ^ m) t =
      causalConvolution (shiftedPower ((n : ℝ) * a)) (shiftedPower ((m : ℝ) * a)) t := by
  unfold causalConvolution
  apply intervalIntegral.integral_congr
  intro s hs
  have hleft : -1 < t - s := by rcases mem_uIcc.mp hs with hs | hs <;> linarith
  have hright : -1 < s := by rcases mem_uIcc.mp hs with hs | hs <;> linarith
  change shiftedPower a (t - s) ^ n * shiftedPower a s ^ m =
    shiftedPower ((n : ℝ) * a) (t - s) * shiftedPower ((m : ℝ) * a) s
  rw [shiftedPower_nat a (t - s) n hleft, shiftedPower_nat a s m hright]

/-- The derivative identity follows from an actual equality on an open
neighborhood, and does not differentiate an asymptotic equivalence. -/
theorem power_convolution_derivative_eq (a t : ℝ) (n m : ℕ) (ht : -1 < t) :
    deriv (causalConvolution (fun s => shiftedPower a s ^ n) (fun s => shiftedPower a s ^ m)) t =
      deriv (causalConvolution (shiftedPower ((n : ℝ) * a)) (shiftedPower ((m : ℝ) * a))) t := by
  have heq : causalConvolution (fun s => shiftedPower a s ^ n) (fun s => shiftedPower a s ^ m) =ᶠ[𝓝 t]
      causalConvolution (shiftedPower ((n : ℝ) * a)) (shiftedPower ((m : ℝ) * a)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact power_convolution_eq a s n m hs
  exact heq.deriv_eq

@[expose] def crossResidual (a t : ℝ) : ℝ :=
  deriv (causalConvolution (shiftedPower a) (fun s => shiftedPower a s ^ 2)) t -
    CriticalEndpoint.exponentCoefficient a * shiftedPower a t ^ 3

@[expose] def quarticResidual (a t : ℝ) : ℝ :=
  deriv (causalConvolution (fun s => shiftedPower a s ^ 2) (fun s => shiftedPower a s ^ 2)) t -
    CriticalEndpoint.exponentCoefficient a * shiftedPower a t ^ 4

/-- The precise actual cross-residual quotient limit in Lemma16.5. Its
strict negativity is proved independently in critical_cross_limit_negative. -/
theorem crossResidual_quotient_tendsto (a : ℝ) (ha : a < 1 / 2) :
    Tendsto (fun t => crossResidual a t / shiftedPower a t ^ 3) atTop
      (𝓝 ((1 - 3 * a) * ProbabilityTheory.beta (1 - a) (1 - 2 * a) -
        CriticalEndpoint.exponentCoefficient a)) := by
  have ht := (shifted_convolution_product_quotient_tendsto a (2 * a)
    (by linarith) (by linarith)).sub
      (tendsto_const_nhds (x := CriticalEndpoint.exponentCoefficient a))
  rw [show 1 - a - 2 * a = 1 - 3 * a by ring] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t htime
  have hd := power_convolution_derivative_eq a t 1 2 (by linarith)
  simp only [pow_one, Nat.cast_one, one_mul, Nat.cast_ofNat] at hd
  have hp := shiftedPower_nat a t 2 (by linarith)
  norm_num only [Nat.cast_ofNat] at hp
  unfold crossResidual
  rw [hd, hp]
  have hn := (shiftedPower_pos a t htime).ne'
  field_simp [hn]

/-- Compactness of the actual continuous beta quotient gives a global
bound on the normalized derivative, not an assumed asymptotic bound. -/
theorem shifted_convolution_quotient_bounded (α ζ : ℝ) (hα : α < 1) (hζ : ζ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≥ 0,
      |deriv (causalConvolution (shiftedPower α) (shiftedPower ζ)) t /
        (shiftedPower α t * shiftedPower ζ t)| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (normalizedConvolutionQuotient_continuousOn α ζ hα hζ).abs
  have hC0 : 0 ≤ C := (abs_nonneg (normalizedConvolutionQuotient α ζ 0)).trans
    (hC ⟨0, by norm_num, rfl⟩)
  refine ⟨C, hC0, ?_⟩
  intro t ht
  rw [shifted_convolution_product_quotient α ζ t ht]
  apply hC
  refine ⟨1 / (t + 2), ⟨(one_div_pos.mpr (by linarith : 0 < t + 2)).le, ?_⟩, rfl⟩
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith)

/-- The global |D₂|<=K*g³ bound of Lemma16.5 for the actual convolution
of squared shifted powers. -/
theorem quarticResidual_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ≥ 0, |quarticResidual a t| ≤ K * shiftedPower a t ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := shifted_convolution_quotient_bounded (2 * a) (2 * a)
    (by linarith) (by linarith)
  let θ := CriticalEndpoint.exponentCoefficient a
  have hθ : 0 < θ := CriticalEndpoint.exponentCoefficient_pos a ha1
  refine ⟨C + |θ|, by positivity, ?_⟩
  intro t ht
  have hd := power_convolution_derivative_eq a t 2 2 (by linarith)
  norm_num only [Nat.cast_ofNat] at hd
  have hp := shiftedPower_nat a t 2 (by linarith)
  norm_num only [Nat.cast_ofNat] at hp
  have hg := shiftedPower_pos a t ht
  have hgn := shiftedPower_le_one a t ha0.le ht
  have hcov := hC t ht
  rw [hp] at hcov
  have hpow : 0 < shiftedPower a t ^ 4 := pow_pos hg 4
  have hprod : shiftedPower a t ^ 2 * shiftedPower a t ^ 2 = shiftedPower a t ^ 4 := by ring
  rw [hprod, abs_div, abs_of_pos hpow] at hcov
  have hcovb := (div_le_iff₀ hpow).mp hcov
  have hp43 : shiftedPower a t ^ 4 ≤ shiftedPower a t ^ 3 := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hg.le _) hgn
  unfold quarticResidual
  rw [hd]
  calc
    |deriv (causalConvolution (shiftedPower (2 * a)) (shiftedPower (2 * a))) t -
        CriticalEndpoint.exponentCoefficient a * shiftedPower a t ^ 4| ≤
      |deriv (causalConvolution (shiftedPower (2 * a)) (shiftedPower (2 * a))) t| +
        |θ * shiftedPower a t ^ 4| := abs_sub _ _
    _ ≤ C * shiftedPower a t ^ 4 + |θ| * shiftedPower a t ^ 4 := by
      rw [abs_mul, abs_of_pos hpow]
      exact add_le_add hcovb le_rfl
    _ = (C + |θ|) * shiftedPower a t ^ 4 := by ring
    _ ≤ (C + |θ|) * shiftedPower a t ^ 3 :=
      mul_le_mul_of_nonneg_left hp43 (by positivity)

end
end SphericalAging.StationaryPowerAsymptotics
