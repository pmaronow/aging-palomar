module

public import SphericalAging.StationaryQuadraticDecay
public import Mathlib.Data.Nat.Choose.Sum

public section

/-! Uniform derivative bounds for every higher corrected-power convolution. -/

open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.StationaryHigherPowerBound
noncomputable section
open StationaryPowerProfiles StationaryBetaConvolution StationaryNormalization StationaryPowerAsymptotics

/-- Extract the singular excess exponent at the positive truncation endpoint.
The remaining kernel has a genuine integrable complete beta majorant. -/
theorem truncatedBeta_excess_bound (a α ζ x : ℝ)
    (ha : a < 1 / 2) (hα : 2 * a ≤ α) (hζ : ζ < 1)
    (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    0 ≤ truncatedBeta α ζ x ∧ truncatedBeta α ζ x ≤
      x ^ (-(α - 2 * a)) * ProbabilityTheory.beta (1 - 2 * a) (1 - ζ) := by
  have hx1 : x < 1 := by linarith
  have hxx : x ≤ 1 - x := by linarith
  have hnon : 0 ≤ truncatedBeta α ζ x := by
    apply intervalIntegral.integral_nonneg hxx
    intro y hy
    unfold betaKernel
    exact mul_nonneg (Real.rpow_nonneg (by linarith [hy.1] : 0 ≤ y) _)
      (Real.rpow_nonneg (by linarith [hy.2] : 0 ≤ 1 - y) _)
  have hib := betaKernel_intervalIntegrable α ζ x (1 - x) hx0 hx1 (by linarith) (by linarith)
  have hbase := betaKernel_intervalIntegrable (2 * a) ζ x (1 - x) hx0 hx1 (by linarith) (by linarith)
  have hmajor : truncatedBeta α ζ x ≤
      x ^ (-(α - 2 * a)) * truncatedBeta (2 * a) ζ x := by
    unfold truncatedBeta
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hxx hib (hbase.const_mul _)
    intro y hy
    have hy0 : 0 < y := hx0.trans_le hy.1
    have hexp : y ^ (-α) = y ^ (-(α - 2 * a)) * y ^ (-(2 * a)) := by
      rw [← Real.rpow_add hy0]
      congr 1
      ring
    have hr := Real.rpow_le_rpow_of_nonpos hx0 hy.1 (by linarith : -(α - 2 * a) ≤ 0)
    unfold betaKernel
    rw [hexp]
    have hh := mul_le_mul_of_nonneg_right hr
      (mul_nonneg (Real.rpow_pos_of_pos hy0 (-(2 * a))).le
        (Real.rpow_pos_of_pos (by linarith [hy.2] : 0 < 1 - y) (-ζ)).le)
    simpa only [mul_assoc] using hh
  have hunit := intervalIntegral.integral_mono_interval hx0.le hxx
    (by linarith : 1 - x ≤ 1)
    (show 0 ≤ᵐ[volume.restrict (Ioc 0 1)] betaKernel (2 * a) ζ by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_nonneg (Real.rpow_nonneg hy.1.le _) (Real.rpow_nonneg (by linarith [hy.2] : 0 ≤ 1 - y) _))
    (betaKernel_integrable_unit (2 * a) ζ (by linarith) hζ)
  rw [betaKernel_integral_unit (2 * a) ζ (by linarith) hζ] at hunit
  exact ⟨hnon, hmajor.trans (mul_le_mul_of_nonneg_left hunit (Real.rpow_pos_of_pos hx0 _).le)⟩

/-- Unlike the complete-beta asymptotic formula, this estimate permits any
large first exponent. It uses only a<1/2, α>=2a and a<=ζ<1. -/
theorem shifted_higher_convolution_bound (a α ζ : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hα : 2 * a ≤ α)
    (hζ0 : a ≤ ζ) (hζ1 : ζ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≥ 0,
      |deriv (causalConvolution (shiftedPower α) (shiftedPower ζ)) t| ≤
        C * shiftedPower a t ^ 3 := by
  let B := ProbabilityTheory.beta (1 - 2 * a) (1 - ζ)
  let C := |1 - α - ζ| * B + (1 / 2 : ℝ) ^ (-ζ) + (1 / 2 : ℝ) ^ (-α)
  have hB : 0 < B := by
    dsimp [B]
    exact ProbabilityTheory.beta_pos (by linarith) (by linarith)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht
  let T := t + 2
  let x := 1 / T
  have hT : 0 < T := by dsimp [T]; linarith
  have hx0 : 0 < x := one_div_pos.mpr hT
  have hxhalf : x ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by dsimp [T]; linarith)
  have hx1 : x < 1 := by linarith
  have hb := truncatedBeta_excess_bound a α ζ x ha1 hα hζ1 hx0 hxhalf
  have hp : 0 < T ^ (-α - ζ) := Real.rpow_pos_of_pos hT _
  have hscale3 (q : ℝ) (hq : 3 * a ≤ q) : T ^ (-q) ≤ shiftedPower a t ^ 3 := by
    have hq0 : 0 ≤ q := by linarith
    have hbase : T ^ (-q) ≤ (1 + t) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by dsimp [T]; linarith) (by linarith)
    have he : (1 + t) ^ (-q) ≤ (1 + t) ^ (-(3 * a)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1 + t) (by linarith)
    rw [← shiftedPower_nat a t 3 (by linarith)]
    unfold shiftedPower
    norm_num only [Nat.cast_ofNat]
    exact hbase.trans he
  have hproduct (r : ℝ) : T ^ (-α - ζ) * x ^ r = T ^ (-α - ζ - r) := by
    dsimp [x]
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow T r, ← Real.rpow_add hT]
    congr 1
  have hBscale : T ^ (-α - ζ) * truncatedBeta α ζ x ≤ B * shiftedPower a t ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hb.2 hp.le
    rw [← mul_assoc, hproduct, show -α - ζ - -(α - 2 * a) = -(2 * a + ζ) by ring] at hh
    dsimp [B] at *
    calc
      T ^ (-α - ζ) * truncatedBeta α ζ x ≤ T ^ (-(2 * a + ζ)) * ProbabilityTheory.beta (1 - 2 * a) (1 - ζ) := hh
      _ ≤ ProbabilityTheory.beta (1 - 2 * a) (1 - ζ) * shiftedPower a t ^ 3 := by
        have hb' := mul_le_mul_of_nonneg_right (hscale3 (2 * a + ζ) (by linarith)) hB.le
        simpa only [mul_comm] using hb'
  have hbound1 : T ^ (-α - ζ) * (x ^ (1 - α) * (1 - x) ^ (-ζ)) ≤
      (1 / 2 : ℝ) ^ (-ζ) * shiftedPower a t ^ 3 := by
    have hr := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : 1 / 2 ≤ 1 - x) (by linarith : -ζ ≤ 0)
    rw [← mul_assoc, hproduct, show -α - ζ - (1 - α) = -(1 + ζ) by ring]
    exact (mul_le_mul_of_nonneg_left hr (Real.rpow_pos_of_pos hT _).le).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hscale3 (1 + ζ) (by linarith)) (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (-ζ)))
  have hbound2 : T ^ (-α - ζ) * (x ^ (1 - ζ) * (1 - x) ^ (-α)) ≤
      (1 / 2 : ℝ) ^ (-α) * shiftedPower a t ^ 3 := by
    have hr := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : 1 / 2 ≤ 1 - x) (by linarith : -α ≤ 0)
    rw [← mul_assoc, hproduct, show -α - ζ - (1 - ζ) = -(1 + α) by ring]
    exact (mul_le_mul_of_nonneg_left hr (Real.rpow_pos_of_pos hT _).le).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hscale3 (1 + α) (by linarith)) (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (-α)))
  rw [shifted_convolution_derivative α ζ t (by linarith)]
  change |T ^ (-α - ζ) * ((1 - α - ζ) * truncatedBeta α ζ x +
    x ^ (1 - α) * (1 - x) ^ (-ζ) + x ^ (1 - ζ) * (1 - x) ^ (-α))| ≤ C * shiftedPower a t ^ 3
  rw [mul_add, mul_add]
  calc
    _ ≤ |T ^ (-α - ζ) * ((1 - α - ζ) * truncatedBeta α ζ x)| +
      |T ^ (-α - ζ) * (x ^ (1 - α) * (1 - x) ^ (-ζ))| +
      |T ^ (-α - ζ) * (x ^ (1 - ζ) * (1 - x) ^ (-α))| := abs_add_three _ _ _
    _ ≤ (|1 - α - ζ| * B + (1 / 2 : ℝ) ^ (-ζ) + (1 / 2 : ℝ) ^ (-α)) * shiftedPower a t ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_nonneg hb.1,
        abs_of_nonneg (by positivity : 0 ≤ T ^ (-α - ζ) * (x ^ (1 - α) * (1 - x) ^ (-ζ))),
        abs_of_nonneg (by positivity : 0 ≤ T ^ (-α - ζ) * (x ^ (1 - ζ) * (1 - x) ^ (-α)))]
      have hfirst := mul_le_mul_of_nonneg_left hBscale (abs_nonneg (1 - α - ζ))
      dsimp [B] at *
      nlinarith
    _ = C * shiftedPower a t ^ 3 := rfl


@[expose] def correctedPowCoefficient (j : ℕ) (ε : ℝ) (k : ℕ) : ℝ :=
  (j.choose k : ℝ) * (1 + ε) ^ (j - k) * (-ε) ^ k

/-- A finite algebraic identity, valid before integration or differentiation. -/
theorem correctedPower_pow_binomial (a ε t : ℝ) (j : ℕ) :
    correctedPower a ε t ^ j = ∑ k ∈ Finset.range (j + 1),
      correctedPowCoefficient j ε k * shiftedPower a t ^ (j + k) := by
  have he : correctedPower a ε t = (-ε * shiftedPower a t ^ 2) + ((1 + ε) * shiftedPower a t) := by
    unfold correctedPower
    ring
  rw [he, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ j := by simp only [Finset.mem_range] at hk; omega
  simp only [mul_pow, correctedPowCoefficient, ← pow_mul]
  have hp : 2 * k + (j - k) = j + k := by omega
  calc
    _ = (j.choose k : ℝ) * (1 + ε) ^ (j-k) * (-ε)^k *
      (shiftedPower a t ^ (2*k) * shiftedPower a t ^ (j-k)) := by ring
    _ = _ := by rw [← pow_add, hp]

theorem power_convolution_integrable (a t : ℝ) (n m : ℕ) (ht : -1 < t) :
    IntervalIntegrable (fun s => shiftedPower a (t-s)^n * shiftedPower a s^m) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  have hs0 : -1 < s := by rcases mem_uIcc.mp hs with hs | hs <;> linarith
  have hts : -1 < t-s := by rcases mem_uIcc.mp hs with hs | hs <;> linarith
  exact ((((shiftedPower_hasDerivAt a (t-s) hts).continuousAt.comp
    (continuousAt_const.sub continuousAt_id)).pow n).mul
      ((shiftedPower_hasDerivAt a s hs0).continuousAt.pow m)).continuousWithinAt

/-- Bilinearity is proved for the actual interval integral. -/
theorem corrected_power_convolution_expansion (a ε t : ℝ) (j : ℕ) (ht : -1 < t) :
    causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε) t =
      ∑ k ∈ Finset.range (j+1), correctedPowCoefficient j ε k *
        ((1+ε) * causalConvolution (fun s => shiftedPower a s^(j+k)) (shiftedPower a) t -
          ε * causalConvolution (fun s => shiftedPower a s^(j+k)) (fun s => shiftedPower a s^2) t) := by
  unfold causalConvolution
  calc
    _ = ∫ s in 0..t, ∑ k ∈ Finset.range (j+1), correctedPowCoefficient j ε k *
      ((1+ε)*(shiftedPower a (t-s)^(j+k)*shiftedPower a s) -
        ε*(shiftedPower a (t-s)^(j+k)*shiftedPower a s^2)) := by
      apply intervalIntegral.integral_congr
      intro s _
      change correctedPower a ε (t-s)^j * correctedPower a ε s = _
      rw [correctedPower_pow_binomial, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      unfold correctedPower
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        have h1 := power_convolution_integrable a t (j+k) 1 ht
        simp only [pow_one] at h1
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
          (h1.const_mul (1+ε))
          ((power_convolution_integrable a t (j+k) 2 ht).const_mul ε),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      · intro k _
        simpa only [pow_one] using (((power_convolution_integrable a t (j+k) 1 ht).const_mul (1+ε)).sub
          ((power_convolution_integrable a t (j+k) 2 ht).const_mul ε)).const_mul (correctedPowCoefficient j ε k)

theorem power_convolution_differentiableAt (a t : ℝ) (n m : ℕ) (ht : -1 < t) :
    DifferentiableAt ℝ (causalConvolution (fun s => shiftedPower a s^n)
      (fun s => shiftedPower a s^m)) t := by
  have heq : causalConvolution (fun s => shiftedPower a s^n) (fun s => shiftedPower a s^m) =ᶠ[𝓝 t]
      causalConvolution (shiftedPower ((n:ℝ)*a)) (shiftedPower ((m:ℝ)*a)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact power_convolution_eq a s n m hs
  exact ((shifted_convolution_hasDerivAt ((n:ℝ)*a) ((m:ℝ)*a) t ht).congr_of_eventuallyEq heq).differentiableAt

/-- The finite binomial identity holds on an open neighborhood, so its
termwise derivative identity is about the actual causal convolution. -/
theorem corrected_power_convolution_derivative (a ε t : ℝ) (j : ℕ) (ht : -1 < t) :
    deriv (causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε)) t =
      ∑ k ∈ Finset.range (j+1), correctedPowCoefficient j ε k *
        ((1+ε) * deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (shiftedPower a)) t -
          ε * deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (fun s => shiftedPower a s^2)) t) := by
  have heq : causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε) =ᶠ[𝓝 t]
      (fun t => ∑ k ∈ Finset.range (j+1), correctedPowCoefficient j ε k *
        ((1+ε) * causalConvolution (fun s => shiftedPower a s^(j+k)) (shiftedPower a) t -
          ε * causalConvolution (fun s => shiftedPower a s^(j+k)) (fun s => shiftedPower a s^2) t)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact corrected_power_convolution_expansion a ε s j hs
  rw [heq.deriv_eq]
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro k _
  have h1 := (power_convolution_differentiableAt a t (j+k) 1 ht).hasDerivAt
  simp only [pow_one] at h1
  exact ((h1.const_mul (1+ε)).sub
    ((power_convolution_differentiableAt a t (j+k) 2 ht).hasDerivAt.const_mul ε)).const_mul _

/-- The final uniform-in-ε higher convolution bound of Lemma16.5.
Compactness is used only for the finitely many explicit binomial coefficients. -/
theorem corrected_higher_convolution_bound (a : ℝ) (j : ℕ)
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, |ε| ≤ 1 / 4 → ∀ t ≥ 0,
      |deriv (causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε)) t| ≤
        K * shiftedPower a t ^ 3 := by
  have hb (k : ℕ) : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ t ≥ 0,
      |deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (shiftedPower a)) t| ≤ C₁*shiftedPower a t^3 ∧
      |deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (fun s => shiftedPower a s^2)) t| ≤ C₂*shiftedPower a t^3 := by
    have hα : 2*a ≤ ((j+k : ℕ):ℝ)*a := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 ≤ j+k by omega)) ha0.le
    obtain ⟨C₁,hC₁,he₁⟩ := shifted_higher_convolution_bound a (((j+k:ℕ):ℝ)*a) a ha0 ha1 hα le_rfl (by linarith)
    obtain ⟨C₂,hC₂,he₂⟩ := shifted_higher_convolution_bound a (((j+k:ℕ):ℝ)*a) (2*a) ha0 ha1 hα (by linarith) (by linarith)
    refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
    intro t ht
    have hd₁ := power_convolution_derivative_eq a t (j+k) 1 (by linarith)
    simp only [pow_one, Nat.cast_one, one_mul] at hd₁
    have hd₂ := power_convolution_derivative_eq a t (j+k) 2 (by linarith)
    norm_num only [Nat.cast_ofNat] at hd₂
    rw [hd₁,hd₂]
    exact ⟨he₁ t ht,he₂ t ht⟩
  choose C₁ C₂ hC₁ hC₂ hbounds using hb
  let A := fun ε : ℝ => ∑ k ∈ Finset.range (j+1), |correctedPowCoefficient j ε k| *
    (|1+ε| * C₁ k + |ε| * C₂ k)
  have hAcont : Continuous A := by
    dsimp [A,correctedPowCoefficient]
    fun_prop
  obtain ⟨K,hK⟩ := (isCompact_Icc : IsCompact (Icc (-1/4:ℝ) (1/4))).bddAbove_image hAcont.continuousOn
  refine ⟨max K 0 + 1, by positivity, ?_⟩
  intro ε hε t ht
  have hεI : ε ∈ Icc (-1/4:ℝ) (1/4) := by
    rw [abs_le] at hε
    exact ⟨by linarith [hε.1],hε.2⟩
  have hAK : A ε ≤ max K 0 + 1 := (hK ⟨ε,hεI,rfl⟩).trans (by linarith [le_max_left K 0])
  rw [corrected_power_convolution_derivative a ε t j (by linarith)]
  calc
    _ ≤ ∑ k ∈ Finset.range (j+1), |correctedPowCoefficient j ε k| *
      (|1+ε| * |deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (shiftedPower a)) t| +
        |ε| * |deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (fun s => shiftedPower a s^2)) t|) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [abs_mul] using abs_sub
        ((1+ε) * deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (shiftedPower a)) t)
        (ε * deriv (causalConvolution (fun s => shiftedPower a s^(j+k)) (fun s => shiftedPower a s^2)) t)
    _ ≤ A ε * shiftedPower a t^3 := by
      dsimp [A]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k _
      have hb₁ := mul_le_mul_of_nonneg_left (hbounds k t ht).1 (abs_nonneg (1+ε))
      have hb₂ := mul_le_mul_of_nonneg_left (hbounds k t ht).2 (abs_nonneg ε)
      have hs := mul_le_mul_of_nonneg_left (add_le_add hb₁ hb₂) (abs_nonneg (correctedPowCoefficient j ε k))
      convert hs using 1; ring
    _ ≤ (max K 0 + 1) * shiftedPower a t^3 :=
      mul_le_mul_of_nonneg_right hAK (pow_nonneg (shiftedPower_pos a t ht).le _)

end
end SphericalAging.StationaryHigherPowerBound
