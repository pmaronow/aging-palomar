module

public import SphericalAging.LogBetaSmoothedRenewal

public section

/-! Actual positive convolution densities vanish at infinity and are
uniformly bounded on the tail starting at one. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.LogBetaPowerDecay
noncomputable section
open GammaEnvelopeConvolution GammaEnvelopeDRI LogBetaConvolutionPowers

theorem envelope_limit_zero (F : ℝ → ℝ) (A α κ : ℝ) (hκ : 0<κ)
    (hF : EnvelopeInput F A α κ) : Tendsto F atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => A*(t^(α-1)*Real.exp (-κ*t))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (α-1) κ hκ).const_mul A
  apply squeeze_zero' (Eventually.of_forall hF.nonnegative) _ hlim
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  simpa only [mul_assoc] using hF.bound t ht

theorem envelope_tail_bound (F : ℝ → ℝ) (A α κ : ℝ) (hA : 0≤A) (hκ : 0<κ)
    (hF : EnvelopeInput F A α κ) : ∃ C : ℝ,0≤C ∧ ∀ t≥1,F t≤C := by
  by_cases hα : α≤1
  · refine ⟨A,hA,?_⟩
    intro t ht
    have ht0 : 0<t := by linarith
    have hp : t^(α-1)≤1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
    have he : Real.exp (-κ*t)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hx : t^(α-1)*Real.exp (-κ*t)≤1 :=
      (mul_le_mul hp he (Real.exp_pos _).le (by norm_num)).trans_eq (by ring)
    exact (hF.bound t ht0).trans (by simpa only [mul_assoc,mul_one] using mul_le_mul_of_nonneg_left hx hA)
  · obtain ⟨C,hC,hb⟩ := power_decay_inverse_square (α-1) κ (by linarith) hκ
    refine ⟨A*C,mul_nonneg hA hC.le,?_⟩
    intro t ht
    have ht0 : 0<t := by linarith
    have hh := mul_le_mul_of_nonneg_left (hb t ht0) hA
    have hDen : C/(1+t^2)≤C := div_le_self hC.le (by nlinarith [sq_nonneg t])
    exact (hF.bound t ht0).trans (by simpa only [mul_assoc] using hh.trans (mul_le_mul_of_nonneg_left hDen hA))

theorem powerDensity_limit_zero {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (n : ℕ) :
    Tendsto (powerDensity ρ a n) atTop (𝓝 0) :=
  envelope_limit_zero _ _ _ _ (by linarith : 0<ρ/2) (powerDensity_properties hρ ha ha1 n).1

theorem powerDensity_tail_bound {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀t≥1,powerDensity ρ a n t≤C :=
  envelope_tail_bound _ _ _ _ (powerConstant_positive hρ ha n).le (by linarith : 0<ρ/2)
    (powerDensity_properties hρ ha ha1 n).1

end
end SphericalAging.LogBetaPowerDecay
