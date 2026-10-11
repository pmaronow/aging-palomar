module

public import SphericalAging.GammaEnvelopeDRI
public import SphericalAging.LogBetaMean

public section

/-! Fully discharged actual key-renewal applicability for finite smoothed
log-beta convolution densities, with a uniform genuine series bound. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.LogBetaSmoothedRenewal
noncomputable section
open LogBetaRenewal LogBetaMoments LogBetaConvolutionPowers GammaEnvelopeDRI
  GammaEnvelopeConvolution AbsorptionCutoff.Renewal

@[expose] def smoothedRenewal (ρ a : ℝ) (j : ℕ) (y : ℝ) :=
  ∑' n : ℕ,∫ s : ℝ,powerDensity ρ a j (y-s) ∂convPow (law ρ a) n

/-- Any finite power whose shape exceeds one is an actual continuous
probability density with finite DRI norm and a global bound. -/
theorem smoothing_properties {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (j : ℕ) (hj : 1<((j:ℝ)+1)*a) :
    Continuous (powerDensity ρ a j) ∧
    driNorm (fun y => ‖powerDensity ρ a j y‖ₑ)≠∞ ∧
    ∃ B : ℝ,0<B ∧ ∀ y : ℝ,0≤powerDensity ρ a j y ∧ powerDensity ρ a j y≤B := by
  obtain ⟨hF,hC,_,_⟩ := powerDensity_properties hρ ha ha1 j
  have hA := (powerConstant_positive hρ ha j).le
  have hc := envelope_continuous _ _ _ _ hA hj hF hC
  have hd := envelope_driNorm_finite _ _ _ _ hA hj (by linarith : 0<ρ/2) hF
  obtain ⟨C,hC,hb⟩ := power_decay_inverse_square (((j:ℝ)+1)*a-1) (ρ/2) (by linarith) (by linarith)
  refine ⟨hc,hd,powerConstant ρ a j*C,mul_pos (powerConstant_positive hρ ha j) hC,?_⟩
  intro y
  refine ⟨hF.nonnegative y,?_⟩
  by_cases hy : 0<y
  · have hh := mul_le_mul_of_nonneg_left (hb y hy) hA
    have hDen : powerConstant ρ a j*(C/(1+y^2))≤powerConstant ρ a j*C := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact (div_le_self hC.le (by nlinarith [sq_nonneg y]))
    exact (hF.bound y hy).trans (by simpa only [mul_assoc] using hh.trans hDen)
  · rw [hF.zero y (le_of_not_gt hy)]
    positivity

/-- Finite smoothing always exists for a>0. -/
theorem exists_smoothing_index (a : ℝ) (ha : 0<a) : ∃ j : ℕ,1<((j:ℝ)+1)*a := by
  obtain ⟨j,hj⟩ := exists_nat_gt (1/a)
  refine ⟨j,?_⟩
  have hh := (div_lt_iff₀ ha).mp hj
  nlinarith only [hh,ha]

/-- The key-renewal theorem applies to the actual smoothed log-beta law,
with no assumed continuous density, DRI norm or moment conditions. -/
theorem smoothed_renewal_limit {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (j : ℕ) (hj : 1<((j:ℝ)+1)*a) :
    Tendsto (smoothedRenewal ρ a j) atTop (𝓝 (1/(∫ y : ℝ,y ∂law ρ a))) := by
  letI := law_probability hρ ha
  obtain ⟨hC,hDri,_⟩ := smoothing_properties hρ ha ha1 j hj
  have h := KeyRenewal.real_key_renewal (law_nonlattice hρ ha) (second_moment_memLp hρ ha)
    (mean_positive hρ ha) (by norm_num : (0:ℝ)<1) (negative_expTransform_lt_one hρ ha (by norm_num : (0:ℝ)<1))
    hC hDri
  rw [(powerDensity_properties hρ ha ha1 j).2.2.2] at h
  exact h

/-- The actual smoothed renewal series is absolutely summable at every
point and bounded uniformly on the whole real line. -/
theorem smoothed_renewal_uniform_bound {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (j : ℕ) (hj : 1<((j:ℝ)+1)*a) :
    (∀y : ℝ,Summable (fun n : ℕ => ∫ s : ℝ,powerDensity ρ a j (y-s) ∂convPow (law ρ a) n)) ∧
    ∃ C : ℝ,0≤C ∧ ∀y : ℝ,0≤smoothedRenewal ρ a j y ∧ smoothedRenewal ρ a j y≤C := by
  letI := law_probability hρ ha
  obtain ⟨hC,hDri,_⟩ := smoothing_properties hρ ha ha1 j hj
  obtain ⟨C,hCells⟩ := KeyRenewal.uniform_renewal_cell_bound (law_nonlattice hρ ha) (second_moment_memLp hρ ha)
    (mean_positive hρ ha) (by norm_num : (0:ℝ)<1) (negative_expTransform_lt_one hρ ha (by norm_num : (0:ℝ)<1)) 1
  let H := fun x : ℝ => (powerDensity ρ a j x : ℂ)
  have hDriC : driNorm (fun x => ‖H x‖ₑ)≠∞ := by simpa [H,enorm_eq_nnnorm] using hDri
  have hSum (y : ℝ) : Summable (fun n : ℕ => ∫ s : ℝ,powerDensity ρ a j (y-s) ∂convPow (law ρ a) n) := by
    have hs := summable_integral_comp_sub_of_driNorm hCells ENNReal.ofReal_ne_top hDriC y
    rw [←Complex.summable_ofReal]
    simpa only [H,integral_complex_ofReal] using hs
  have hn (y : ℝ) (n : ℕ) : 0≤∫ s : ℝ,powerDensity ρ a j (y-s) ∂convPow (law ρ a) n :=
    integral_nonneg (fun s => (powerDensity_properties hρ ha ha1 j).1.nonnegative (y-s))
  refine ⟨hSum,(ENNReal.ofReal C*driNorm (fun x => ‖H x‖ₑ)).toReal,ENNReal.toReal_nonneg,?_⟩
  intro y
  refine ⟨tsum_nonneg (hn y),?_⟩
  have hb := tsum_norm_integral_comp_sub_le hCells ENNReal.ofReal_ne_top hDriC y
  calc
    _ = ∑' n : ℕ,‖∫ s : ℝ,H (y-s) ∂convPow (law ρ a) n‖ := by
      apply tsum_congr
      intro n
      rw [show (fun s : ℝ => H (y-s))=(fun s => ((powerDensity ρ a j (y-s):ℝ):ℂ)) from rfl,
        integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn y n)]
    _ ≤ _ := hb

end
end SphericalAging.LogBetaSmoothedRenewal
