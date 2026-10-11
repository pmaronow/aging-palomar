module

public import SphericalAging.MonotoneResponseTail
public import Mathlib.Analysis.SpecialFunctions.Exp

public section

/-! Genuine age-weighted second spectral moment decay. The actual spectral
law supplies its measure and derivative formula; dominated convergence is proved. -/
noncomputable section
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.SpectralSmoothingModulus

@[expose] def ageMoment (D x : ℝ) : ℝ := (D*x)^2*Real.exp (-2*D*x)

theorem ageMoment_bound {D x : ℝ} (hD : 0 ≤ D) (hx : 0 ≤ x) :
    |ageMoment D x| ≤ 1 := by
  let y := D*x
  have hy : 0 ≤ y := mul_nonneg hD hx
  have he : y ≤ Real.exp y := by have hh := Real.add_one_le_exp y; linarith
  have hesq : y^2 ≤ (Real.exp y)^2 := (sq_le_sq₀ hy (Real.exp_pos y).le).mpr he
  have hexp : (Real.exp y)^2*Real.exp (-2*y)=1 := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    simp
  have hb := mul_le_mul_of_nonneg_right hesq (Real.exp_pos (-2*y)).le
  rw [hexp] at hb
  unfold ageMoment
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
  convert hb using 1 <;> dsimp only [y] <;> congr 1 <;> ring

theorem ageMoment_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun D : ℝ => ageMoment D x) atTop (nhds 0) := by
  by_cases hx0 : x=0
  · simp only [ageMoment,hx0,mul_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul]
    exact tendsto_const_nhds
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have harg : Tendsto (fun D : ℝ => 2*x*D) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (mul_pos (by norm_num) hxpos)).mpr tendsto_id
  have hl := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp harg).const_mul (1/4 : ℝ)
  simp only [mul_zero] at hl
  convert hl using 1
  funext D
  dsimp only [ageMoment,Function.comp_def]
  rw [show -2*D*x = -(2*x*D) from by ring]
  ring

/-- The first source smoothing modulus is a genuine finite-measure dominated
convergence theorem, including the zero-frequency atom. -/
theorem age_second_moment_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    Tendsto (fun D : ℝ => ∫ x : ℝ, ageMoment D x ∂ν) atTop (nhds 0) := by
  have hl : Tendsto (fun D : ℝ => ∫ x : ℝ, ageMoment D x ∂ν) atTop
      (nhds (∫ _x : ℝ, (0 : ℝ) ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall (fun D => by unfold ageMoment; fun_prop)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
      filter_upwards [hν] with x hx
      simpa only [Real.norm_eq_abs] using ageMoment_bound hD hx
    · exact integrable_const 1
    · filter_upwards [hν] with x hx
      exact ageMoment_tendsto hx
  simpa only [integral_zero] using hl

/-- Exact application to the profile's ordinary second derivative formula. -/
theorem age_second_derivative_tendsto {c : ℝ → ℝ} (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (hsecond : ∀ t : ℝ, 0 < t → iteratedDeriv 2 c t = ∫ x : ℝ, x^2*Real.exp (-x*t) ∂ν) :
    Tendsto (fun D : ℝ => D^2*iteratedDeriv 2 c (2*D)) atTop (nhds 0) := by
  apply (age_second_moment_tendsto ν hν).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  rw [hsecond (2*D) (by positivity),←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    unfold ageMoment
    rw [show -2*D*x = -x*(2*D) from by ring]
    ring)

/-- The exact later-coordinate smoothing error in the center-Gram theorem
vanishes as the age tends to infinity. -/
theorem age_sqrt_second_derivative_tendsto {c : ℝ → ℝ} (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (hsecond : ∀ t : ℝ, 0 < t → iteratedDeriv 2 c t = ∫ x : ℝ, x^2*Real.exp (-x*t) ∂ν) :
    Tendsto (fun D : ℝ => D*Real.sqrt (iteratedDeriv 2 c (2*D))) atTop (nhds 0) := by
  have hl := (age_second_derivative_tendsto ν hν hsecond).sqrt
  simp only [Real.sqrt_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
  rw [Real.sqrt_mul (sq_nonneg D),Real.sqrt_sq hD]

end SphericalAging.SpectralSmoothingModulus
