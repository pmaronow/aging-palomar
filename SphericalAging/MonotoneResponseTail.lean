module

public import SphericalAging.EarlierSmoothing

public section

/-! The actual age-weighted squared response tail tends to zero from
nonnegativity, monotonicity and ordinary integrability. No power law is needed. -/
noncomputable section
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.MonotoneResponseTail
open EarlierSmoothing

theorem square_integrable_ray {r : ℝ → ℝ}
    (hc : ContinuousOn r (Ici 0)) (hpos : ∀ x, 0 ≤ x → 0 ≤ r x)
    (hmono : AntitoneOn r (Ici 0)) (hr0 : r 0 ≤ 1)
    (hi : IntegrableOn r (Ici 0)) : IntegrableOn (fun x => (r x)^2) (Ici 0) := by
  apply hi.mono' ((hc.pow 2).aestronglyMeasurable measurableSet_Ici)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh := hmono (show (0 : ℝ) ∈ Ici 0 from by simp) hx hx
  have hp := hpos x hx
  change (r x)^2 ≤ r x
  nlinarith

/-- The elementary true interval bound D*r(D) ≤ total response mass. -/
theorem age_response_le_mass {r : ℝ → ℝ}
    (hc : ContinuousOn r (Ici 0)) (hpos : ∀ x, 0 ≤ x → 0 ≤ r x)
    (hmono : AntitoneOn r (Ici 0)) (hi : IntegrableOn r (Ici 0))
    {D : ℝ} (hD : 0 ≤ D) : D*r D ≤ ∫ x in Ici (0 : ℝ), r x := by
  have hr : IntervalIntegrable r volume 0 D :=
    (hc.mono (fun x hx => hx.1)).intervalIntegrable_of_Icc hD
  have hb := intervalIntegral.integral_mono_on (μ := volume) hD
    (f := fun _ : ℝ => r D) intervalIntegrable_const hr
    (fun x hx => hmono hx.1 hD hx.2)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hb
  apply hb.trans
  rw [intervalIntegral.integral_of_le hD]
  exact setIntegral_mono_set hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact hpos x hx)
    (Eventually.of_forall (fun x hx => show x ∈ Ici (0 : ℝ) from hx.1.le))

/-- The squared tail is bounded by the endpoint response times the true
unsquared tail integral, by monotonicity inside the actual measure integral. -/
theorem square_tail_le_endpoint {r : ℝ → ℝ}
    (hc : ContinuousOn r (Ici 0)) (hpos : ∀ x, 0 ≤ x → 0 ≤ r x)
    (hmono : AntitoneOn r (Ici 0)) (hr0 : r 0 ≤ 1)
    (hi : IntegrableOn r (Ici 0)) {D : ℝ} (hD : 0 ≤ D) :
    responseTail r D ≤ r D*(∫ x in Ici D, r x) := by
  have hir := hi.mono_set (Ici_subset_Ici.mpr hD)
  have hi2 := (square_integrable_ray hc hpos hmono hr0 hi).mono_set (Ici_subset_Ici.mpr hD)
  rw [responseTail,← integral_const_mul]
  apply setIntegral_mono_on hi2 (hir.const_mul (r D)) measurableSet_Ici
  intro x hx
  have hh := hmono hD (hD.trans hx) hx
  have hp := hpos x (hD.trans hx)
  nlinarith

/-- Exact second source smoothing-modulus limit, proved solely from the
nonincreasing integrable response profile. -/
theorem age_square_tail_tendsto {r : ℝ → ℝ}
    (hc : ContinuousOn r (Ici 0)) (hpos : ∀ x, 0 ≤ x → 0 ≤ r x)
    (hmono : AntitoneOn r (Ici 0)) (hr0 : r 0 ≤ 1)
    (hi : IntegrableOn r (Ici 0)) :
    Tendsto (fun D : ℝ => D*responseTail r D) atTop (nhds 0) := by
  let M := ∫ x in Ici (0 : ℝ), r x
  have ht : Tendsto (fun D : ℝ => ∫ x in Ici D, r x) atTop (nhds 0) :=
    tendsto_integral_Ici_zero tendsto_id
  have hbound := ht.const_mul M
  simp only [mul_zero] at hbound
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
    exact mul_nonneg hD (integral_nonneg (fun _ => sq_nonneg _))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
    have h1 := mul_le_mul_of_nonneg_left (square_tail_le_endpoint hc hpos hmono hr0 hi hD) hD
    have ht0 : 0 ≤ ∫ x in Ici D, r x := integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      exact hpos x (hD.trans hx))
    have h2 := mul_le_mul_of_nonneg_right (age_response_le_mass hc hpos hmono hi hD) ht0
    dsimp only [M] at *
    nlinarith

/-- Equivalent square-root form occurring in the actual center-Gram modulus. -/
theorem sqrt_age_square_tail_tendsto {r : ℝ → ℝ}
    (hc : ContinuousOn r (Ici 0)) (hpos : ∀ x, 0 ≤ x → 0 ≤ r x)
    (hmono : AntitoneOn r (Ici 0)) (hr0 : r 0 ≤ 1)
    (hi : IntegrableOn r (Ici 0)) :
    Tendsto (fun D : ℝ => Real.sqrt D*Real.sqrt (responseTail r D)) atTop (nhds 0) := by
  have hl := (age_square_tail_tendsto hc hpos hmono hr0 hi).sqrt
  simp only [Real.sqrt_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
  exact Real.sqrt_mul hD _

end SphericalAging.MonotoneResponseTail
