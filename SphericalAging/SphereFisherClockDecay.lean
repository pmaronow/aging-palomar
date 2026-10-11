module

public import SphericalAging.SphereFisherClock
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

/-! True pointwise late Fisher decay for the actual positive spherical forward
density. Integrability comes from the proved initial entropy budget, and the
uniform tail bound comes from the genuine differential clock. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFisherClockDecay

open MeasureTheory Set Filter FiniteModel SphereInitialLaw SphereRotationGeometry
open SphereCanonicalEntropy SphereFisherClock SphereMixedDerivatives
open scoped Topology

theorem curvatureRate_nonneg {N p : ℕ} {β : ℝ} (hβ : 0≤β) (J : Disorder N p) :
    0≤curvatureRate β J := by
  unfold curvatureRate
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) (sq_nonneg _))
    (GaussianLandscape.landscapeNorm_nonnegative N p J)

theorem spherical_fisher_time_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hinit : ∀ x,ρ 0 x=1)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x) :
    IntegrableOn (fun t => fisherInformation β J (ρ t)) (Ioi 0) := by
  have hρ₂ : ContDiff ℝ 2 (Function.uncurry ρ) := hρ.of_le (by norm_num)
  exact (spherical_fisher_budget hN hp hβ J hρ₂ (timeSlope_contDiff_one hρ₂).continuous hpos
    (timeSlope_hasDerivAt (hρ.of_le (by norm_num))) hinit hPDE).1

theorem spherical_fisher_nonneg {N p : ℕ} (β : ℝ) (J : Disorder N p)
    {ρ : ℝ → Vector N → ℝ} (hpos : ∀ t x,0<ρ t x) (t : ℝ) :
    0≤fisherInformation β J (ρ t) := by
  unfold fisherInformation
  exact integral_nonneg fun x => mul_nonneg (hpos t x).le (sq_nonneg _)

theorem spherical_fisher_tail_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hinit : ∀ x,ρ 0 x=1)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x)
    {t : ℝ} (ht : 1≤t) :
    fisherInformation β J (ρ t) ≤ Real.exp (curvatureRate β J)*
      (∫ u in Ioi (t-1),fisherInformation β J (ρ u)) := by
  have hi := spherical_fisher_time_integrable hN (by omega) hβ J hρ hpos hinit hPDE
  have hnon := spherical_fisher_nonneg β J hpos
  have hC := spherical_fisher_continuous hN β J (hρ.of_le (by norm_num)) hpos
  have hK := curvatureRate_nonneg hβ J
  have hpoint u (hu : u ∈ Icc (t-1) t) : fisherInformation β J (ρ t) ≤
      Real.exp (curvatureRate β J)*fisherInformation β J (ρ u) := by
    have hu0 : 0≤u := by linarith [hu.1]
    have hh := spherical_fisher_exponential_comparison hN hp hβ J hρ hpos hPDE hu0 hu.2
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [hu.1])) (hnon u))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : t-1≤t)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => fisherInformation β J (ρ t)) volume (t-1) t)
    ((hC.const_mul (Real.exp (curvatureRate β J))).intervalIntegrable (t-1) t) hpoint
  have hconst : (∫ u in (t-1)..t,fisherInformation β J (ρ t)) = fisherInformation β J (ρ t) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hconst, intervalIntegral.integral_const_mul] at hmono
  have hitail := hi.mono_set (Ioi_subset_Ioi (by linarith : 0≤t-1))
  have htail := setIntegral_mono_set hitail (ae_of_all _ hnon)
    (ae_of_all volume (show Ioc (t-1) t ⊆ Ioi (t-1) from fun u hu => hu.1))
  rw [← intervalIntegral.integral_of_le (by linarith : t-1≤t)] at htail
  exact hmono.trans (mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le)

/-- The actual Fisher information tends to zero, and hence is uniformly small
at all sufficiently late times. This follows from the proved budget and clock. -/
theorem spherical_fisher_tendsto_zero {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hinit : ∀ x,ρ 0 x=1)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x) :
    Tendsto (fun t => fisherInformation β J (ρ t)) atTop (𝓝 0) := by
  have htail : Tendsto (fun t : ℝ => ∫ u in Ioi (t-1),fisherInformation β J (ρ u)) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  apply squeeze_zero' (Eventually.of_forall (spherical_fisher_nonneg β J hpos))
    ((eventually_ge_atTop (1 : ℝ)).mono fun t ht => spherical_fisher_tail_bound hN hp hβ J hρ hpos hinit hPDE ht)
  simpa only [mul_zero] using htail.const_mul (Real.exp (curvatureRate β J))

end SphericalAging.SphereFisherClockDecay
