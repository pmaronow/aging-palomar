module

public import SphericalAging.ThermalRowConvergence
public import SphericalAging.GreenCovarianceClosure

public section

/-! The actual full colored rectangle retains any aging correlation after
the initial and thermal terms vanish on late pairs of diverging lag. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ThermalAging
open CKSpecification GreenCovariance StrongBackwardDefect BackwardRowL2
  ThermalRowConvergence GreenCovarianceClosure

theorem correlation_green_decomposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0≤t) (hs : 0≤s) :
    d.C t s=initialTerm d t s+whiteTerm d t s+coloredTerm p β d t s := by
  rw [green_covariance_identity h ht hs,←clampedGreen_eq ht hs,clampedGreen_decomposition]

theorem coloredTerm_causal_rectangle {p : ℕ} {β : ℝ} {d : CKData}
    {t s : ℝ} (ht : 0≤t) (hs : 0≤s) :
    coloredTerm p β d t s=β^2*(p:ℝ)*(∫u in (0:ℝ)..t,∫v in (0:ℝ)..s,
      d.R t u*d.R s v*(d.C u v)^(p-1)) := by
  rw [coloredTerm_eq_double_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hs] at hv
  dsimp only
  rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2,
    clampedCorrelation_eq hu.1 hv.1]

/-- The full source colored-aging conclusion, for arbitrary late causal
sequences/filter families with diverging lag and convergent correlation. -/
theorem colored_aging_rectangle {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0))
    (hdecay : Tendsto (thermalProfile r) atTop (𝓝 0))
    {ι : Type*} {F : Filter ι} {t s : ι→ℝ} (hs : Tendsto s F atTop)
    (hlag : Tendsto (fun n => t n-s n) F atTop) {c₀ : ℝ}
    (hC : Tendsto (fun n => d.C (t n) (s n)) F (𝓝 c₀)) :
    Tendsto (fun n => β^2*(p:ℝ)*(∫u in (0:ℝ)..t n,∫v in (0:ℝ)..s n,
      d.R (t n) u*d.R (s n) v*(d.C u v)^(p-1))) F (𝓝 c₀) := by
  have hts : ∀ᶠn in F,s n≤t n := by
    filter_upwards [hlag.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    linarith
  have ht : Tendsto t F atTop := tendsto_atTop_mono' F hts hs
  have hR0 := response_fixed_wait_tendsto h hb hforget (s:=0) le_rfl
  have hinit : Tendsto (fun n => initialTerm d (t n) (s n)) F (𝓝 0) := by
    have he := (hR0.comp ht).mul (hR0.comp hs)
    simp only [mul_zero] at he
    apply he.congr'
    filter_upwards [ht.eventually (eventually_ge_atTop (0:ℝ)),
      hs.eventually (eventually_ge_atTop (0:ℝ))] with n htn hsn
    rw [initialTerm,clampedResponse_eq le_rfl htn,clampedResponse_eq le_rfl hsn]
    rfl
  have hthermal := thermal_late_diverging_pair h hr hrow hdecay hs hlag
  have he := (hC.sub hinit).sub hthermal
  simp only [sub_zero] at he
  apply he.congr'
  filter_upwards [ht.eventually (eventually_ge_atTop (0:ℝ)),
    hs.eventually (eventually_ge_atTop (0:ℝ))] with n htn hsn
  rw [correlation_green_decomposition h htn hsn,
    ←coloredTerm_causal_rectangle htn hsn]
  ring

end SphericalAging.ThermalAging
