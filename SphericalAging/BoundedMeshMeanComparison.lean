module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real

public section

/-! Mean comparison across a finite mesh, retaining the exact cost of
the exceptional sample-path event. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.BoundedMeshMeanComparison
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem mean_difference_le_bad_event {f g : Ω→ℝ} (hf : Integrable f P) (hg : Integrable g P)
    {bad : Set Ω} (hbad : MeasurableSet bad) {e B : ℝ} (he : 0 ≤ e) (hB : 0 ≤ B)
    (hglobal : ∀ᵐω ∂P,|f ω-g ω| ≤ B)
    (hgood : ∀ᵐω ∂P,ω ∉ bad → |f ω-g ω| ≤ e) :
    |(∫ω,f ω ∂P)-(∫ω,g ω ∂P)| ≤ e+B*P.real bad := by
  have hi : Integrable (fun ω => e+B*bad.indicator (fun _ => (1:ℝ)) ω) P :=
    (integrable_const e).add (((integrable_const (1:ℝ)).indicator hbad).const_mul B)
  have hb : ∀ᵐω ∂P,|f ω-g ω| ≤ e+B*bad.indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [hglobal,hgood] with ω hω hgω
    by_cases h : ω ∈ bad
    · simp only [indicator_of_mem h,mul_one]
      linarith
    · simpa only [indicator_of_notMem h,mul_zero,add_zero] using hgω h
  rw [←integral_sub hf hg]
  refine abs_integral_le_integral_abs.trans ((integral_mono_ae (hf.sub hg).abs hi hb).trans_eq ?_)
  rw [integral_add (integrable_const e) (((integrable_const (1:ℝ)).indicator hbad).const_mul B),
    integral_const_mul,integral_indicator hbad]
  simp only [integral_const,probReal_univ,one_smul,smul_eq_mul,mul_one,one_mul,measureReal_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ,ENNReal.toReal_one]

end SphericalAging.BoundedMeshMeanComparison
