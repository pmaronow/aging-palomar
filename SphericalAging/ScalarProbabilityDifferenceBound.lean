module

public import SphericalAging.ResponseMatrixEnergyContraction

public section

/-! A probability mean difference follows from genuine integrable
quadratic domination of the scalar difference. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SphericalAging.ScalarProbabilityDifferenceBound
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem mean_difference_le_sqrt_ceiling (f g d : Ω→ℝ)
    (hf : Integrable f P) (hg : Integrable g P) (hd : Integrable d P)
    (hb : ∀ᵐ omega ∂P,(f omega-g omega)^2≤d omega)
    (C : ℝ) (hC : (∫omega,d omega ∂P)≤C) :
    |(∫omega,f omega ∂P)-(∫omega,g omega ∂P)|≤Real.sqrt C := by
  have hsm := hf.aestronglyMeasurable.sub hg.aestronglyMeasurable
  have hi : Integrable (fun omega => (f omega-g omega)^2) P :=
    hd.mono_nonneg (hsm.pow 2) (.of_forall (fun omega => sq_nonneg _)) hb
  have hm : MemLp (fun omega => f omega-g omega) 2 P :=
    (memLp_two_iff_integrable_sq hsm).mpr hi
  have he := (integral_mono_ae hi hd hb).trans hC
  rw [←integral_sub hf hg]
  exact abs_integral_le_integral_abs.trans
    ((ResponseMatrixEnergyContraction.integral_abs_le_sqrt_secondMoment hm).trans
      (Real.sqrt_le_sqrt he))

end SphericalAging.ScalarProbabilityDifferenceBound
