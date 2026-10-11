module

public import Mathlib.Probability.CondVar

public section

/-! True conditional prediction variance identities and comparison with
any square-integrable observable measurable in the conditioning history. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace SphericalAging.ConditionalPredictionVariance
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {m : MeasurableSpace Ω} (hm : m≤m₀)
  {A B C : Ω→ℝ}
include hm

theorem innovation_variance_identity (hA : MemLp A 2 P)
    (hCE : P[A | m]=ᵐ[P] B) :
    (∫ ω,(A ω-B ω)^2 ∂P)+variance B P=variance A P := by
  have hBi := (hA.condExp (by norm_num)).ae_eq hCE
  have hvar := integral_condVar_add_variance_condExp hm hA
  rw [variance_congr hCE] at hvar
  have hsq : Integrable ((A-P[A | m])^2) P :=
    (hA.sub (hA.condExp (by norm_num))).integrable_sq
  have he : (∫ ω,ProbabilityTheory.condVar m A P ω ∂P)=∫ ω,(A ω-B ω)^2 ∂P := by
    have hh := setIntegral_condVar (hm:=hm) hsq MeasurableSet.univ
    simp only [setIntegral_univ] at hh
    exact hh.trans (integral_congr_ae (hCE.mono (fun _ h => by simp only [Pi.pow_apply,Pi.sub_apply,h])))
  rw [he] at hvar
  exact hvar

/-- Conditional expectation is the optimal mean-square predictor, with
all integrability and conditional variance steps checked. -/
theorem innovation_le_prediction_error (hA : MemLp A 2 P) (hC : MemLp C 2 P)
    (hCm : AEStronglyMeasurable[m] C P) (hCE : P[A | m]=ᵐ[P] B) :
    (∫ ω,(A ω-B ω)^2 ∂P)≤∫ ω,(A ω-C ω)^2 ∂P := by
  have hAC := hA.sub hC
  have hCeq : P[C | m]=ᵐ[P] C :=
    condExp_of_aestronglyMeasurable' hm hCm (hC.integrable (by norm_num))
  have hCEdiff : P[A-C | m]=ᵐ[P] fun ω => B ω-C ω := by
    filter_upwards [condExp_sub (hA.integrable (by norm_num)) (hC.integrable (by norm_num)) m,hCE,hCeq] with ω h1 h2 h3
    simpa only [Pi.sub_apply,h2,h3] using h1
  have hsq : Integrable ((A-C-P[A-C | m])^2) P :=
    (hAC.sub (hAC.condExp (by norm_num))).integrable_sq
  have he : (∫ ω,ProbabilityTheory.condVar m (A-C) P ω ∂P)=∫ ω,(A ω-B ω)^2 ∂P := by
    have hh := setIntegral_condVar (hm:=hm) hsq MeasurableSet.univ
    simp only [setIntegral_univ] at hh
    exact hh.trans (integral_congr_ae (hCEdiff.mono (fun ω h => by
      simp only [Pi.pow_apply,Pi.sub_apply,h]
      ring)))
  have hh := integral_mono_ae integrable_condVar integrable_condExp (condVar_ae_le_condExp_sq hm hAC)
  rw [he,integral_condExp hm] at hh
  exact hh

end SphericalAging.ConditionalPredictionVariance
