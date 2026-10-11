module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

/-! Quantitative true second-moment perturbation by two square-integrable
remainders, with arbitrarily small loss in the leading term. -/
noncomputable section
open MeasureTheory Filter
namespace SphericalAging.SecondMomentPerturbation
set_option maxHeartbeats 800000
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem square_sum_le (a b η : ℝ) (hη : 0<η) :
    (a+b)^2≤(1+η)*a^2+(1+1/η)*b^2 := by
  have he : (1+η)*a^2+(1+1/η)*b^2-(a+b)^2=(η*a-b)^2/η := by
    field_simp
    ring
  have hh := div_nonneg (sq_nonneg (η*a-b)) hη.le
  linarith only [he,hh]

theorem integral_square_perturbation (A B R L : Ω→ℝ)
    (hAi : Integrable (fun ω => (A ω)^2) P) (hBi : Integrable (fun ω => (B ω)^2) P)
    (hRi : Integrable (fun ω => (R ω)^2) P) (hLi : Integrable (fun ω => (L ω)^2) P)
    (hEq : ∀ᵐ ω ∂P,A ω=B ω+R ω+L ω) (η : ℝ) (hη : 0<η) :
    (∫ ω,(A ω)^2 ∂P)≤(1+η)*(∫ ω,(B ω)^2 ∂P)+
      2*(1+1/η)*((∫ ω,(R ω)^2 ∂P)+(∫ ω,(L ω)^2 ∂P)) := by
  have hRLi : Integrable (fun ω => (R ω)^2+(L ω)^2) P := hRi.add hLi
  have hUi : Integrable (fun ω => (1+η)*(B ω)^2+
      2*(1+1/η)*((R ω)^2+(L ω)^2)) P :=
    (hBi.const_mul (1+η)).add (hRLi.const_mul (2*(1+1/η)))
  have hpoint : ∀ᵐ ω ∂P,(A ω)^2≤(1+η)*(B ω)^2+
      2*(1+1/η)*((R ω)^2+(L ω)^2) := by
    filter_upwards [hEq] with ω hω
    rw [hω,add_assoc]
    have hs := square_sum_le (B ω) (R ω+L ω) η hη
    have hr : (R ω+L ω)^2≤2*(R ω)^2+2*(L ω)^2 := by nlinarith [sq_nonneg (R ω-L ω)]
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤1+1/η by positivity)
    nlinarith only [hs,hh]
  have hi := integral_mono_ae hAi hUi hpoint
  rwa [integral_add (hBi.const_mul (1+η)) (hRLi.const_mul (2*(1+1/η))),
    integral_const_mul,integral_const_mul,integral_add hRi hLi] at hi

end SphericalAging.SecondMomentPerturbation
