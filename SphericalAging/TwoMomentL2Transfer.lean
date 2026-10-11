module

public import SphericalAging.ForkFisherWindowLimit

public section

/-! Exact second-moment transfer from the first two scalar moments.
This is the algebra used after the actual fork current comparison. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TwoMomentL2Transfer
open MeasureTheory

theorem centered_square_eq_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Q : Ω→ℝ}
    (hQ : Integrable Q μ) (hQ2 : Integrable (fun ω => (Q ω)^2) μ) (c : ℝ) :
    (∫ω,(Q ω-c)^2 ∂μ)=(∫ω,(Q ω)^2 ∂μ)-2*c*(∫ω,Q ω ∂μ)+c^2 := by
  have he : (fun ω => (Q ω-c)^2)=(fun ω => (Q ω)^2-2*c*Q ω+c^2) := by
    funext ω;ring
  have hsum := integral_add (hQ2.sub (hQ.const_mul (2*c))) (integrable_const (c^2))
  have hsub := integral_sub hQ2 (hQ.const_mul (2*c))
  simp only [Pi.add_apply,Pi.sub_apply] at hsum hsub
  rw [he,hsum,hsub,integral_const_mul]
  simp only [integral_const,probReal_univ,one_smul]

theorem centered_square_eq_mean_centered_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Q : Ω→ℝ}
    (hQ : Integrable Q μ) (hQ2 : Integrable (fun ω => (Q ω)^2) μ) (c : ℝ) :
    (∫ω,(Q ω-c)^2 ∂μ)=
      (∫ω,(Q ω-(∫z,Q z ∂μ))^2 ∂μ)+((∫z,Q z ∂μ)-c)^2 := by
  rw [centered_square_eq_moments μ hQ hQ2,
    centered_square_eq_moments μ hQ hQ2]
  ring

theorem centered_secondMoment_le_of_two_moments
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Q : Ω→ℝ} {C : Ξ→ℝ} (hQ : Integrable Q μ)
    (hQ2 : Integrable (fun ω => (Q ω)^2) μ) (hC : Integrable C ν)
    (hC2 : Integrable (fun ω => (C ω)^2) ν)
    {c e1 e2 : ℝ} (hc : |c|≤1)
    (h1 : |(∫ω,Q ω ∂μ)-(∫ω,C ω ∂ν)|≤e1)
    (h2 : |(∫ω,(Q ω)^2 ∂μ)-(∫ω,(C ω)^2 ∂ν)|≤e2) :
    (∫ω,(Q ω-c)^2 ∂μ)≤(∫ω,(C ω-c)^2 ∂ν)+e2+2*e1 := by
  have he1 : 0≤e1 := (abs_nonneg _).trans h1
  have hm : |2*c*((∫ω,Q ω ∂μ)-(∫ω,C ω ∂ν))|≤2*e1 := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ (2*1)*e1 := mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) h1
        (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hleft := neg_le_abs (2*c*((∫ω,Q ω ∂μ)-(∫ω,C ω ∂ν)))
  have hright := le_abs_self ((∫ω,(Q ω)^2 ∂μ)-(∫ω,(C ω)^2 ∂ν))
  rw [centered_square_eq_moments μ hQ hQ2,centered_square_eq_moments ν hC hC2]
  nlinarith only [hm,hleft,hright,h2]

end SphericalAging.TwoMomentL2Transfer
