module

public import SphericalAging.ResponseTraceReplacement

public section

/-! Quantitative replacement of two correlated powers in a signed
response memory by their means. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SphericalAging.MixedResponseTraceReplacement
open ResponseTraceReplacement
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma product_power_difference_abs_le (n m : ℕ) {a b c d r : ℝ}
    (ha : |a|≤1) (hb : |b|≤1) (hc : |c|≤1) (hd : |d|≤1) :
    |(a^n*c^m-b^n*d^m)*r|≤|(a^n-b^n)*r|+|(c^m-d^m)*r| := by
  have he : (a^n*c^m-b^n*d^m)*r=(a^n-b^n)*r*c^m+b^n*((c^m-d^m)*r) := by ring
  rw [he]
  calc
    _≤|(a^n-b^n)*r*c^m|+|b^n*((c^m-d^m)*r)| := abs_add_le _ _
    _≤|(a^n-b^n)*r|+|(c^m-d^m)*r| := by
      rw [abs_mul _ (c^m),abs_pow,abs_mul (b^n),abs_pow]
      exact add_le_add
        (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hc))
        (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hb))

theorem weighted_product_trace_replacement {a c r : Ω → ℝ} {b d C : ℝ} (n m : ℕ)
    (ha : AEStronglyMeasurable a P) (hc : AEStronglyMeasurable c P)
    (hab : ∀ᵐ ω ∂P,|a ω|≤1) (hcd : ∀ᵐ ω ∂P,|c ω|≤1)
    (hb : |b|≤1) (hd : |d|≤1) (hr : MemLp r 4 P)
    (hC : (∫ ω,|r ω|^4 ∂P)≤C) :
    Integrable (fun ω => |((a ω)^n*(c ω)^m-b^n*d^m)*r ω|) P ∧
    (∫ ω,|((a ω)^n*(c ω)^m-b^n*d^m)*r ω| ∂P)≤
      ((n : ℝ)*Real.sqrt (∫ ω,(a ω-b)^2 ∂P)+
        (m : ℝ)*Real.sqrt (∫ ω,(c ω-d)^2 ∂P))*Real.sqrt (1+C) := by
  have h₁ := weighted_trace_replacement n ha hab hb hr hC
  have h₂ := weighted_trace_replacement m hc hcd hd hr hC
  have hmeas := ((((ha.pow n).mul (hc.pow m)).sub (aestronglyMeasurable_const (b := b^n*d^m))).mul
    hr.aestronglyMeasurable).norm
  have hbound : ∀ᵐ ω ∂P,|((a ω)^n*(c ω)^m-b^n*d^m)*r ω|≤
      |((a ω)^n-b^n)*r ω|+|((c ω)^m-d^m)*r ω| := by
    filter_upwards [hab,hcd] with ω haw hcw
    exact product_power_difference_abs_le n m haw hb hcw hd
  have hi : Integrable (fun ω => |((a ω)^n*(c ω)^m-b^n*d^m)*r ω|) P :=
    (h₁.1.add h₂.1).mono' (by simpa only [Real.norm_eq_abs,Pi.mul_apply,Pi.pow_apply,Pi.sub_apply] using hmeas)
      (hbound.mono (fun ω hw => by simpa only [Real.norm_eq_abs,abs_abs,Pi.add_apply] using hw))
  refine ⟨hi,?_⟩
  calc
    _≤∫ ω,|((a ω)^n-b^n)*r ω|+|((c ω)^m-d^m)*r ω| ∂P :=
      integral_mono_ae hi (h₁.1.add h₂.1) hbound
    _=(∫ ω,|((a ω)^n-b^n)*r ω| ∂P)+(∫ ω,|((c ω)^m-d^m)*r ω| ∂P) :=
      integral_add h₁.1 h₂.1
    _≤(n : ℝ)*Real.sqrt (∫ ω,(a ω-b)^2 ∂P)*Real.sqrt (1+C)+
        (m : ℝ)*Real.sqrt (∫ ω,(c ω-d)^2 ∂P)*Real.sqrt (1+C) := add_le_add h₁.2 h₂.2
    _=_ := by ring

end SphericalAging.MixedResponseTraceReplacement
