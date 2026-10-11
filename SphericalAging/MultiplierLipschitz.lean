module

public import SphericalAging.MultiplierDerivative
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

public section

/-! Scalar uniform multiplier/energy Lipschitz consequences of the two
local Hilbert moment estimates. The final moment estimates are proved in
separate Hilbert modules. No Lipschitz or derivative bound is assumed. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace SphericalAging.MultiplierLipschitz
open CKSpecification MultiplierDerivative CKPhysicalConsequences UniformMultiplier
open GreenCovariance BackwardResponse

@[expose] def multiplierSlope (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ :=
  β^2*(p : ℝ)^2*(1-(p : ℝ)*d.multiplier t*memoryMass p d t+
    β^2*(p : ℝ)*((p : ℝ)-1)^2*mixedMoment p d t+
    2*β^2*(p : ℝ)*((p : ℝ)-1)*nestedMoment p d t)

@[expose] def regularityCeiling (p : ℕ) (β : ℝ) : ℝ :=
  β^2*(p : ℝ)^4+(p : ℝ)*(multiplierCeiling p β)^2

theorem mixedMoment_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ mixedMoment p d t := by
  unfold mixedMoment
  apply intervalIntegral.integral_nonneg ht
  intro u _
  apply intervalIntegral.integral_nonneg ht
  intro v _
  have hb := physical_bounds_of_equations h
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (clampedResponse_nonnegative hb t u) (clampedResponse_nonnegative hb t v))
    (pow_nonneg (clampedCorrelation_nonnegative hb t u) _))
    (pow_nonneg (clampedCorrelation_nonnegative hb t v) _))
    (clampedCorrelation_nonnegative hb u v)

theorem nestedMoment_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ nestedMoment p d t := by
  unfold nestedMoment lowerWeight powerWeight
  have hb := physical_bounds_of_equations h
  apply intervalIntegral.integral_nonneg ht
  intro u hu
  apply mul_nonneg
  · exact mul_nonneg (clampedResponse_nonnegative hb t u)
      (pow_nonneg (clampedCorrelation_nonnegative hb t u) _)
  · apply intervalIntegral.integral_nonneg hu.1
    intro v _
    exact mul_nonneg (pow_nonneg (clampedCorrelation_nonnegative hb t v) _)
      (clampedResponse_nonnegative hb u v)

theorem multiplierSlope_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt d.multiplier (multiplierSlope p β d t) t :=
  multiplier_two_moment_hasDerivAt h ht

/-- The upper derivative bound is β²p⁴ after the two actual memory
moments have been bounded by the colored-feature contraction. -/
theorem multiplierSlope_upper_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t)
    (hA : β^2*(p : ℝ)*mixedMoment p d t ≤ 1)
    (hB : β^2*(p : ℝ)*nestedMoment p d t ≤ 1) :
    multiplierSlope p β d t ≤ β^2*(p : ℝ)^4 := by
  have hlam := multiplier_uniform_bound h (physical_bounds_of_equations h)
    (correlation_psd_of_equations h) ht
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by have hp := h.spin_ge_three; omega)
  have hM : 0 ≤ memoryMass p d t := by
    unfold memoryMass
    apply intervalIntegral.integral_nonneg ht
    intro u hu
    exact mul_nonneg (pow_nonneg ((physical_bounds_of_equations h).1 t u ht hu.1).1 _)
      ((physical_bounds_of_equations h).2 t u hu.1 hu.2)
  have hAa := mul_le_mul_of_nonneg_right hA (sq_nonneg ((p : ℝ)-1))
  have hBb := mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ 2*((p : ℝ)-1))
  have hlam0 : 0 ≤ d.multiplier t := le_trans zero_le_one hlam.1
  have hneg : 0 ≤ (p : ℝ)*d.multiplier t*memoryMass p d t := by positivity
  have hbracket : 1-(p : ℝ)*d.multiplier t*memoryMass p d t+
      β^2*(p : ℝ)*((p : ℝ)-1)^2*mixedMoment p d t+
      2*β^2*(p : ℝ)*((p : ℝ)-1)*nestedMoment p d t ≤ (p : ℝ)^2 := by
    nlinarith only [hAa,hBb,hneg]
  have hh := mul_le_mul_of_nonneg_left hbracket
    (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ)))
  unfold multiplierSlope
  nlinarith only [hh]

/-- Nonnegativity and the sharp λ ceiling bound its negative derivative. -/
theorem multiplierSlope_lower_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    -(p : ℝ)*(multiplierCeiling p β)^2 ≤ multiplierSlope p β d t := by
  have hlam := multiplier_uniform_bound h (physical_bounds_of_equations h)
    (correlation_psd_of_equations h) ht
  have hL : 0 ≤ multiplierCeiling p β := by linarith [hlam.1,hlam.2]
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by have hp := h.spin_ge_three; omega)
  have hA := mixedMoment_nonnegative h ht
  have hB := nestedMoment_nonnegative h ht
  have hM := h.multiplier_eq t ht
  have hprod : d.multiplier t*(d.multiplier t-1) ≤ (multiplierCeiling p β)^2 := by
    have hh := mul_le_mul hlam.2 (by linarith [hlam.2] : d.multiplier t-1 ≤ multiplierCeiling p β)
      (by linarith [hlam.1] : 0 ≤ d.multiplier t-1) hL
    nlinarith only [hh]
  have hn := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg p)
  have hiA : 0 ≤ β^2*(p : ℝ)*((p : ℝ)-1)^2*mixedMoment p d t := by positivity
  have hiB : 0 ≤ 2*β^2*(p : ℝ)*((p : ℝ)-1)*nestedMoment p d t := by positivity
  have hi := mul_nonneg (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ)))
    (add_nonneg (add_nonneg (by norm_num : 0 ≤ (1 : ℝ)) hiA) hiB)
  have he : multiplierSlope p β d t=
      -(p : ℝ)*d.multiplier t*(d.multiplier t-1)+β^2*(p : ℝ)^2*
        (1+β^2*(p : ℝ)*((p : ℝ)-1)^2*mixedMoment p d t+
          2*β^2*(p : ℝ)*((p : ℝ)-1)*nestedMoment p d t) := by
    unfold multiplierSlope
    rw [hM]
    ring
  rw [he]
  nlinarith only [hn,hi]

theorem multiplierSlope_abs_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t)
    (hA : β^2*(p : ℝ)*mixedMoment p d t ≤ 1)
    (hB : β^2*(p : ℝ)*nestedMoment p d t ≤ 1) :
    |multiplierSlope p β d t| ≤ regularityCeiling p β := by
  have hu := multiplierSlope_upper_bound h ht hA hB
  have hl := multiplierSlope_lower_bound h ht
  have hpos : 0 ≤ β^2*(p : ℝ)^4 := mul_nonneg (sq_nonneg β) (pow_nonneg (Nat.cast_nonneg p) 4)
  have hLamSq : 0 ≤ (p : ℝ)*(multiplierCeiling p β)^2 := mul_nonneg (Nat.cast_nonneg p) (sq_nonneg _)
  unfold regularityCeiling
  apply abs_le.mpr
  constructor <;> linarith only [hu,hl,hpos,hLamSq]

/-- Genuine MVT gives the scalar uniform Lipschitz conclusion from local
Hilbert moment bounds; no λ regularity is an input. -/
theorem multiplier_lipschitz_of_moment_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (hA : ∀ t : ℝ, 0 < t → β^2*(p : ℝ)*mixedMoment p d t ≤ 1)
    (hB : ∀ t : ℝ, 0 < t → β^2*(p : ℝ)*nestedMoment p d t ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |d.multiplier b-d.multiplier a| ≤ regularityCeiling p β*|b-a| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm (d.multiplier b) (d.multiplier a),abs_sub_comm b a]
    exact this hb ha (le_of_not_ge hab)
  rcases lt_or_eq_of_le hab with hab | rfl
  · have hc : ContinuousOn d.multiplier (Icc a b) := h.multiplier_continuous.mono
      (fun x hx => ha.trans hx.1)
    obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope d.multiplier (multiplierSlope p β d) hab hc
      (fun x hx => multiplierSlope_hasDerivAt h (lt_of_le_of_lt ha hx.1))
    have ht := lt_of_le_of_lt ha hx.1
    have hh := multiplierSlope_abs_bound h ht.le (hA x ht) (hB x ht)
    rw [he,abs_div,abs_of_nonneg (sub_nonneg.mpr hab.le)] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hab.le)]
    exact (div_le_iff₀ (sub_pos.mpr hab)).mp hh
  · simp

theorem energy_lipschitz_of_moment_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (hA : ∀ t : ℝ, 0 < t → β^2*(p : ℝ)*mixedMoment p d t ≤ 1)
    (hB : ∀ t : ℝ, 0 < t → β^2*(p : ℝ)*nestedMoment p d t ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |energy p β d b-energy p β d a| ≤
      (regularityCeiling p β/((p : ℝ)*β))*|b-a| := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have hh := h.spin_ge_three; omega)
  have hc := mul_pos hp h.beta_pos
  have hh := multiplier_lipschitz_of_moment_bounds h hA hB ha hb
  have he : d.multiplier b-d.multiplier a=(p : ℝ)*β*(energy p β d b-energy p β d a) := by
    rw [multiplier_energy_identity h b hb,multiplier_energy_identity h a ha]
    ring
  rw [he,abs_mul,abs_of_nonneg hc.le] at hh
  calc
    _ = ((p : ℝ)*β*|energy p β d b-energy p β d a|)/((p : ℝ)*β) := by field_simp [ne_of_gt hp,ne_of_gt h.beta_pos]
    _ ≤ (regularityCeiling p β*|b-a|)/((p : ℝ)*β) := div_le_div_of_nonneg_right hh hc.le
    _ = _ := by ring

end SphericalAging.MultiplierLipschitz
