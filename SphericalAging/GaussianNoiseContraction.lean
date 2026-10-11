module

public import SphericalAging.GaussianNoiseOperator
public import Mathlib.Probability.Moments.Variance

public section

/-! The Gaussian noise operator contracts the true L2 norm. Pointwise
Jensen is derived from nonnegative actual variance, and stationarity from
the literal independent Gaussian mixture law. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianNoiseContraction
open Set MeasureTheory ProbabilityTheory GaussianNoiseSymmetry GaussianLinearMixtureLaw GaussianNoiseOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem operator_sq_le (ρ : ℝ) (f : E→ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀x,|f x|≤B) (x : E) :
    (operator ρ f x)^2≤operator ρ (fun z => (f z)^2) x := by
  have hm : Measurable (fun y : E => f (noise ρ x y)) := hf.comp
    ((mixture (E:=E) ρ (Real.sqrt (1-ρ^2))).measurable.comp (measurable_const.prodMk measurable_id))
  have hL : MemLp (fun y : E => f (noise ρ x y)) 2 (stdGaussian E) :=
    MemLp.of_bound hm.aestronglyMeasurable B
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs];exact hB _))
  have hh := variance_nonneg (fun y : E => f (noise ρ x y)) (stdGaussian E)
  rw [variance_eq_sub hL] at hh
  exact sub_nonneg.mp hh

theorem operator_L2_contraction (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1)
    (f : E→ℝ) (hf : Measurable f) (B : ℝ) (hB0 : 0≤B) (hB : ∀x,|f x|≤B) :
    (∫x,(operator ρ f x)^2 ∂stdGaussian E)≤∫x,(f x)^2 ∂stdGaussian E := by
  have hf2 : Measurable (fun x => (f x)^2) := hf.pow_const _
  have hb2 x : |(f x)^2|≤B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB0).mpr (hB x)
  have hbOp x : |(operator ρ f x)^2|≤B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hh := (sq_le_sq₀ (abs_nonneg _) hB0).mpr (operator_abs_bound ρ f hf B hB x)
    simpa only [sq_abs] using hh
  have hmOp := operator_measurable ρ f hf
  have hi := signed_bounded_integrable (stdGaussian E) _ (hmOp.pow_const 2) (B^2) hbOp
  have hi' := signed_bounded_integrable (stdGaussian E) _
    (operator_measurable ρ (fun x => (f x)^2) hf2) (B^2)
    (operator_abs_bound ρ _ hf2 (B^2) hb2)
  calc
    _≤∫x,operator ρ (fun z => (f z)^2) x ∂stdGaussian E :=
      integral_mono hi hi' (operator_sq_le ρ f hf B hB)
    _=_ := operator_stationary ρ h0 h1 _ hf2 (B^2) hb2

end SphericalAging.GaussianNoiseContraction
