module

public import SphericalAging.GaussianNoiseSymmetry
public import SphericalAging.ConditionalCloneSuccessJensen

public section

/-! The actual Gaussian noise averaging operator and its stationary
integral, constructed from independent standard Gaussian input noise. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianNoiseOperator
open Set MeasureTheory ProbabilityTheory GaussianNoiseSymmetry GaussianLinearMixtureLaw
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def operator (ρ : ℝ) (f : E→ℝ) (x : E) : ℝ := ∫y,f (noise ρ x y) ∂stdGaussian E

theorem signed_bounded_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀x,|f x|≤B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs];exact hB x))

theorem operator_measurable (ρ : ℝ) (f : E→ℝ) (hf : Measurable f) :
    Measurable (operator ρ f) := by
  have hm : Measurable (fun z : E×E => f (noise ρ z.1 z.2)) :=
    hf.comp (mixture (E:=E) ρ (Real.sqrt (1-ρ^2))).measurable
  exact hm.stronglyMeasurable.integral_prod_right' (ν:=stdGaussian E) |>.measurable

theorem operator_abs_bound (ρ : ℝ) (f : E→ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀x,|f x|≤B) (x : E) : |operator ρ f x|≤B := by
  have hm : Measurable (fun y : E => f (noise ρ x y)) := hf.comp
    ((mixture (E:=E) ρ (Real.sqrt (1-ρ^2))).measurable.comp (measurable_const.prodMk measurable_id))
  have hi := signed_bounded_integrable (stdGaussian E) _ hm B (fun y => hB _)
  unfold operator
  calc
    _≤∫y,|f (noise ρ x y)| ∂stdGaussian E := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun y : E => f (noise ρ x y))
    _≤∫_y,B ∂stdGaussian E := integral_mono hi.norm (integrable_const _) (fun y => hB _)
    _=B := by simp

theorem operator_stationary (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1)
    (f : E→ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀x,|f x|≤B) :
    (∫x,operator ρ f x ∂stdGaussian E)=∫x,f x ∂stdGaussian E := by
  have hmp := mixture_sqrt_measurePreserving (E:=E) ρ h0 h1
  have hm : Measurable (fun z : E×E => f (noise ρ z.1 z.2)) := hf.comp hmp.measurable
  have hi := signed_bounded_integrable ((stdGaussian E).prod (stdGaussian E)) _ hm B (fun z => hB _)
  change (∫x,∫y,f (noise ρ x y) ∂stdGaussian E ∂stdGaussian E)=_
  rw [←integral_prod _ hi]
  exact hmp.hasLaw.integral_comp hf.aestronglyMeasurable

end SphericalAging.GaussianNoiseOperator
