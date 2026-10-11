module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

public section

/-! Exact laws of linear mixtures of independent standard Gaussian vectors.
The law is derived from characteristic functions; no Gaussian conclusion is
assumed. Coefficients may have either sign and the zero-variance case is included. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianLinearMixtureLaw
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def scale (a : ℝ) : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E

@[expose] def mixture (a b : ℝ) : E×E →L[ℝ] E :=
  a • ContinuousLinearMap.fst ℝ E E + b • ContinuousLinearMap.snd ℝ E E

@[simp] theorem scale_apply (a : ℝ) (x : E) : scale a x=a•x := rfl
@[simp] theorem mixture_apply (a b : ℝ) (x : E×E) : mixture a b x=a•x.1+b•x.2 := rfl

theorem dual_comp_scale (a : ℝ) (L : StrongDual ℝ E) : L.comp (scale a)=a•L := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,scale_apply,map_smul,
    ContinuousLinearMap.smul_apply]

theorem dual_comp_mixture_inl (a b : ℝ) (L : StrongDual ℝ E) :
    (L.comp (mixture a b)).comp (ContinuousLinearMap.inl ℝ E E)=a•L := by
  ext x
  simp

theorem dual_comp_mixture_inr (a b : ℝ) (L : StrongDual ℝ E) :
    (L.comp (mixture a b)).comp (ContinuousLinearMap.inr ℝ E E)=b•L := by
  ext x
  simp

theorem dual_scaled_norm_sq (a : ℝ) (L : StrongDual ℝ E) :
    ‖a•L‖^2=a^2*‖L‖^2 := by
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

/-- The true variance of the mixture is the sum of the two squared coefficients. -/
theorem mixture_map_eq_scaled (a b c : ℝ) (h : a^2+b^2=c^2) :
    ((stdGaussian E).prod (stdGaussian E)).map (mixture a b)=
      (stdGaussian E).map (scale c) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map,charFunDual_prod,dual_comp_mixture_inl,
    dual_comp_mixture_inr,charFunDual_stdGaussian,charFunDual_stdGaussian,
    charFunDual_map,dual_comp_scale,charFunDual_stdGaussian,←Complex.exp_add]
  congr 1
  norm_cast
  rw [dual_scaled_norm_sq,dual_scaled_norm_sq,dual_scaled_norm_sq,←h]
  ring

/-- Every unit linear combination of two independent standard Gaussians is standard. -/
theorem mixture_map_eq_stdGaussian (a b : ℝ) (h : a^2+b^2=1) :
    ((stdGaussian E).prod (stdGaussian E)).map (mixture a b)=stdGaussian E := by
  have hh := mixture_map_eq_scaled (E:=E) a b 1 (by simpa using h)
  simpa [scale,Measure.map_id] using hh

theorem mixture_measurePreserving (a b : ℝ) (h : a^2+b^2=1) :
    MeasurePreserving (fun x : E×E => a•x.1+b•x.2)
      ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) := by
  change MeasurePreserving (mixture (E:=E) a b) _ _
  exact ⟨(mixture (E:=E) a b).measurable,mixture_map_eq_stdGaussian a b h⟩

theorem mixture_sqrt_measurePreserving (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1) :
    MeasurePreserving (fun x : E×E => ρ•x.1+Real.sqrt (1-ρ^2)•x.2)
      ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) := by
  apply mixture_measurePreserving
  rw [Real.sq_sqrt (by nlinarith)]
  ring

end SphericalAging.GaussianLinearMixtureLaw
