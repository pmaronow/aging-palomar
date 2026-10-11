module

public import SphericalAging.LogBetaMoments
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

public section

/-! Exact logarithmic beta mean by differentiating the actual moment
 generating function, with the standard Gamma logarithmic derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SphericalAging.LogBetaMean
open LogBetaRenewal LogBetaMoments

/-- The real digamma function is the logarithmic derivative of Gamma. -/
@[expose] def gammaLogDerivative (x : ℝ) := deriv Real.Gamma x/Real.Gamma x

theorem zero_mem_interior_integrableExpSet {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    (0 : ℝ) ∈ interior (integrableExpSet id (law ρ a)) := by
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [Iio_mem_nhds hρ] with s hs
  exact exponential_integrable hρ ha hs

theorem beta_ratio_hasDerivAt_zero {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    HasDerivAt (fun s : ℝ => beta (ρ-s) a/beta ρ a)
      (gammaLogDerivative (ρ+a)-gammaLogDerivative ρ) 0 := by
  have hg1 : HasDerivAt Real.Gamma (deriv Real.Gamma ρ) ρ :=
    ((Real.differentiableOn_Gamma_Ioi ρ hρ).differentiableAt (Ioi_mem_nhds hρ)).hasDerivAt
  have hg2 : HasDerivAt Real.Gamma (deriv Real.Gamma (ρ+a)) (ρ+a) :=
    ((Real.differentiableOn_Gamma_Ioi (ρ+a) (add_pos hρ ha)).differentiableAt
      (Ioi_mem_nhds (add_pos hρ ha))).hasDerivAt
  have hd1 := hg1.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_sub ρ) (by simp)
  have hd2 := hg2.comp_of_eq 0 (((hasDerivAt_id (0 : ℝ)).const_sub ρ).add_const a) (by simp)
  have hGa := Real.Gamma_pos_of_pos ha
  have hGρ := Real.Gamma_pos_of_pos hρ
  have hGρa := Real.Gamma_pos_of_pos (add_pos hρ ha)
  have hratio := ((hd1.mul_const (Real.Gamma a)).div hd2 (by simpa using ne_of_gt hGρa)).div_const (beta ρ a)
  convert hratio using 1
  · funext s
    simp only [Function.comp_apply,beta,Pi.div_apply,id_eq]
  · dsimp only [gammaLogDerivative,beta,id_eq,sub_zero,neg_mul,one_mul,Function.comp_apply]
    field_simp [ne_of_gt hGρ,ne_of_gt hGρa,ne_of_gt hGa]
    ring

/-- The source mean formula, with psi expressed as the Gamma logarithmic derivative. -/
theorem mean_formula {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    (∫ y : ℝ,y ∂law ρ a)=gammaLogDerivative (ρ+a)-gammaLogDerivative ρ := by
  have hm := hasDerivAt_mgf (zero_mem_interior_integrableExpSet hρ ha)
  have he : mgf id (law ρ a) =ᶠ[nhds (0 : ℝ)] fun s => beta (ρ-s) a/beta ρ a := by
    filter_upwards [Iio_mem_nhds hρ] with s hs
    exact exponential_moment hρ ha hs
  have hm' : HasDerivAt (fun s : ℝ => beta (ρ-s) a/beta ρ a) (∫ y : ℝ,y ∂law ρ a) 0 := by
    convert hm.congr_of_eventuallyEq he.symm using 1
    simp only [id_eq,zero_mul,Real.exp_zero,mul_one]
  exact hm'.unique (beta_ratio_hasDerivAt_zero hρ ha)

/-- Compatibility with Mathlib's standard complex digamma on the positive real axis. -/
theorem gammaLogDerivative_eq_digamma_re {x : ℝ} (hx : 0 < x) :
    gammaLogDerivative x=(Complex.digamma (x : ℂ)).re := by
  have hc := Complex.differentiableAt_Gamma (x : ℂ) (fun n hn => by
    have hh : x=-(n : ℝ) := by exact_mod_cast hn
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith)
  have hr := hc.hasDerivAt.real_of_complex
  have he : deriv Real.Gamma x=(deriv Complex.Gamma (x : ℂ)).re := by
    simpa only [Complex.Gamma_ofReal,Complex.ofReal_re] using hr.deriv
  rw [Complex.digamma_def,logDeriv_apply,Complex.Gamma_ofReal,Complex.div_ofReal_re]
  exact congrArg (fun z : ℝ => z/Real.Gamma x) he

/-- The exact manuscript formula E Y=psi(rho+a)-psi(rho), using the
standard digamma function rather than an assumed special-function identity. -/
theorem mean_digamma_formula {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    (∫ y : ℝ,y ∂law ρ a)=
      (Complex.digamma ((ρ+a : ℝ) : ℂ)).re-(Complex.digamma (ρ : ℂ)).re := by
  rw [mean_formula hρ ha,gammaLogDerivative_eq_digamma_re (add_pos hρ ha),
    gammaLogDerivative_eq_digamma_re hρ]

end SphericalAging.LogBetaMean
