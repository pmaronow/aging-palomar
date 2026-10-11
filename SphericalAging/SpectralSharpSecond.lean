module

public import SphericalAging.NonnegativeSpectralLaplace
public import Mathlib.MeasureTheory.Measure.Real

public section

/-! The sharp remote derivative envelope, including arbitrary plateau atoms. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.SpectralSharpSecond
open SpectralLaplace (laplaceMoment)
open NonnegativeSpectralLaplace

theorem damped_square_bound {L x : ℝ} (hL : 0<L) (hx : 0≤x) :
    x^2*Real.exp (-x*(2*L)) ≤ (Real.exp (-1)/L)^2 := by
  have he := Real.mul_exp_neg_le_exp_neg_one (L*x)
  have hb : x*Real.exp (-L*x)≤Real.exp (-1)/L := by
    apply (le_div_iff₀ hL).mpr
    rw [show -L*x=-(L*x) from by ring]
    simpa only [mul_assoc,mul_comm,mul_left_comm] using he
  have hp : 0≤x*Real.exp (-L*x) := by positivity
  have hs := (sq_le_sq₀ hp (by positivity : 0≤Real.exp (-1)/L)).mpr hb
  have hid : (x*Real.exp (-L*x))^2=x^2*Real.exp (-x*(2*L)) := by
    rw [mul_pow,pow_two (Real.exp _),←Real.exp_add]
    congr 1
    ring
  simpa only [hid] using hs

/-- The actual zero atom is removed by the integrand itself, yielding 1-q. -/
theorem laplaceMoment_second_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν,0≤x) {q L : ℝ} (hq : ν.real {0}=q) (hL : 0<L) :
    laplaceMoment ν 2 (2*L) ≤ (1-q)*(Real.exp (-1)/L)^2 := by
  let B := (Real.exp (-1)/L)^2
  have hi : Integrable (fun x : ℝ => x^2*Real.exp (-x*(2*L))) ν :=
    spectralMoment_integrable ν hν 2 (2*L) (by positivity)
  have hj : Integrable (({0} : Set ℝ)ᶜ.indicator (fun _ => B)) ν :=
    (integrable_const B).indicator (measurableSet_singleton 0).compl
  have hb : (fun x : ℝ => x^2*Real.exp (-x*(2*L))) ≤ᵐ[ν]
      (({0} : Set ℝ)ᶜ.indicator (fun _ => B)) := by
    filter_upwards [hν] with x hx
    by_cases hx0 : x=0
    · subst x
      simp
    · rw [indicator_of_mem (by simpa using hx0)]
      exact damped_square_bound hL hx
  have hs : ν.real ({0} : Set ℝ)ᶜ=1-q := by
    rw [measureReal_compl (measurableSet_singleton 0),probReal_univ,hq]
  have he := integral_mono_ae hi hj hb
  rw [integral_indicator_const B (measurableSet_singleton 0).compl,hs] at he
  simpa only [laplaceMoment,smul_eq_mul] using he

theorem sqrt_second_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν,0≤x) {q L : ℝ} (hq : ν.real {0}=q) (hL : 0<L) :
    Real.sqrt (laplaceMoment ν 2 (2*L)) ≤ Real.sqrt (1-q)/(Real.exp 1*L) := by
  have hqn : 0≤1-q := by
    have hs : ν.real ({0} : Set ℝ)ᶜ=1-q := by
      rw [measureReal_compl (measurableSet_singleton 0),probReal_univ,hq]
    rw [←hs]
    exact measureReal_nonneg
  have he := Real.sqrt_le_sqrt (laplaceMoment_second_bound ν hν hq hL)
  rw [Real.sqrt_mul hqn,Real.sqrt_sq (by positivity : 0≤Real.exp (-1)/L)] at he
  convert he using 1
  rw [Real.exp_neg,div_eq_mul_inv]
  field_simp

end SphericalAging.SpectralSharpSecond
