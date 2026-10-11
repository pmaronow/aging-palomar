module

public import SphericalAging.GammaRatioDensity
public import SphericalAging.DirichletLogChange
public import Mathlib.Probability.Moments.Variance

public section

/-! Actual gamma smoothing variance and its Dirichlet energy control. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SphericalAging.GammaSmoothingVariance

@[expose] def gammaAverage (b : ℝ) (D : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ g,D (x+Real.log g) ∂gammaMeasure b 1

@[expose] def gammaVariance (b : ℝ) (D : ℝ → ℝ) (x : ℝ) : ℝ :=
  gammaAverage b (fun y => (D y)^2) x-(gammaAverage b D x)^2

theorem gamma_ae_positive (b : ℝ) : ∀ᵐ g ∂gammaMeasure b 1,0<g := by
  rw [ae_iff]
  simp only [not_lt]
  change gammaMeasure b 1 (Iic 0)=0
  rw [gammaMeasure,withDensity_apply _ measurableSet_Iic]
  rw [←restrict_Iio_eq_restrict_Iic]
  exact lintegral_gammaPDF_of_nonpos (le_refl 0)

theorem gammaAverage_memLp {b : ℝ} (hb : 0<b) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M) (x : ℝ) :
    MemLp (fun g => D (x+Real.log g)) 2 (gammaMeasure b 1) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  exact MemLp.of_bound (hD.comp (measurable_const.add Real.measurable_log)).aestronglyMeasurable
    M (Eventually.of_forall (fun g => hM (x+Real.log g)))

theorem gammaVariance_eq_variance {b : ℝ} (hb : 0<b) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M) (x : ℝ) :
    gammaVariance b D x=variance (fun g => D (x+Real.log g)) (gammaMeasure b 1) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  exact (variance_eq_sub (gammaAverage_memLp hb hD hM x)).symm

theorem gammaVariance_nonnegative {b : ℝ} (hb : 0<b) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M) (x : ℝ) :
    0≤gammaVariance b D x := by
  rw [gammaVariance_eq_variance hb hD hM]
  exact variance_nonneg _ _

theorem pair_variance_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {F : ℝ → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀y,‖F y‖≤M) :
    variance F μ=(1/2:ℝ)*(∫ q : ℝ×ℝ,(F q.1-F q.2)^2 ∂μ.prod μ) := by
  have hp : MemLp F 2 μ :=
    MemLp.of_bound hF.aestronglyMeasurable M (Eventually.of_forall hM)
  have hx := hp.comp_measurePreserving (measurePreserving_fst (μ:=μ) (ν:=μ))
  have hy := hp.comp_measurePreserving (measurePreserving_snd (μ:=μ) (ν:=μ))
  change MemLp (fun q : ℝ×ℝ => F q.1) 2 (μ.prod μ) at hx
  change MemLp (fun q : ℝ×ℝ => F q.2) 2 (μ.prod μ) at hy
  have hmean : (∫ q : ℝ×ℝ,F q.1-F q.2 ∂μ.prod μ)=0 := by
    rw [integral_sub (hx.integrable one_le_two) (hy.integrable one_le_two),
      integral_fun_fst,integral_fun_snd]
    simp
  have hv := variance_of_integral_eq_zero ((hF.comp measurable_fst).sub
    (hF.comp measurable_snd)).aemeasurable hmean
  change variance (fun q : ℝ×ℝ => F q.1-F q.2) (μ.prod μ)=
    (∫q : ℝ×ℝ,(F q.1-F q.2)^2 ∂μ.prod μ) at hv
  have hvar := variance_fun_sub hx hy
  rw [(indepFun_prod hF hF).covariance_eq_zero hx hy,
    (measurePreserving_fst (μ:=μ) (ν:=μ)).variance_fun_comp hF.aemeasurable,
    (measurePreserving_snd (μ:=μ) (ν:=μ)).variance_fun_comp hF.aemeasurable] at hvar
  rw [hv] at hvar
  linarith

theorem gammaVariance_pair {b : ℝ} (hb : 0<b) {D : ℝ → ℝ}
    (hD : Measurable D) {M : ℝ} (hM : ∀y,‖D y‖≤M) (x : ℝ) :
    gammaVariance b D x=(1/2:ℝ)*(∫ q : ℝ×ℝ,
      (D (x+Real.log q.1)-D (x+Real.log q.2))^2
      ∂(gammaMeasure b 1).prod (gammaMeasure b 1)) := by
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  rw [gammaVariance_eq_variance hb hD hM]
  exact pair_variance_identity (gammaMeasure b 1)
    (hD.comp (measurable_const.add Real.measurable_log))
    (fun g => hM (x+Real.log g))

end SphericalAging.GammaSmoothingVariance
