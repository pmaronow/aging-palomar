module

public import SphericalAging.StationaryBetaGammaAverage
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual regularity and limits of probability averages of translates. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SphericalAging.StationaryAveragingRegularity
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GammaSmoothingVariance StationaryBetaGammaAverage

@[expose] def translatedAverage (μ : Measure ℝ) (φ D : ℝ → ℝ) (x : ℝ) := ∫ s,D (x+φ s) ∂μ

theorem translatedAverage_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ D : ℝ → ℝ) (hφ : Measurable φ) (hD : Measurable D) (M : ℝ)
    (hM : ∀ y,‖D y‖≤M) (x : ℝ) : Integrable (fun s => D (x+φ s)) μ := by
  exact (MemLp.of_bound (hD.comp (measurable_const.add hφ)).aestronglyMeasurable M
    (Eventually.of_forall (fun s => hM (x+φ s))) : MemLp (fun s => D (x+φ s)) 1 μ).integrable le_rfl

theorem translatedAverage_measurable (μ : Measure ℝ) [SFinite μ]
    (φ D : ℝ → ℝ) (hφ : Measurable φ) (hD : Measurable D) :
    Measurable (translatedAverage μ φ D) := by
  have hm : Measurable (fun q : ℝ×ℝ => D (q.1+φ q.2)) :=
    hD.comp (measurable_fst.add (hφ.comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem translatedAverage_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ D : ℝ → ℝ) (M : ℝ) (hM : ∀ y,‖D y‖≤M) (x : ℝ) :
    ‖translatedAverage μ φ D x‖≤M := by
  simpa only [translatedAverage,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall (fun s => hM (x+φ s))))

/-- Translation averaging preserves the actual Lipschitz constant. -/
theorem translatedAverage_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ D : ℝ → ℝ) (hφ : Measurable φ) (L : ℝ≥0) (hD : LipschitzWith L D)
    (M : ℝ) (hM : ∀ y,‖D y‖≤M) : LipschitzWith L (translatedAverage μ φ D) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := translatedAverage_integrable μ φ D hφ hD.continuous.measurable M hM x
  have hy := translatedAverage_integrable μ φ D hφ hD.continuous.measurable M hM y
  have hb : ∀ᵐ s ∂μ,‖D (x+φ s)-D (y+φ s)‖≤(L:ℝ)*dist x y := by
    apply Eventually.of_forall
    intro s
    simpa only [Real.dist_eq,show x+φ s-(y+φ s)=x-y by ring,Real.norm_eq_abs] using
      hD.dist_le_mul (x+φ s) (y+φ s)
  have he := norm_integral_le_of_norm_le_const hb
  change dist (∫ s,D (x+φ s) ∂μ) (∫ s,D (y+φ s) ∂μ)≤(L:ℝ)*dist x y
  rw [dist_eq_norm,←integral_sub hx hy]
  simpa only [translatedAverage,probReal_univ,mul_one] using he

/-- The negative-time limit is preserved by genuine dominated convergence. -/
theorem translatedAverage_tendsto_atBot (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ D : ℝ → ℝ) (hφ : Measurable φ) (hD : Measurable D) (M : ℝ)
    (hM : ∀ y,‖D y‖≤M) (hBot : Tendsto D atBot (𝓝 0)) :
    Tendsto (translatedAverage μ φ D) atBot (𝓝 0) := by
  have he := tendsto_integral_filter_of_dominated_convergence (μ:=μ) (F:=fun x s : ℝ => D (x+φ s))
    (f:=fun _ : ℝ => (0:ℝ)) (bound:=fun _ => M)
    (Eventually.of_forall (fun x => (hD.comp (measurable_const.add hφ)).aestronglyMeasurable))
    (Eventually.of_forall (fun _ => Eventually.of_forall (fun s => hM _)))
    (integrable_const M) (Eventually.of_forall (fun s =>
      hBot.comp (tendsto_atBot_add_const_right atBot (φ s) tendsto_id)))
  change Tendsto (fun x : ℝ => ∫ s,D (x+φ s) ∂μ) atBot (𝓝 0)
  simpa only [integral_zero] using he

/-- If the actual fixed increments vanish, probability smoothing differs
from the original bounded function by a quantity tending to zero. -/
theorem translatedAverage_sub_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ D : ℝ → ℝ) (hφ : Measurable φ) (hD : Measurable D) (M : ℝ)
    (hM : ∀ y,‖D y‖≤M)
    (hInc : ∀ s : ℝ,Tendsto (fun x : ℝ => D (x+s)-D x) atTop (𝓝 0)) :
    Tendsto (fun x => translatedAverage μ φ D x-D x) atTop (𝓝 0) := by
  have he := tendsto_integral_filter_of_dominated_convergence (μ:=μ)
    (F:=fun x s : ℝ => D (x+φ s)-D x) (f:=fun _ : ℝ => (0:ℝ)) (bound:=fun _ => 2*M)
    (Eventually.of_forall (fun x => ((hD.comp (measurable_const.add hφ)).aestronglyMeasurable).sub
      aestronglyMeasurable_const))
    (Eventually.of_forall (fun x => Eventually.of_forall (fun s => by
      exact (norm_sub_le _ _).trans (by linarith [hM (x+φ s),hM x]))))
    (integrable_const (2*M)) (Eventually.of_forall (fun s => hInc (φ s)))
  simp only [integral_zero] at he
  convert he using 1
  funext x
  rw [integral_sub (translatedAverage_integrable μ φ D hφ hD M hM x) (integrable_const _),
    integral_const,probReal_univ,one_smul]
  rfl

/-- A globally bounded Lipschitz function has a genuinely Lipschitz square. -/
theorem bounded_square_lipschitz (D : ℝ → ℝ) (L : ℝ≥0) (hD : LipschitzWith L D)
    (M : ℝ≥0) (hM : ∀ y,‖D y‖≤(M:ℝ)) :
    LipschitzWith (2*M*L) (fun x => D x^2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hs : |D x+D y|≤2*(M:ℝ) := (abs_add_le _ _).trans (by have hh := add_le_add (hM x) (hM y); simp only [Real.norm_eq_abs] at hh; linarith)
  have hd := hD.dist_le_mul x y
  change |D x^2-D y^2|≤(↑(2*M*L):ℝ)*|x-y|
  rw [show D x^2-D y^2=(D x-D y)*(D x+D y) by ring,abs_mul]
  have he := mul_le_mul (show |D x-D y|≤(L:ℝ)*|x-y| from hd) hs (abs_nonneg _) (by positivity)
  simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using he.trans_eq (by ring)

/-- Actual squared fixed increments also vanish under a global bound. -/
theorem bounded_square_increment_tendsto (D : ℝ → ℝ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀ y,‖D y‖≤M) (s : ℝ)
    (hInc : Tendsto (fun x : ℝ => D (x+s)-D x) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => D (x+s)^2-D x^2) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a:=fun x => (2*M)*|D (x+s)-D x|)
  · intro x
    rw [Real.norm_eq_abs,show D (x+s)^2-D x^2=(D (x+s)-D x)*(D (x+s)+D x) by ring,abs_mul]
    have hb : |D (x+s)+D x|≤2*M := (abs_add_le _ _).trans (by have hh := add_le_add (hM (x+s)) (hM x); simp only [Real.norm_eq_abs] at hh; linarith)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg (D (x+s)-D x))
  · simpa only [abs_zero,mul_zero] using hInc.abs.const_mul (2*M)

end
end SphericalAging.StationaryAveragingRegularity
