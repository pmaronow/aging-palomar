module

public import SphericalAging.LogBetaRenewal
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.Moments.IntegrableExpMul

public section

/-! Genuine density law and moments of Y=-log B for B~Beta(rho,a).
All identities are derived from the actual beta law and change of variables. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace SphericalAging.LogBetaMoments
open LogBetaRenewal

theorem density_integrable {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    Integrable (density ρ a) := by
  unfold density
  have hi := (integrable_comp_exp (betaPDFReal ρ a)).mpr
    ((betaPDFReal_integrable hρ ha).integrableOn (s := Ioi 0))
  have hn := hi.comp_mul_left' (R := -1) (by norm_num)
  simpa only [neg_one_mul,smul_eq_mul] using hn

/-- The change of variables is proved for every measurable test function. -/
theorem integral_law {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ y,f y ∂law ρ a=∫ y,density ρ a y*f y := by
  unfold law
  rw [integral_map_of_stronglyMeasurable (φ := fun b : ℝ => -Real.log b)
    Real.measurable_log.neg hf.stronglyMeasurable]
  unfold betaMeasure betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_betaPDFReal ρ a).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (betaPDFReal_nonnegative hρ ha _),smul_eq_mul]
  have hrestrict : (∫ b in Ioi (0 : ℝ),betaPDFReal ρ a b*f (-Real.log b))=
      ∫ b,betaPDFReal ρ a b*f (-Real.log b) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro b hb
    simp only [mem_Ioi,not_lt] at hb
    simp [betaPDFReal,not_lt.mpr hb]
  rw [←hrestrict,←integral_comp_exp]
  simp only [Real.log_exp,smul_eq_mul]
  rw [←integral_neg_eq_self (fun x : ℝ =>
    Real.exp x*(betaPDFReal ρ a (Real.exp x)*f (-x)))]
  simp only [neg_neg,density,mul_assoc]

/-- The logarithmic beta pushforward really has the manuscript's density. -/
theorem law_eq_withDensity {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    law ρ a=volume.withDensity (fun y => ENNReal.ofReal (density ρ a y)) := by
  let := law_probability hρ ha
  let := isFiniteMeasure_withDensity_ofReal (density_integrable hρ ha).2
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_law hρ ha f.continuous.measurable,
    integral_withDensity_eq_integral_toReal_smul (density_measurable ρ a).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (density_nonnegative hρ ha _),smul_eq_mul]

/-- Exact exponential tilting changes only the first beta parameter. -/
theorem density_tilt {ρ a s : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hs : s < ρ) (y : ℝ) :
    Real.exp (s*y)*density ρ a y=(beta (ρ-s) a/beta ρ a)*density (ρ-s) a y := by
  by_cases hy : 0 < y
  · rw [density_formula hy,density_formula hy]
    have he : Real.exp (s*y)*Real.exp (-ρ*y)=Real.exp (-(ρ-s)*y) := by
      rw [←Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (s*y)*Real.exp (-ρ*y))*(1-Real.exp (-y))^(a-1)/beta ρ a := by ring
      _ = Real.exp (-(ρ-s)*y)*(1-Real.exp (-y))^(a-1)/beta ρ a := by rw [he]
      _ = _ := by
        field_simp [ne_of_gt (beta_pos hρ ha),ne_of_gt (beta_pos (sub_pos.mpr hs) ha)]
  · rw [density_zero_of_nonpositive (le_of_not_gt hy),density_zero_of_nonpositive (le_of_not_gt hy)]
    ring

theorem exponential_integrable {ρ a s : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hs : s < ρ) :
    Integrable (fun y : ℝ => Real.exp (s*y)) (law ρ a) := by
  rw [law_eq_withDensity hρ ha,integrable_withDensity_iff_integrable_smul'
    (density_measurable ρ a).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (density_nonnegative hρ ha _),smul_eq_mul]
  have he : (fun y => density ρ a y*Real.exp (s*y))=
      fun y => (beta (ρ-s) a/beta ρ a)*density (ρ-s) a y := by
    funext y
    rw [mul_comm,density_tilt hρ ha hs]
  rw [he]
  exact (density_integrable (sub_pos.mpr hs) ha).const_mul _

/-- The genuine exponential moment, valid throughout s<rho. -/
theorem exponential_moment {ρ a s : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hs : s < ρ) :
    (∫ y : ℝ,Real.exp (s*y) ∂law ρ a)=beta (ρ-s) a/beta ρ a := by
  rw [integral_law hρ ha (f := fun y : ℝ => Real.exp (s*y)) (by fun_prop)]
  have he : (fun y => density ρ a y*Real.exp (s*y))=
      fun y => (beta (ρ-s) a/beta ρ a)*density (ρ-s) a y := by
    funext y
    rw [mul_comm,density_tilt hρ ha hs]
  rw [he,integral_const_mul,integral_density (sub_pos.mpr hs) ha,mul_one]

/-- All natural moments, and in particular the required second moment,
are finite because there are genuine exponential moments around zero. -/
theorem power_integrable {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (n : ℕ) :
    Integrable (fun y : ℝ => y^n) (law ρ a) :=
  integrable_pow_of_integrable_exp_mul (X := fun y : ℝ => y) (t := ρ/2)
    (ne_of_gt (half_pos hρ)) (exponential_integrable hρ ha (by linarith))
    (exponential_integrable hρ ha (by linarith)) n

theorem first_moment_integrable {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    Integrable (fun y : ℝ => y) (law ρ a) := by
  simpa only [pow_one] using power_integrable hρ ha 1

theorem second_moment_integrable {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    Integrable (fun y : ℝ => y^2) (law ρ a) := power_integrable hρ ha 2

theorem second_moment_memLp {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    MemLp id 2 (law ρ a) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr (second_moment_integrable hρ ha)

theorem mean_positive {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    0 < ∫ y : ℝ,y ∂law ρ a := by
  let := law_probability hρ ha
  have hp := law_positive_support ρ a
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono (fun _ hy => hy.le))
    (first_moment_integrable hρ ha)).mpr
  have he : (law ρ a) (Function.support (fun y : ℝ => y))=(law ρ a) univ := by
    apply measure_congr
    filter_upwards [hp] with y hy
    simp [Function.mem_support,ne_of_gt hy]
  rw [he,measure_univ]
  norm_num

theorem law_absolutelyContinuous {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    law ρ a ≪ volume := by
  rw [law_eq_withDensity hρ ha]
  exact withDensity_absolutelyContinuous _ _

theorem law_nonlattice {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    AbsorptionCutoff.Renewal.Nonlattice (law ρ a) :=
  KeyRenewal.nonlattice_of_absolutelyContinuous (law_absolutelyContinuous hρ ha)

theorem negative_expTransform_lt_one {ρ a θ : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hθ : 0 < θ) :
    AbsorptionCutoff.Renewal.expTransform θ (law ρ a) < 1 := by
  let := law_probability hρ ha
  exact KeyRenewal.expTransform_lt_one_of_positive_support hθ (law_positive_support ρ a)

/-- Every genuine distributional input needed by the key renewal theorem. -/
theorem renewal_law_conditions {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    IsProbabilityMeasure (law ρ a) ∧
    AbsorptionCutoff.Renewal.Nonlattice (law ρ a) ∧
    MemLp id 2 (law ρ a) ∧
    0 < (∫ y : ℝ,y ∂law ρ a) ∧
    (∀ θ : ℝ,0 < θ → AbsorptionCutoff.Renewal.expTransform θ (law ρ a) < 1) :=
  ⟨law_probability hρ ha,law_nonlattice hρ ha,second_moment_memLp hρ ha,mean_positive hρ ha,
    fun _ hθ => negative_expTransform_lt_one hρ ha hθ⟩

end SphericalAging.LogBetaMoments
