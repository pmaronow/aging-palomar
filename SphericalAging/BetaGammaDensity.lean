module

public import SphericalAging.LogBetaRenewal
public import Mathlib.Probability.Distributions.Gamma

public section

/-! Analytic beta--gamma product density, with the actual beta and gamma PDFs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped Topology ENNReal
namespace SphericalAging.BetaGammaDensity

@[expose] def productKernel (ρ a z b : ℝ) : ℝ :=
  betaPDFReal ρ a b * gammaPDFReal (ρ+a) 1 (z/b) / b

@[expose] def substitution (z v : ℝ) : ℝ := z / (z+v)

theorem substitution_pos_lt_one {z v : ℝ} (hz : 0 < z) (hv : 0 < v) :
    0 < substitution z v ∧ substitution z v < 1 := by
  dsimp [substitution]
  exact ⟨div_pos hz (add_pos hz hv), (div_lt_one (add_pos hz hv)).mpr (by linarith)⟩

theorem substitution_image {z : ℝ} (hz : 0 < z) :
    substitution z '' Ioi 0 = Ioo 0 1 := by
  ext b
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact substitution_pos_lt_one hz hv
  · intro hb
    refine ⟨z*(1-b)/b, div_pos (mul_pos hz (sub_pos.mpr hb.2)) hb.1, ?_⟩
    dsimp [substitution]
    have hn : z+z*(1-b)/b ≠ 0 := ne_of_gt (add_pos hz
      (div_pos (mul_pos hz (sub_pos.mpr hb.2)) hb.1))
    field_simp [ne_of_gt hz,ne_of_gt hb.1,hn]
    <;> ring

theorem substitution_injective {z : ℝ} (hz : 0 < z) :
    InjOn (substitution z) (Ioi 0) := by
  intro v hv w hw he
  dsimp [substitution] at he
  have h := (div_eq_div_iff (ne_of_gt (add_pos hz hv))
    (ne_of_gt (add_pos hz hw))).mp he
  nlinarith

theorem substitution_hasDerivAt {z v : ℝ} (hz : 0 < z) (hv : 0 < v) :
    HasDerivAt (substitution z) (-z/(z+v)^2) v := by
  unfold substitution
  convert (hasDerivAt_const v z).div ((hasDerivAt_id v).const_add z)
    (ne_of_gt (add_pos hz hv)) using 1 <;> simp <;> rfl

theorem positive_power_cancel {z v w : ℝ} (hz : 0 < z) (hv : 0 < v)
    (hw : 0 < w) (r s : ℝ) :
    (z/w)^r*(v/w)^s*w^(r+s+1)/w = z^r*v^s := by
  rw [Real.div_rpow hz.le hw.le, Real.div_rpow hv.le hw.le,
    Real.rpow_add hw (r+s) 1, Real.rpow_add hw r s, Real.rpow_one]
  field_simp [ne_of_gt hw,ne_of_gt (Real.rpow_pos_of_pos hw r),
    ne_of_gt (Real.rpow_pos_of_pos hw s)]

theorem transformed_kernel {ρ a z v : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (hz : 0 < z) (hv : 0 < v) :
    (z/(z+v)^2) * productKernel ρ a z (substitution z v) =
      (z^(ρ-1)*Real.exp (-z)/(Real.Gamma ρ*Real.Gamma a)) *
        (v^(a-1)*Real.exp (-v)) := by
  have hw := add_pos hz hv
  have hb := substitution_pos_lt_one hz hv
  have hc : z/substitution z v=z+v := by
    dsimp [substitution]
    field_simp [ne_of_gt hz,ne_of_gt hw]
  have hd : 1-substitution z v=v/(z+v) := by
    dsimp [substitution]
    field_simp
    <;> ring
  unfold productKernel
  rw [betaPDFReal,ite_eq_left hb,gammaPDFReal,hc,ite_eq_left hw.le,Real.one_rpow,one_mul,hd]
  have hp := positive_power_cancel hz hv hw (ρ-1) (a-1)
  have he : ρ+a-1=(ρ-1)+(a-1)+1 := by ring
  rw [←he] at hp
  have hexp : Real.exp (-(z+v))=Real.exp (-z)*Real.exp (-v) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hexp]
  dsimp [substitution]
  unfold beta
  have hGρ := ne_of_gt (Real.Gamma_pos_of_pos hρ)
  have hGa := ne_of_gt (Real.Gamma_pos_of_pos ha)
  have hGb := ne_of_gt (Real.Gamma_pos_of_pos (add_pos hρ ha))
  calc
    _ = ((z/(z+v))^(ρ-1)*(v/(z+v))^(a-1)*(z+v)^(ρ+a-1)/(z+v)) *
        Real.exp (-z)*Real.exp (-v)/(Real.Gamma ρ*Real.Gamma a) := by
      field_simp [hGρ,hGa,hGb,ne_of_gt hz,ne_of_gt hw]
      <;> ring
    _ = _ := by rw [hp]; ring

/-- The genuine product-density convolution simplifies to the gamma density. -/
theorem integral_productKernel {ρ a z : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hz : 0 < z) :
    (∫ b in Ioo 0 1, productKernel ρ a z b) = gammaPDFReal ρ 1 z := by
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun v (hv : 0 < v) => (substitution_hasDerivAt hz hv).hasDerivWithinAt)
    (substitution_injective hz) (productKernel ρ a z)
  rw [substitution_image hz] at hi
  have habs : ∀ v ∈ Ioi (0:ℝ), |(-z/(z+v)^2)|=z/(z+v)^2 := by
    intro v hv
    rw [abs_div,abs_neg,abs_of_pos hz,abs_of_nonneg (sq_nonneg _)]
  calc
    _ = ∫ v in Ioi 0, (z/(z+v)^2)*productKernel ρ a z (substitution z v) := by
      rw [hi]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      simp only [habs v hv,smul_eq_mul]
    _ = (z^(ρ-1)*Real.exp (-z)/(Real.Gamma ρ*Real.Gamma a))*
        ∫ v in Ioi 0,v^(a-1)*Real.exp (-v) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact transformed_kernel hρ ha hz hv
    _ = (z^(ρ-1)*Real.exp (-z)/(Real.Gamma ρ*Real.Gamma a))*Real.Gamma a := by
      rw [Real.Gamma_eq_integral ha]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      ring
    _ = _ := by
      rw [gammaPDFReal,ite_eq_left hz.le,Real.one_rpow,one_mul]
      field_simp [ne_of_gt (Real.Gamma_pos_of_pos hρ),ne_of_gt (Real.Gamma_pos_of_pos ha)]


theorem integrableOn_productKernel {ρ a z : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hz : 0 < z) :
    IntegrableOn (productKernel ρ a z) (Ioo 0 1) := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun v (hv : 0 < v) => (substitution_hasDerivAt hz hv).hasDerivWithinAt)
    (substitution_injective hz) (productKernel ρ a z)
  rw [substitution_image hz] at hi
  apply hi.mpr
  have hg := (Real.GammaIntegral_convergent ha).const_mul
    (z^(ρ-1)*Real.exp (-z)/(Real.Gamma ρ*Real.Gamma a))
  apply hg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have habs : |(-z/(z+v)^2)|=z/(z+v)^2 := by
    rw [abs_div,abs_neg,abs_of_pos hz,abs_of_nonneg (sq_nonneg _)]
  simp only [habs,smul_eq_mul]
  rw [transformed_kernel hρ ha hz hv]
  ring

theorem productKernel_nonnegative {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (z b : ℝ) :
    0 ≤ productKernel ρ a z b := by
  by_cases hb : 0 < b ∧ b < 1
  · exact div_nonneg (mul_nonneg (LogBetaRenewal.betaPDFReal_nonnegative hρ ha _)
      (gammaPDFReal_nonneg (add_pos hρ ha) zero_lt_one _)) hb.1.le
  · simp [productKernel,betaPDFReal,hb]

theorem productKernel_zero_outside {ρ a z b : ℝ} (hb : b ∉ Ioo (0:ℝ) 1) :
    productKernel ρ a z b=0 := by
  simp only [mem_Ioo] at hb
  simp [productKernel,betaPDFReal,hb]

end SphericalAging.BetaGammaDensity
