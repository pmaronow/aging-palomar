module

public import SphericalAging.StationaryLogSource
public import SphericalAging.StationaryLogProfile
public import SphericalAging.GammaSmoothingVariance

public section

/-! Exact Laplace/gamma averaging scaling of the actual logarithmic profile. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SphericalAging.StationaryGammaScaling
noncomputable section
open StationaryLaplaceBalance StationaryLogProfile GammaSmoothingVariance

/-- The actual gamma average written using its genuine positive-ray density. -/
theorem gammaAverage_density (b : ℝ) (D : ℝ → ℝ) (x : ℝ) (hb : 0<b) :
    gammaAverage b D x=
      ∫ w in Ioi 0,(w^(b-1)*Real.exp (-w)/Real.Gamma b)*D (x+Real.log w) := by
  unfold gammaAverage gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDFReal b 1).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg hb zero_lt_one _),smul_eq_mul]
  have he : (∫ w in Ici 0,gammaPDFReal b 1 w*D (x+Real.log w))=
      ∫ w : ℝ,gammaPDFReal b 1 w*D (x+Real.log w) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    simp only [mem_Ici,not_le] at hw
    simp [gammaPDFReal,not_le.mpr hw]
  rw [←he,integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  change 0<w at hw
  change gammaPDFReal b 1 w*D (x+Real.log w)=(w^(b-1)*Real.exp (-w)/Real.Gamma b)*D (x+Real.log w)
  simp only [gammaPDFReal,ite_eq_left hw.le,Real.one_rpow,one_mul]
  ring

/-- Exact reconstruction at the scaled positive lag. -/
theorem scaled_logProfile (α x w : ℝ) (F : ℝ → ℝ) (hw : 0<w) :
    w^(-α)*logProfile α F (x+Real.log w)=Real.exp (α*x)*F (Real.exp x*w) := by
  unfold logProfile
  rw [Real.exp_add,Real.exp_log hw,
    show α*(x+Real.log w)=α*x+Real.log w*α by ring,Real.exp_add,
    ←Real.rpow_def_of_pos hw]
  have hi : w^(-α)*w^α=1 := by
    rw [←Real.rpow_add hw,neg_add_cancel,Real.rpow_zero]
  calc
    _ = Real.exp (α*x)*(w^(-α)*w^α)*F (Real.exp x*w) := by ring
    _ = _ := by rw [hi,mul_one]

/-- The genuine positive-ray substitution t=exp(x)w. -/
theorem laplace_exp_scale (F : ℝ → ℝ) (x : ℝ) :
    laplace F (Real.exp (-x))=Real.exp x*(∫ w in Ioi 0,Real.exp (-w)*F (Real.exp x*w)) := by
  have he := integral_comp_mul_left_Ioi' (fun t : ℝ => Real.exp (-Real.exp (-x)*t)*F t)
    (0:ℝ) (Real.exp_pos x)
  simp only [mul_zero,smul_eq_mul] at he
  change Real.exp x*(∫ w in Ioi 0,Real.exp (-Real.exp (-x)*(Real.exp x*w))*F (Real.exp x*w))=
    laplace F (Real.exp (-x)) at he
  rw [←he]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w _
  have hc : -Real.exp (-x)*(Real.exp x*w)=-w := by
    rw [Real.exp_neg]
    field_simp
  change Real.exp (-Real.exp (-x)*(Real.exp x*w))*F (Real.exp x*w)=Real.exp (-w)*F (Real.exp x*w)
  rw [hc]

/-- Exact gamma scaling of an arbitrary logarithmically normalized profile.
All substitution and density statements are proved, rather than inputs. -/
theorem laplace_gamma_scaling (α : ℝ) (F : ℝ → ℝ) (x : ℝ) (hα : α<1) :
    laplace F (Real.exp (-x))=
      Real.exp ((1-α)*x)*Real.Gamma (1-α)*gammaAverage (1-α) (logProfile α F) x := by
  rw [gammaAverage_density _ _ _ (by linarith)]
  have hΓ := ne_of_gt (Real.Gamma_pos_of_pos (show 0<1-α by linarith))
  have hi : Real.Gamma (1-α)*(∫ w in Ioi 0,
      (w^((1-α)-1)*Real.exp (-w)/Real.Gamma (1-α))*logProfile α F (x+Real.log w))=
      Real.exp (α*x)*(∫ w in Ioi 0,Real.exp (-w)*F (Real.exp x*w)) := by
    rw [←integral_const_mul,←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    rw [show (1-α)-1=-α by ring]
    have hp := scaled_logProfile α x w F hw
    calc
      _ = Real.exp (-w)*(w^(-α)*logProfile α F (x+Real.log w)) := by field_simp [hΓ]
      _ = _ := by rw [hp]; ring
  rw [mul_assoc,hi]
  have hExp : Real.exp ((1-α)*x)*Real.exp (α*x)=Real.exp x := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [←mul_assoc,hExp,←laplace_exp_scale]

/-- Actual squaring commutes with logarithmic normalization. -/
theorem squared_logProfile (a : ℝ) (u : ℝ → ℝ) :
    logProfile (2*a) (fun t => u t^2)=fun x => logProfile a u x^2 := by
  funext x
  unfold logProfile
  rw [mul_pow,pow_two (Real.exp (a*x)),←Real.exp_add]
  congr 1
  congr 1
  ring

/-- Both transforms occurring in the quadratic balance have the exact
source gamma-averaging scalings. -/
theorem laplace_critical_profile_scalings (a : ℝ) (u : ℝ → ℝ) (x : ℝ) (ha : a<1/2) :
    laplace u (Real.exp (-x))=
      Real.exp ((1-a)*x)*Real.Gamma (1-a)*gammaAverage (1-a) (logProfile a u) x ∧
    laplace (fun t => u t^2) (Real.exp (-x))=
      Real.exp ((1-2*a)*x)*Real.Gamma (1-2*a)*
        gammaAverage (1-2*a) (fun y => logProfile a u y^2) x := by
  constructor
  · exact laplace_gamma_scaling a u x (by linarith)
  · have he := laplace_gamma_scaling (2*a) (fun t => u t^2) x (by linarith)
    rw [squared_logProfile a u] at he
    exact he

end
end SphericalAging.StationaryGammaScaling
