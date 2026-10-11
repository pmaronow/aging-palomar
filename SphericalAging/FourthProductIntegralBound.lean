module

public import SphericalAging.LpThreeProductBounds

public section

/-! Cauchy–Schwarz for the genuine fourth power of an eighth-integrable product. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SphericalAging.FourthProductIntegralBound
set_option maxHeartbeats 1400000
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}

lemma fourthPower_memLp_two {f : α→E} (hf : MemLp f 8 μ) :
    MemLp (fun q => ‖f q‖^4) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.norm.pow 4)).mpr
  simpa only [Pi.pow_apply,←pow_mul,show 4*2=8 from rfl] using hf.integrable_norm_pow (by norm_num : 8≠0)

theorem integral_product_fourth_le {f g : α→E} (hf : MemLp f 8 μ) (hg : MemLp g 8 μ) :
    (∫q,(‖f q‖*‖g q‖)^4∂μ)≤
      (∫q,‖f q‖^8∂μ)^((1:ℝ)/2)*(∫q,‖g q‖^8∂μ)^((1:ℝ)/2) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (.of_forall (fun q => by positivity : ∀q,0≤‖f q‖^4))
    (.of_forall (fun q => by positivity : ∀q,0≤‖g q‖^4))
    (by simpa using fourthPower_memLp_two hf) (by simpa using fourthPower_memLp_two hg)
  simpa only [mul_pow,Real.rpow_ofNat,←pow_mul,show 4*2=8 from rfl] using h

theorem integral_product_fourth_le_of_moments {f g : α→E} (hf : MemLp f 8 μ) (hg : MemLp g 8 μ)
    (C u v : ℝ) (hC : 0≤C) (hu : 0≤u) (hv : 0≤v)
    (hfm : (∫q,‖f q‖^8∂μ)≤C*u^8) (hgm : (∫q,‖g q‖^8∂μ)≤C*v^8) :
    (∫q,(‖f q‖*‖g q‖)^4∂μ)≤C*u^4*v^4 := by
  apply (integral_product_fourth_le hf hg).trans
  have h1 := Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hfm (by norm_num : (0:ℝ)≤1/2)
  have h2 := Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hgm (by norm_num : (0:ℝ)≤1/2)
  apply (mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)).trans_eq
  rw [Real.mul_rpow hC (by positivity),Real.mul_rpow hC (by positivity)]
  have hr (z : ℝ) (hz : 0≤z) : (z^8)^((1:ℝ)/2)=z^4 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz]
    norm_num
  rw [hr u hu,hr v hv]
  calc
    _=(C^((1:ℝ)/2)*C^((1:ℝ)/2))*u^4*v^4 := by ring
    _=C*u^4*v^4 := by rw [←Real.rpow_add' hC (by norm_num : (1:ℝ)/2+(1:ℝ)/2≠0)];norm_num

end SphericalAging.FourthProductIntegralBound
