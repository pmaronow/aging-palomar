module

public import SphericalAging.LogBetaMoments
public import SphericalAging.StationaryBetaConvolution
public import Mathlib.Analysis.SpecialFunctions.Exp

public section

/-! Genuine exponential-power envelope for the actual logarithmic beta
density, with a constructive constant. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SphericalAging.LogBetaEnvelope
noncomputable section
open LogBetaRenewal StationaryBetaConvolution

@[expose] def envelopeConstant (ρ a : ℝ) := (1+2/ρ)/beta ρ a

theorem one_sub_exp_neg_lower (y : ℝ) (hy : 0<y) :
    y/(1+y)≤1-Real.exp (-y) := by
  have hp : 0<1+y := by linarith
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp y) (Real.exp_pos (-y)).le
  have he : Real.exp y*Real.exp (-y)=1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  rw [he] at h
  apply (div_le_iff₀ hp).mpr
  nlinarith only [h]

theorem linear_exp_decay_bound (b y : ℝ) (hb : 0<b) (hy : 0≤y) :
    (1+y)*Real.exp (-b*y)≤1+1/b := by
  have hExp : Real.exp (-b*y)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hAux := Real.mul_exp_neg_le_exp_neg_one (b*y)
  rw [show -(b*y)=(-b)*y by ring] at hAux
  have hOne : Real.exp (-1)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hRate : y*Real.exp (-b*y)≤1/b := by
    apply (le_div_iff₀ hb).mpr
    nlinarith only [hAux,hOne]
  nlinarith only [hExp,hRate]

/-- The actual log-beta density is bounded by a genuine Gamma-type
exponential-power kernel on the entire positive ray. -/
theorem density_envelope {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) :
    0<envelopeConstant ρ a ∧ ∀ y>0,density ρ a y≤
      envelopeConstant ρ a*y^(a-1)*Real.exp (-(ρ/2)*y) := by
  have hBeta : 0<beta ρ a := beta_pos hρ ha
  refine ⟨by dsimp [envelopeConstant];positivity,?_⟩
  intro y hy
  have hp : 0<1+y := by linarith
  have hn : 0<1-Real.exp (-y) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hfrac : 0<y/(1+y) := div_pos hy hp
  have hpow := Real.rpow_le_rpow_of_nonpos hfrac (one_sub_exp_neg_lower y hy) (by linarith : a-1≤0)
  have hExp := linear_exp_decay_bound (ρ/2) y (by linarith) hy.le
  have hpows : (1+y)^(1-a)≤1+y := by
    calc
      _ ≤ (1+y)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := Real.rpow_one _
  have hCoeff : (1+y)^(1-a)*Real.exp (-(ρ/2)*y)≤1+2/ρ := by
    have hh := mul_le_mul_of_nonneg_right hpows (Real.exp_pos (-(ρ/2)*y)).le
    have hi : 1+1/(ρ/2)=1+2/ρ := by field_simp <;> ring
    exact (hh.trans hExp).trans_eq hi
  have hFactor : (y/(1+y))^(a-1)=y^(a-1)*(1+y)^(1-a) := by
    rw [Real.div_rpow hy.le hp.le,div_eq_mul_inv,←Real.rpow_neg hp.le]
    rw [show -(a-1)=1-a by ring]
  rw [hFactor] at hpow
  have hAll := mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-ρ*y)).le
  have he : Real.exp (-ρ*y)=Real.exp (-(ρ/2)*y)*Real.exp (-(ρ/2)*y) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he] at hAll
  have hFinal := mul_le_mul_of_nonneg_left hCoeff (show 0≤y^(a-1)*Real.exp (-(ρ/2)*y) by positivity)
  rw [density_formula hy]
  unfold envelopeConstant
  apply (div_le_iff₀ hBeta).mpr
  have hR : ((1+2/ρ)/beta ρ a*y^(a-1)*Real.exp (-(ρ/2)*y))*beta ρ a=
      (1+2/ρ)*y^(a-1)*Real.exp (-(ρ/2)*y) := by field_simp [hBeta.ne'] <;> ring
  rw [hR,he]
  exact hAll.trans (by nlinarith only [hFinal])

/-- The genuine density is continuous at every strictly positive argument. -/
theorem density_continuousOn_positive {ρ a : ℝ} : ContinuousOn (density ρ a) (Ioi 0) := by
  intro y hy
  have hy0 : 0<y := hy
  have hn : 0<1-Real.exp (-y) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hc : ContinuousAt (fun y : ℝ => Real.exp (-ρ*y)*(1-Real.exp (-y))^(a-1)/beta ρ a) y := by
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    exact ContinuousAt.rpow_const (by fun_prop) (Or.inl hn.ne')
  apply hc.continuousWithinAt.congr
  · intro t ht
    exact density_formula ht
  · exact density_formula hy0

end
end SphericalAging.LogBetaEnvelope
