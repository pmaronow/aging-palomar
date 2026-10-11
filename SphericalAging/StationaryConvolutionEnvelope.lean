module

public import SphericalAging.StationaryWeightedFTC

public section

/-! Genuine profile-convolution bounds for the finite Schur cutoff. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryConvolutionEnvelope
noncomputable section
open StationaryNormalization StationaryComparison StationaryPatchedProfiles
  StationaryConvolutionDerivative StationaryBetaConvolution

/-- The actual self-convolution of a unit-range profile lies between0 andt. -/
theorem admissible_self_convolution_bounds (u : ℝ → ℝ) (hu : AdmissibleProfile u) (t : ℝ) (ht : 0≤t) :
    0≤causalConvolution u u t ∧ causalConvolution u u t≤t := by
  have hc : ContinuousOn (fun s => u (t-s)*u s) (uIcc 0 t) := by
    apply ContinuousOn.mul
    · apply (hu.locally_AC t ht).continuousOn.comp (by fun_prop)
      intro s hs
      rw [uIcc_of_le ht] at hs ⊢
      exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
    · exact (hu.locally_AC t ht).continuousOn
  have hi := hc.intervalIntegrable (μ:=volume)
  unfold causalConvolution
  constructor
  · apply intervalIntegral.integral_nonneg ht
    intro s hs
    exact mul_nonneg (hu.values (t-s) (by change 0≤t-s; linarith [hs.2])).1 (hu.values s hs.1).1
  · have hm := intervalIntegral.integral_mono_on ht hi (intervalIntegrable_const (c:=(1:ℝ))) (fun s hs => ?_)
    · simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] using hm
    · have h1 := hu.values (t-s) (by change 0≤t-s; linarith [hs.2])
      have h2 := hu.values s hs.1
      exact (mul_le_mul h1.2 h2.2 h2.1 (by norm_num : (0:ℝ)≤1)).trans_eq (by ring)

/-- The source beta bound for the actual Q=u*u follows from the genuine
raw-power majorant and actual affine convolution substitution. -/
theorem self_convolution_beta_bound (u : ℝ → ℝ) (a A t : ℝ)
    (ha0 : 0<a) (ha1 : a<1) (hA : 0≤A) (ht : 0<t)
    (hu : ContinuousOn u (Ici 0)) (hb : ∀ s≥0,0≤u s ∧ u s≤A*(1+s)^(-a)) :
    causalConvolution u u t≤A^2*ProbabilityTheory.beta (1-a) (1-a)*t^(1-2*a) := by
  have hc : ContinuousOn (fun z => u (t*(1-z))*u (t*z)) (uIcc 0 1) := by
    apply ContinuousOn.mul
    · apply hu.comp (by fun_prop)
      intro z hz
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hz
      exact mul_nonneg ht.le (by linarith [hz.2])
    · apply hu.comp (by fun_prop)
      intro z hz
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hz
      exact mul_nonneg ht.le hz.1
  have hi := hc.intervalIntegrable (μ:=volume)
  have hβ := betaKernel_integrable_unit a a ha1 ha1
  let C := A^2*t^(-2*a)
  have hci := hβ.const_mul C
  have hmajor : (∫ z in 0..1,u (t*(1-z))*u (t*z))≤C*ProbabilityTheory.beta (1-a) (1-a) := by
    have he := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1) hi hci ?_
    · rw [intervalIntegral.integral_const_mul,betaKernel_integral_unit a a ha1 ha1] at he
      exact he
    · intro z hzI
      have hz0 := hzI.1
      have hz1 := hzI.2
      have hx0 : 0<t*(1-z) := mul_pos ht (by linarith)
      have hy0 : 0<t*z := mul_pos ht hz0
      have hF := (hb (t*(1-z)) hx0.le).2
      have hG := (hb (t*z) hy0.le).2
      have hRawF := Real.rpow_le_rpow_of_nonpos hx0 (by linarith : t*(1-z)≤1+t*(1-z)) (by linarith : -a≤0)
      have hRawG := Real.rpow_le_rpow_of_nonpos hy0 (by linarith : t*z≤1+t*z) (by linarith : -a≤0)
      have hF' := hF.trans (mul_le_mul_of_nonneg_left hRawF hA)
      have hG' := hG.trans (mul_le_mul_of_nonneg_left hRawG hA)
      have he := mul_le_mul hF' hG' (hb (t*z) hy0.le).1 (by positivity : 0≤A*(t*(1-z))^(-a))
      rw [Real.mul_rpow ht.le (by linarith : 0≤1-z),Real.mul_rpow ht.le hz0.le] at he
      have hpow : t^(-a)*t^(-a)=t^(-2*a) := by rw [← Real.rpow_add ht]; congr 1; ring
      change u (t*(1-z))*u (t*z)≤C*betaKernel a a z
      dsimp [C,betaKernel]
      convert he using 1
      calc
        _ = A^2*(t^(-a)*t^(-a))*(z^(-a)*(1-z)^(-a)) := by rw [hpow]
        _ = _ := by ring
  have he := mul_le_mul_of_nonneg_left hmajor ht.le
  rw [← causal_unit_interval u u t] at he
  have hpow : t*t^(-2*a)=t^(1-2*a) := by
    calc
      _ = t^(1:ℝ)*t^(-2*a) := by rw [Real.rpow_one]
      _ = t^(1-2*a) := by rw [← Real.rpow_add ht]; congr 1; ring
  dsimp [C] at he
  convert he using 1
  calc
    _ = A^2*ProbabilityTheory.beta (1-a) (1-a)*(t*t^(-2*a)) := by rw [hpow]
    _ = _ := by ring

end
end SphericalAging.StationaryConvolutionEnvelope
