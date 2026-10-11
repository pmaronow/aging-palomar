module

public import SphericalAging.StationaryPatchedProfiles

public section

/-! Actual lower patched-profile memory comparison. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryLowerResidual
noncomputable section
open StationaryNormalization StationaryComparison StationaryPatchedProfiles StationaryIdealResidual

theorem lowerPatch_above_ideal (u f : ℝ → ℝ) (h T τ z : ℝ)
    (hu : AdmissibleProfile u) (hf : AdmissibleProfile f) (huT : u T=h)
    (hT : 0≤T) (hτ : 0<τ) (hz : 0≤z) :
    h*f z≤lowerPatch u h T τ f (τ*z) := by
  have hh : 0≤h := by rw [← huT]; exact (hu.values T hT).1
  by_cases hzt : τ*z≤T
  · rw [lowerPatch,joinAt_left T u _ (τ*z) hzt]
    have huord := hu.nonincreasing (show τ*z∈Ici 0 from mul_nonneg hτ.le hz) hT hzt
    have hfb := mul_le_mul_of_nonneg_left (hf.values z hz).2 hh
    rw [huT] at huord
    simp only [mul_one] at hfb
    exact hfb.trans huord
  · rw [lowerPatch,joinAt_right T u _ (τ*z) (lt_of_not_ge hzt)]
    have harg0 : 0≤(τ*z-T)/τ := div_nonneg (by linarith) hτ.le
    have hargz : (τ*z-T)/τ≤z := by apply (div_le_iff₀ hτ).mpr; nlinarith
    exact mul_le_mul_of_nonneg_left (hf.nonincreasing harg0 hz hargz) hh

theorem C1_positive_differentiable (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Ici 0)) (t : ℝ) (ht : 0<t) :
    DifferentiableAt ℝ f t := by
  exact ((hf.differentiableOn (by norm_num)) t ht.le).differentiableAt (Ici_mem_nhds ht)

/-- The actual late-time derivative of the lower patch. -/
theorem lowerPatch_deriv_tail (u f : ℝ → ℝ) (h T τ t : ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici 0)) (hτ : 0<τ) (ht : T<t) :
    deriv (lowerPatch u h T τ f) t=(h/τ)*deriv f ((t-T)/τ) := by
  rw [lowerPatch,joinAt_deriv_right T u _ t ht]
  exact (scaledTail_hasDerivAt h T τ t f
    (C1_positive_differentiable f hf _ (div_pos (sub_pos.mpr ht) hτ))).deriv

/-- Integration over the actual tail uses a real affine substitution. -/
theorem lower_tail_memory_substitution (M P f : ℝ → ℝ) (h T τ t : ℝ) (hτ : 0<τ) :
    (∫ s in T..t,M (P (t-s))*((h/τ)*deriv f ((s-T)/τ))) =
      h*causalConvolution (fun z => M (P (τ*z))) (deriv f) ((t-T)/τ) := by
  let x := (t-T)/τ
  have he := intervalIntegral.smul_integral_comp_sub_mul
    (fun s => M (P (t-s))*((h/τ)*deriv f ((s-T)/τ))) τ t (a:=0) (b:=x)
  have hxend : t-τ*x=T := by dsimp [x]; field_simp [hτ.ne']; ring
  simp only [smul_eq_mul,mul_zero,sub_zero,hxend] at he
  rw [← he]
  rw [causal_convolution_comm]
  unfold causalConvolution
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z _
  have harg : (t-τ*z-T)/τ=x-z := by dsimp [x]; field_simp [hτ.ne']; ring
  have hpos : t-(t-τ*z)=τ*z := by ring
  change τ*(M (P (t-(t-τ*z)))*((h/τ)*deriv f ((t-τ*z-T)/τ)))=h*(deriv f (x-z)*M (P (τ*z)))
  rw [harg,hpos]
  field_simp [hτ.ne']


theorem memory_derivative_intervalIntegrable (M P : ℝ → ℝ) (t : ℝ) (ht : 0≤t)
    (hM : Continuous M) (hP : AbsolutelyContinuousOnInterval P 0 t) :
    IntervalIntegrable (fun s => M (P (t-s))*deriv P s) volume 0 t := by
  have hc : ContinuousOn (fun s => M (P (t-s))) (uIcc 0 t) := by
    apply hM.comp_continuousOn
    apply hP.continuousOn.comp (by fun_prop)
    intro s hs
    rw [uIcc_of_le ht] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  exact hP.intervalIntegrable_deriv.continuousOn_mul hc

/-- The source lower-patch residual inequality, derived by actual memory
splitting, affine substitution, and monotonicity. No residual inequality is
an input. -/
theorem lowerPatch_residual_bound (M u f : ℝ → ℝ) (h T τ t : ℝ)
    (hM : Continuous M) (hMmono : MonotoneOn M (Icc 0 1))
    (hu : AdmissibleProfile u) (hf : AdmissibleProfile f)
    (huC1 : ContDiffOn ℝ 1 u (Ici 0)) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (huT : u T=h) (hT : 0≤T) (hτ : 0<τ) (ht : T<t) :
    profileResidual M (lowerPatch u h T τ f) t ≤
      (h/τ)*deriv f ((t-T)/τ)+h*f ((t-T)/τ)-(1-h)*M (h*f ((t-T)/τ))+
        h*causalConvolution (fun z => M (h*f z)) (deriv f) ((t-T)/τ) := by
  let P := lowerPatch u h T τ f
  let x := (t-T)/τ
  have ht0 : 0<t := hT.trans_lt ht
  have hx0 : 0<x := div_pos (sub_pos.mpr ht) hτ
  have hh0 : 0≤h := by rw [← huT]; exact (hu.values T hT).1
  have hP := lowerPatch_admissible u f h T τ hT hτ huC1 hfC1 hu hf huT
  have hPac := hP.locally_AC t ht0.le
  have hPt : P t=h*f x := joinAt_right T u _ t ht
  have hi := memory_derivative_intervalIntegrable M P t ht0.le hM hPac
  have hi0 := hi.mono (by
    rw [uIcc_of_le hT,uIcc_of_le ht0.le]
    exact Icc_subset_Icc le_rfl ht.le) le_rfl
  have hiT := hi.mono (by
    rw [uIcc_of_le ht.le,uIcc_of_le ht0.le]
    exact Icc_subset_Icc hT le_rfl) le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi0 hiT
  have hfirstEq : (∫ s in 0..T,M (P (t-s))*deriv P s)=
      ∫ s in 0..T,M (P (t-s))*deriv u s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne T] with s hs hsI
    rw [uIoc_of_le hT] at hsI
    have hsT : s<T := lt_of_le_of_ne hsI.2 hs
    rw [show deriv P s=deriv u s from joinAt_deriv_left T u _ s hsT]
  have hker : ContinuousOn (fun s => M (P (t-s))) (uIcc 0 T) := by
    apply hM.comp_continuousOn
    apply hPac.continuousOn.comp (by fun_prop)
    intro s hs
    rw [uIcc_of_le hT] at hs
    rw [uIcc_of_le ht0.le]
    constructor <;> linarith [hs.1,hs.2]
  have huac := hu.locally_AC T hT
  have hui := huac.intervalIntegrable_deriv
  have hfirstBound : (∫ s in 0..T,M (P (t-s))*deriv u s)≤
      M (h*f x)*(h-1) := by
    have hb := intervalIntegral.integral_mono_on hT (hui.continuousOn_mul hker)
      (hui.const_mul (M (h*f x))) (fun s hs => ?_)
    · rw [intervalIntegral.integral_const_mul,huac.integral_deriv_eq_sub,huT,hu.initial] at hb
      exact hb
    · have hts0 : 0≤t-s := by linarith [hs.2]
      have htsT : t-s≤t := by linarith [hs.1]
      have hPord := hP.nonincreasing hts0 ht0.le htsT
      change P t≤P (t-s) at hPord
      rw [hPt] at hPord
      have hm := hMmono (by rw [← hPt]; exact hP.values t ht0.le)
        (hP.values (t-s) hts0) hPord
      exact mul_le_mul_of_nonpos_right hm (antitoneOn_deriv_nonpos u hu.nonincreasing s hs.1)
  have htailEq : (∫ s in T..t,M (P (t-s))*deriv P s)=
      ∫ s in T..t,M (P (t-s))*((h/τ)*deriv f ((s-T)/τ)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hsI
    rw [uIoc_of_le ht.le] at hsI
    rw [show deriv P s=(h/τ)*deriv f ((s-T)/τ) from lowerPatch_deriv_tail u f h T τ s hfC1 hτ hsI.1]
  have hfInt : IntervalIntegrable (fun z => deriv f (x-z)) volume 0 x := by
    simpa only [sub_zero,sub_self] using ((hf.locally_AC x hx0.le).intervalIntegrable_deriv.comp_sub_left x).symm
  have hPscaled : ContinuousOn (fun z => M (P (τ*z))) (uIcc 0 x) := by
    apply hM.comp_continuousOn
    apply (hP.locally_AC (τ*x) (mul_nonneg hτ.le hx0.le)).continuousOn.comp (by fun_prop)
    intro z hz
    rw [uIcc_of_le hx0.le] at hz
    rw [uIcc_of_le (mul_nonneg hτ.le hx0.le)]
    exact ⟨mul_nonneg hτ.le hz.1,mul_le_mul_of_nonneg_left hz.2 hτ.le⟩
  have hfscaled : ContinuousOn (fun z => M (h*f z)) (uIcc 0 x) :=
    hM.comp_continuousOn (continuousOn_const.mul (hf.locally_AC x hx0.le).continuousOn)
  have htailBound : causalConvolution (fun z => M (P (τ*z))) (deriv f) x≤
      causalConvolution (fun z => M (h*f z)) (deriv f) x := by
    rw [causal_convolution_comm (fun z => M (P (τ*z))),causal_convolution_comm (fun z => M (h*f z))]
    unfold causalConvolution
    have hb := intervalIntegral.integral_mono_on hx0.le
      (hfInt.mul_continuousOn hPscaled) (hfInt.mul_continuousOn hfscaled) (fun z hz => ?_)
    · exact hb
    · have hpord := lowerPatch_above_ideal u f h T τ z hu hf huT hT hτ hz.1
      have hpval := hP.values (τ*z) (mul_nonneg hτ.le hz.1)
      have hfval : h*f z∈Icc 0 1 := by
        have hhh1 : h≤1 := by rw [← huT]; exact (hu.values T hT).2
        exact ⟨mul_nonneg hh0 (hf.values z hz.1).1,
          (mul_le_mul_of_nonneg_left (hf.values z hz.1).2 hh0).trans (by simpa only [mul_one] using hhh1)⟩
      exact mul_le_mul_of_nonpos_left (hMmono hfval hpval hpord)
        (antitoneOn_deriv_nonpos f hf.nonincreasing (x-z) (by linarith [hz.2]))
  unfold profileResidual
  rw [lowerPatch_deriv_tail u f h T τ t hfC1 hτ ht]
  change (h/τ)*deriv f x+P t+(∫ s in 0..t,M (P (t-s))*deriv P s)≤_
  rw [← hsplit,hfirstEq,htailEq,lower_tail_memory_substitution M P f h T τ t hτ,hPt]
  have hb := mul_le_mul_of_nonneg_left htailBound hh0
  dsimp [x] at *
  linarith


theorem normalized_memory_continuous (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) :
    Continuous (normalizedMemory q (purePhi p (β^2) γ)) := by
  have he : normalizedMemory q (purePhi p (β^2) γ)=
      (fun y => y+∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*y^(j+2)) := funext h.memory_expansion
  rw [he]
  fun_prop

/-- The lower-patch inequality for the exact manuscript normalized memory. -/
theorem normalized_lowerPatch_residual_bound (p : ℕ) (β γ q : ℝ) (c r f : ℝ → ℝ) (hscale T τ t : ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r)
    (hf : AdmissibleProfile f) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (huT : normalizedProfile q c T=hscale) (hT : 0≤T) (hτ : 0<τ) (ht : T<t) :
    profileResidual (normalizedMemory q (purePhi p (β^2) γ))
      (lowerPatch (normalizedProfile q c) hscale T τ f) t ≤
        (hscale/τ)*deriv f ((t-T)/τ)+
          StationaryCorrectedCriticalProfiles.normalizedIdealResidual p β γ q hscale f ((t-T)/τ) := by
  obtain ⟨hM0,hMono,L,hLip⟩ := normalized_memory_properties p β γ q c r h
  obtain ⟨hu,huRes⟩ := normalized_profile_admissible p β γ q c r h
  have hb := lowerPatch_residual_bound (normalizedMemory q (purePhi p (β^2) γ))
    (normalizedProfile q c) f hscale T τ t (normalized_memory_continuous p β γ q c r h)
    hMono hu hf h.profile_C1 hfC1 huT hT hτ ht
  unfold StationaryCorrectedCriticalProfiles.normalizedIdealResidual
  convert hb using 1; ring

end
end SphericalAging.StationaryLowerResidual
