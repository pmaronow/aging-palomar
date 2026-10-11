module

public import SphericalAging.StationaryShiftCosts

public section

/-! Exact actual upper-patch memory decomposition and errors. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryUpperResidual
noncomputable section
open StationaryNormalization StationaryComparison StationaryPatchedProfiles StationaryIdealResidual
  StationaryLowerResidual StationaryPowerProfiles StationaryShiftCosts

/-- The actual upper tail derivative. -/
theorem upperPatch_deriv_tail (u f : ℝ → ℝ) (h T0 T1 τ t : ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici 0)) (hτ : 0<τ) (hT1 : T0≤T1) (ht : T1<t) :
    deriv (upperPatch u h T0 T1 τ f) t=(h/τ)*deriv f ((t-T1)/τ) := by
  rw [upperPatch,joinAt_deriv_right T0 u _ t (hT1.trans_lt ht),joinAt_deriv_right T1 _ _ t ht]
  exact (scaledTail_hasDerivAt h T1 τ t f
    (C1_positive_differentiable f hf _ (div_pos (sub_pos.mpr ht) hτ))).deriv

theorem upperPatch_deriv_plateau (u f : ℝ → ℝ) (h T0 T1 τ t : ℝ) (ht0 : T0<t) (ht1 : t<T1) :
    deriv (upperPatch u h T0 T1 τ f) t=0 := by
  rw [upperPatch,joinAt_deriv_right T0 u _ t ht0,joinAt_deriv_left T1 _ _ t ht1,deriv_const]

theorem upperPatch_tail_value (u f : ℝ → ℝ) (h T0 T1 τ t : ℝ) (hT1 : T0≤T1) (ht : T1<t) :
    upperPatch u h T0 T1 τ f t=h*f ((t-T1)/τ) := by
  rw [upperPatch,joinAt_right T0 u _ t (hT1.trans_lt ht),joinAt_right T1 _ _ t ht]
  rfl

/-- Exact clipped representation of the upper patch after its first join. -/
theorem upperPatch_clipped_value (u f : ℝ → ℝ) (h T0 T1 τ s : ℝ)
    (hT : T0≤T1) (hτ : 0<τ) (huT : u T0=h) (hf0 : f 0=1) (hs : T0≤s) :
    upperPatch u h T0 T1 τ f s=h*f (max ((s-T1)/τ) 0) := by
  by_cases hs0 : s=T0
  · subst s
    rw [upperPatch,joinAt_left T0 u _ T0 le_rfl,huT]
    have hx : (T0-T1)/τ≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hT) hτ.le
    rw [max_eq_right hx,hf0,mul_one]
  · have hsT : T0<s := lt_of_le_of_ne hs (Ne.symm hs0)
    rw [upperPatch,joinAt_right T0 u _ s hsT]
    by_cases hs1 : s≤T1
    · rw [joinAt_left T1 _ _ s hs1]
      have hx : (s-T1)/τ≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs1) hτ.le
      rw [max_eq_right hx,hf0,mul_one]
    · rw [joinAt_right T1 _ _ s (lt_of_not_ge hs1)]
      unfold scaledTail
      rw [max_eq_left (div_nonneg (sub_nonneg.mpr (le_of_not_ge hs1)) hτ.le)]

/-- The initial memory segment has the exact clipped representation in the
source proof; the waiting plateau keeps all its arguments beyond T0. -/
theorem upperPatch_initial_memory_value (u f : ℝ → ℝ) (h T0 T1 τ t s : ℝ)
    (hT0 : 0≤T0) (hT1 : 2*T0≤T1) (hτ : 0<τ) (huT : u T0=h) (hf0 : f 0=1)
    (ht : T1<t) (hs : s∈Icc 0 T0) :
    upperPatch u h T0 T1 τ f (t-s)=h*f (max ((t-T1)/τ-s/τ) 0) := by
  have hT01 : T0≤T1 := by linarith
  have harg : T0≤t-s := by linarith [hs.2]
  rw [upperPatch_clipped_value u f h T0 T1 τ (t-s) hT01 hτ huT hf0 harg]
  rw [show (t-s-T1)/τ=(t-T1)/τ-s/τ by ring]

/-- Upper patch values dominate all ideal replacements in the tail memory. -/
theorem upperPatch_above_ideal (u f : ℝ → ℝ) (h T0 T1 τ z : ℝ)
    (hu : AdmissibleProfile u) (hf : AdmissibleProfile f) (huT : u T0=h)
    (hT0 : 0≤T0) (hT1 : T0≤T1) (hτ : 0<τ) (hz : 0≤z) :
    h*f z≤upperPatch u h T0 T1 τ f (τ*z) := by
  have hh : 0≤h := by rw [← huT]; exact (hu.values T0 hT0).1
  by_cases hz0 : τ*z≤T0
  · rw [upperPatch,joinAt_left T0 u _ (τ*z) hz0]
    have hfb := mul_le_mul_of_nonneg_left (hf.values z hz).2 hh
    simp only [mul_one] at hfb
    have hub := hu.nonincreasing (mul_nonneg hτ.le hz) hT0 hz0
    rw [huT] at hub
    exact hfb.trans hub
  · rw [upperPatch_clipped_value u f h T0 T1 τ (τ*z) hT1 hτ huT hf.initial (le_of_not_ge hz0)]
    have harg0 : 0≤max ((τ*z-T1)/τ) 0 := le_max_right _ _
    have hargz : max ((τ*z-T1)/τ) 0≤z := by
      apply max_le _ hz
      apply (div_le_iff₀ hτ).mpr
      have hT10 := hT0.trans hT1
      nlinarith
    exact mul_le_mul_of_nonneg_left (hf.nonincreasing harg0 hz hargz) hh

@[expose] def upperErrorOne (M u f : ℝ → ℝ) (h T0 τ x : ℝ) : ℝ :=
  ∫ s in 0..T0,(M (h*f (max (x-s/τ) 0))-M (h*f x))*(-deriv u s)

@[expose] def upperErrorTwo (M P f : ℝ → ℝ) (h τ x : ℝ) : ℝ :=
  h*∫ z in 0..x,(M (P (τ*z))-M (h*f z))*(-deriv f (x-z))


theorem clipped_memory_continuousOn (M f : ℝ → ℝ) (h τ x A B : ℝ) (hM : Continuous M)
    (hf : ContinuousOn f (Ici 0)) :
    ContinuousOn (fun s => M (h*f (max (x-s/τ) 0))) (uIcc A B) := by
  apply hM.comp_continuousOn
  apply continuousOn_const.mul
  apply hf.comp (by fun_prop)
  exact fun s hs => mem_Ici.mpr (le_max_right _ _)

theorem scaled_memory_continuousOn (M P : ℝ → ℝ) (τ x : ℝ) (hM : Continuous M)
    (hP : AdmissibleProfile P) (hτ : 0<τ) (hx : 0≤x) :
    ContinuousOn (fun z => M (P (τ*z))) (uIcc 0 x) := by
  apply hM.comp_continuousOn
  apply (hP.locally_AC (τ*x) (mul_nonneg hτ.le hx)).continuousOn.comp (by fun_prop)
  intro z hz
  rw [uIcc_of_le hx] at hz
  rw [uIcc_of_le (mul_nonneg hτ.le hx)]
  exact ⟨mul_nonneg hτ.le hz.1,mul_le_mul_of_nonneg_left hz.2 hτ.le⟩

theorem ideal_memory_continuousOn (M f : ℝ → ℝ) (h x : ℝ) (hM : Continuous M)
    (hf : AdmissibleProfile f) (hx : 0≤x) :
    ContinuousOn (fun z => M (h*f z)) (uIcc 0 x) :=
  hM.comp_continuousOn (continuousOn_const.mul (hf.locally_AC x hx).continuousOn)

/-- The initial-segment memory error identity follows from actual integral
linearity and actual AC FTC, including its full original initial segment. -/
theorem initial_memory_error_identity (M u f : ℝ → ℝ) (h T0 τ x : ℝ)
    (hM : Continuous M) (hu : AdmissibleProfile u) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (huT : u T0=h) (hT0 : 0≤T0) :
    (∫ s in 0..T0,M (h*f (max (x-s/τ) 0))*deriv u s)=
      M (h*f x)*(h-1)-upperErrorOne M u f h T0 τ x := by
  have huac := hu.locally_AC T0 hT0
  have hui := huac.intervalIntegrable_deriv
  have hfc := hfC1.continuousOn
  have hi := hui.continuousOn_mul (clipped_memory_continuousOn M f h τ x 0 T0 hM hfc)
  have hconst := hui.const_mul (M (h*f x))
  have he : upperErrorOne M u f h T0 τ x=
      (∫ s in 0..T0,M (h*f x)*deriv u s)-(∫ s in 0..T0,M (h*f (max (x-s/τ) 0))*deriv u s) := by
    unfold upperErrorOne
    rw [← intervalIntegral.integral_sub hconst hi]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [intervalIntegral.integral_const_mul,huac.integral_deriv_eq_sub,huT,hu.initial] at he
  linarith

/-- The actual tail error is exactly the difference between its two causal
memory convolutions, by interval reflection and integral linearity. -/
theorem tail_memory_error_identity (M P f : ℝ → ℝ) (h τ x : ℝ)
    (hM : Continuous M) (hP : AdmissibleProfile P) (hf : AdmissibleProfile f) (hτ : 0<τ) (hx : 0≤x) :
    h*causalConvolution (fun z => M (P (τ*z))) (deriv f) x=
      h*causalConvolution (fun z => M (h*f z)) (deriv f) x-upperErrorTwo M P f h τ x := by
  have hfi : IntervalIntegrable (fun z => deriv f (x-z)) volume 0 x := by
    simpa only [sub_zero,sub_self] using ((hf.locally_AC x hx).intervalIntegrable_deriv.comp_sub_left x).symm
  have hp := hfi.continuousOn_mul (scaled_memory_continuousOn M P τ x hM hP hτ hx)
  have hi := hfi.continuousOn_mul (ideal_memory_continuousOn M f h x hM hf hx)
  have he : upperErrorTwo M P f h τ x=h*((∫ z in 0..x,M (h*f z)*deriv f (x-z))-
      (∫ z in 0..x,M (P (τ*z))*deriv f (x-z))) := by
    unfold upperErrorTwo
    rw [← intervalIntegral.integral_sub hi hp]
    congr 1
    apply intervalIntegral.integral_congr
    intro z _
    ring
  rw [he,causal_convolution_comm (fun z => M (P (τ*z))),causal_convolution_comm (fun z => M (h*f z))]
  unfold causalConvolution
  have hcomm1 : (∫ z in 0..x,deriv f (x-z)*M (P (τ*z)))=(∫ z in 0..x,M (P (τ*z))*deriv f (x-z)) := by
    apply intervalIntegral.integral_congr
    intro z _
    ring
  have hcomm2 : (∫ z in 0..x,deriv f (x-z)*M (h*f z))=(∫ z in 0..x,M (h*f z)*deriv f (x-z)) := by
    apply intervalIntegral.integral_congr
    intro z _
    ring
  rw [hcomm1,hcomm2]
  ring


@[expose] def generalIdealResidual (M : ℝ → ℝ) (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  h*f x-(1-h)*M (h*f x)+h*causalConvolution (fun z => M (h*f z)) (deriv f) x

/-- The exact source upper-memory decomposition, proved for actual locally
AC profiles and actual interval integrals. -/
theorem upperPatch_residual_decomposition (M u f : ℝ → ℝ) (h T0 T1 τ t : ℝ)
    (hM : Continuous M) (hu : AdmissibleProfile u) (hf : AdmissibleProfile f)
    (huC1 : ContDiffOn ℝ 1 u (Ici 0)) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (huT : u T0=h) (hT0 : 0≤T0) (hT1 : 2*T0≤T1) (hτ : 0<τ) (ht : T1<t) :
    profileResidual M (upperPatch u h T0 T1 τ f) t =
      (h/τ)*deriv f ((t-T1)/τ)+generalIdealResidual M h f ((t-T1)/τ)-
        upperErrorOne M u f h T0 τ ((t-T1)/τ)-
          upperErrorTwo M (upperPatch u h T0 T1 τ f) f h τ ((t-T1)/τ) := by
  let P := upperPatch u h T0 T1 τ f
  let x := (t-T1)/τ
  have hT01 : T0≤T1 := by linarith
  have hT10 : 0≤T1 := hT0.trans hT01
  have ht0 : 0<t := hT10.trans_lt ht
  have hx0 : 0<x := div_pos (sub_pos.mpr ht) hτ
  have hP := upperPatch_admissible u f h T0 T1 τ hT0 hT01 hτ huC1 hfC1 hu hf huT
  have hi := memory_derivative_intervalIntegrable M P t ht0.le hM (hP.locally_AC t ht0.le)
  have hrestrict (A B : ℝ) (hA : 0≤A) (hAB : A≤B) (hB : B≤t) :
      IntervalIntegrable (fun s => M (P (t-s))*deriv P s) volume A B := by
    apply hi.mono _ le_rfl
    rw [uIcc_of_le hAB,uIcc_of_le ht0.le]
    exact Icc_subset_Icc hA hB
  have hi0 := hrestrict 0 T0 le_rfl hT0 (hT01.trans ht.le)
  have hi01 := hrestrict T0 T1 hT0 hT01 ht.le
  have hi1 := hrestrict 0 T1 le_rfl hT10 ht.le
  have hit := hrestrict T1 t hT10 ht.le le_rfl
  have hsplit0 := intervalIntegral.integral_add_adjacent_intervals hi0 hi01
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hi1 hit
  have hplateau : (∫ s in T0..T1,M (P (t-s))*deriv P s)=0 := by
    have he : (∫ s in T0..T1,M (P (t-s))*deriv P s)=(∫ s in T0..T1,(0:ℝ)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne T1] with s hs hsI
      rw [uIoc_of_le hT01] at hsI
      change M (P (t-s))*deriv (upperPatch u h T0 T1 τ f) s=0
      rw [upperPatch_deriv_plateau u f h T0 T1 τ s hsI.1 (lt_of_le_of_ne hsI.2 hs),mul_zero]
    simpa only [intervalIntegral.integral_zero] using he
  have hfirst : (∫ s in 0..T0,M (P (t-s))*deriv P s)=
      M (h*f x)*(h-1)-upperErrorOne M u f h T0 τ x := by
    rw [← initial_memory_error_identity M u f h T0 τ x hM hu hfC1 huT hT0]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne T0] with s hs hsI
    rw [uIoc_of_le hT0] at hsI
    have hsIcc : s∈Icc 0 T0 := ⟨hsI.1.le,hsI.2⟩
    have hsT : s<T0 := lt_of_le_of_ne hsI.2 hs
    change M (upperPatch u h T0 T1 τ f (t-s))*deriv (upperPatch u h T0 T1 τ f) s=
      M (h*f (max (x-s/τ) 0))*deriv u s
    rw [upperPatch_initial_memory_value u f h T0 T1 τ t s hT0 hT1 hτ huT hf.initial ht hsIcc]
    rw [upperPatch,joinAt_deriv_left T0 u _ s hsT]
  have htail : (∫ s in T1..t,M (P (t-s))*deriv P s)=
      h*causalConvolution (fun z => M (P (τ*z))) (deriv f) x := by
    rw [← lower_tail_memory_substitution M P f h T1 τ t hτ]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hsI
    rw [uIoc_of_le ht.le] at hsI
    change M (P (t-s))*deriv (upperPatch u h T0 T1 τ f) s=
      M (P (t-s))*((h/τ)*deriv f ((s-T1)/τ))
    rw [upperPatch_deriv_tail u f h T0 T1 τ s hfC1 hτ hT01 hsI.1]
  have htailError := tail_memory_error_identity M P f h τ x hM hP hf hτ hx0.le
  unfold profileResidual
  rw [upperPatch_deriv_tail u f h T0 T1 τ t hfC1 hτ hT01 ht,upperPatch_tail_value u f h T0 T1 τ t hT01 ht]
  change (h/τ)*deriv f x+h*f x+(∫ s in 0..t,M (P (t-s))*deriv P s)=_
  rw [← hsplit1,← hsplit0,hplateau,add_zero,hfirst,htail,htailError]
  unfold generalIdealResidual
  ring

end
end SphericalAging.StationaryUpperResidual
