module

public import SphericalAging.StationaryUpperResidual

public section

/-! The waiting plateau of the genuine upper comparison profile. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryUpperPlateau
noncomputable section
open StationaryNormalization StationaryComparison StationaryPatchedProfiles
  StationaryUpperResidual StationaryLowerResidual

/-- The plateau memory is controlled by the actual old memory at T0. -/
theorem upperPatch_plateau_residual_bound (M u f : ℝ → ℝ) (h T0 T1 τ t : ℝ)
    (hM : Continuous M) (hmono : MonotoneOn M (Icc 0 1))
    (hu : AdmissibleProfile u) (hf : AdmissibleProfile f)
    (huC1 : ContDiffOn ℝ 1 u (Ici 0)) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (huT : u T0=h) (hT0 : 0≤T0) (hT1 : T0≤T1) (hτ : 0<τ)
    (ht0 : T0<t) (ht1 : t<T1) :
    h+causalConvolution (M∘u) (deriv u) T0≤
      profileResidual M (upperPatch u h T0 T1 τ f) t := by
  let P := upperPatch u h T0 T1 τ f
  have ht : 0≤t := hT0.trans ht0.le
  have hP := upperPatch_admissible u f h T0 T1 τ hT0 hT1 hτ huC1 hfC1 hu hf huT
  have hi := memory_derivative_intervalIntegrable M P t ht hM (hP.locally_AC t ht)
  have hi0 := hi.mono (by rw [uIcc_of_le hT0,uIcc_of_le ht]; exact Icc_subset_Icc le_rfl ht0.le) le_rfl
  have hi1 := hi.mono (by rw [uIcc_of_le ht0.le,uIcc_of_le ht]; exact Icc_subset_Icc hT0 le_rfl) le_rfl
  have hiu := memory_derivative_intervalIntegrable M u T0 hT0 hM (hu.locally_AC T0 hT0)
  have hz : (∫ s in T0..t,M (P (t-s))*deriv P s)=0 := by
    have he : (∫ s in T0..t,M (P (t-s))*deriv P s)=(∫ s in T0..t,(0:ℝ)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      rw [uIoc_of_le ht0.le] at hs
      change M (P (t-s))*deriv (upperPatch u h T0 T1 τ f) s=0
      rw [upperPatch_deriv_plateau u f h T0 T1 τ s hs.1 (hs.2.trans_lt ht1),mul_zero]
    simpa only [intervalIntegral.integral_zero] using he
  have hfirst : (∫ s in 0..T0,M (P (t-s))*deriv P s)=(∫ s in 0..T0,M (P (t-s))*deriv u s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne T0] with s hs hsI
    rw [uIoc_of_le hT0] at hsI
    change M (P (t-s))*deriv (upperPatch u h T0 T1 τ f) s=_
    rw [upperPatch,joinAt_deriv_left T0 u _ s (lt_of_le_of_ne hsI.2 hs)]
  have hib : IntervalIntegrable (fun s => M (P (t-s))*deriv u s) volume 0 T0 := by
    apply (hu.locally_AC T0 hT0).intervalIntegrable_deriv.continuousOn_mul
    apply hM.comp_continuousOn
    apply (hP.locally_AC t ht).continuousOn.comp (by fun_prop)
    intro s hs
    rw [uIcc_of_le hT0] at hs
    rw [uIcc_of_le ht]
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hcomp := intervalIntegral.integral_mono_on hT0 hiu hib (fun s hs => ?_)
  · unfold profileResidual
    rw [upperPatch_deriv_plateau u f h T0 T1 τ t ht0 ht1]
    rw [upperPatch,joinAt_right T0 u _ t ht0,joinAt_left T1 _ _ t ht1.le]
    change h+causalConvolution (M∘u) (deriv u) T0≤0+h+(∫ s in 0..t,M (P (t-s))*deriv P s)
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,hz,add_zero,hfirst]
    simpa only [causalConvolution,Function.comp_apply,zero_add,add_zero,add_comm] using add_le_add_left hcomp h
  · have hs0 := hs.1
    have hsT := hs.2
    have harg0 : 0≤T0-s := by linarith
    have harg1 : 0≤t-s := by linarith
    have hargle : T0-s≤t-s := by linarith
    have hparg := hP.nonincreasing harg0 harg1 hargle
    have hpeq : P (T0-s)=u (T0-s) := by
      change upperPatch u h T0 T1 τ f (T0-s)=_
      rw [upperPatch,joinAt_left T0 u _ (T0-s) (by linarith)]
    change P (t-s)≤P (T0-s) at hparg
    rw [hpeq] at hparg
    have hm := hmono (hP.values (t-s) harg1) (hu.values (T0-s) harg0) hparg
    exact mul_le_mul_of_nonpos_right hm (antitoneOn_deriv_nonpos u hu.nonincreasing s hs0)

/-- The actual stationary residual vanishes pointwise at every positive time. -/
theorem normalized_profile_residual_exact (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (t : ℝ) (ht : 0<t) :
    profileResidual (normalizedMemory q (purePhi p (β^2) γ)) (normalizedProfile q c) t=0 := by
  let u := normalizedProfile q c
  let v := normalizedResponse q r
  let M := normalizedMemory q (purePhi p (β^2) γ)
  have hc : causalConvolution (M∘u) (deriv u) t=-causalConvolution (M∘u) v t := by
    unfold causalConvolution
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [uIoc_of_le ht.le] at hs
    have hd := normalized_profile_hasDerivAt p β γ q c r h s hs.1
    change M (u (t-s))*deriv u s=-(M (u (t-s))*v s)
    rw [hd.deriv]
    ring
  have hb := normalized_memory_response_balance p β γ q c r h t ht.le
  have hd := normalized_profile_hasDerivAt p β γ q c r h t ht
  unfold profileResidual
  change deriv u t+u t+causalConvolution (M∘u) (deriv u) t=0
  rw [hd.deriv,hc]
  change -v t+u t-(causalConvolution (fun s => M (u s)) v t)=0
  rw [hb]
  ring

/-- The whole genuine waiting plateau has a strictly positive residual. -/
theorem normalized_upperPatch_plateau_positive (p : ℕ) (β γ q : ℝ) (c r f : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (hscale T0 T1 τ t : ℝ)
    (hf : AdmissibleProfile f) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (huT : normalizedProfile q c T0=hscale) (hT0 : 0<T0) (hT1 : T0≤T1) (hτ : 0<τ)
    (ht0 : T0<t) (ht1 : t<T1) :
    0<profileResidual (normalizedMemory q (purePhi p (β^2) γ))
      (upperPatch (normalizedProfile q c) hscale T0 T1 τ f) t := by
  obtain ⟨hu,_⟩ := normalized_profile_admissible p β γ q c r h
  obtain ⟨_,hm,_,_⟩ := normalized_memory_properties p β γ q c r h
  have hb := upperPatch_plateau_residual_bound _ _ _ hscale T0 T1 τ t
    (normalized_memory_continuous p β γ q c r h) hm hu hf h.profile_C1 hfC1 huT hT0.le hT1 hτ ht0 ht1
  have hr := normalized_profile_residual_exact p β γ q c r h T0 hT0
  have hd := normalized_profile_hasDerivAt p β γ q c r h T0 hT0
  unfold profileResidual at hr
  rw [hd.deriv,huT] at hr
  have hv := h.response_positive T0 hT0.le
  linarith

end
end SphericalAging.StationaryUpperPlateau
