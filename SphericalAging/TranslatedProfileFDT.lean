module

public import SphericalAging.CKTranslatedFDT
public import SphericalAging.StationaryClusterInputs

public section

/-! FDT and stationary response are proved from the genuine translated
integral identity. No derivative or stationarity premise is supplied. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.TranslatedProfileFDT
open Set Filter MeasureTheory CKSpecification ResponseCompactness CKTranslatedFDT
open scoped Topology

@[expose] def correlationProfile (C : C(ℝ×ℝ,ℝ)) (t : ℝ) : ℝ := C (t,0)
@[expose] def responseProfile (R : C(CausalOffsets,ℝ)) (t : ℝ) : ℝ := responseExtension R (0,-t)

theorem correlationProfile_continuous (C : C(ℝ×ℝ,ℝ)) : Continuous (correlationProfile C) :=
  C.continuous.comp (continuous_id.prodMk continuous_const)

theorem responseProfile_continuous (R : C(CausalOffsets,ℝ)) : Continuous (responseProfile R) :=
  (responseExtension_continuous R).comp (continuous_const.prodMk continuous_id.neg)

theorem profile_integrated_fdt {C : C(ℝ×ℝ,ℝ)} {R : C(CausalOffsets,ℝ)}
    (hstat : ∀ x y,C (x,y)=C (|x-y|,0))
    (hint : ∀ x y,y≤x → (∫ u in y..x,responseExtension R (x,u))=1-C (x,y))
    {t : ℝ} (ht : 0≤t) :
    correlationProfile C t=1-(∫ u in (0:ℝ)..t,responseProfile R u) := by
  have hh := hint 0 (-t) (by linarith)
  rw [hstat 0 (-t)] at hh
  simp only [sub_neg_eq_add,zero_add,abs_of_nonneg ht] at hh
  have he : (∫ u in (0:ℝ)..t,responseProfile R u)=∫ u in -t..0,responseExtension R (0,u) := by
    unfold responseProfile
    simpa only [neg_zero] using
      intervalIntegral.integral_comp_neg (fun u => responseExtension R (0,u)) (a := 0) (b := t)
  rw [he]
  dsimp [correlationProfile]
  linarith only [hh]

theorem profile_fdt {C : C(ℝ×ℝ,ℝ)} {R : C(CausalOffsets,ℝ)}
    (hstat : ∀ x y,C (x,y)=C (|x-y|,0))
    (hint : ∀ x y,y≤x → (∫ u in y..x,responseExtension R (x,u))=1-C (x,y))
    {t : ℝ} (ht : 0≤t) :
    HasDerivWithinAt (correlationProfile C) (-responseProfile R t) (Ici 0) t := by
  have hr := responseProfile_continuous R
  have hp := intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
    hr.stronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  exact hp.const_sub 1 |>.hasDerivWithinAt.congr
    (fun u hu => profile_integrated_fdt hstat hint hu)
    (profile_integrated_fdt hstat hint ht)

theorem response_limit_stationary {C : C(ℝ×ℝ,ℝ)} {R : C(CausalOffsets,ℝ)}
    (hstat : ∀ x y,C (x,y)=C (|x-y|,0))
    (hint : ∀ x y,y≤x → (∫ u in y..x,responseExtension R (x,u))=1-C (x,y))
    {x y : ℝ} (hyx : y≤x) :
    responseExtension R (x,y)=responseProfile R (x-y) := by
  have hrow (v : ℝ) (hv : v≤x) :
      (∫ u in v..x,responseExtension R (x,u))=1-correlationProfile C (x-v) := by
    rw [hint x v hv,hstat x v,abs_of_nonneg (sub_nonneg.mpr hv)]
    rfl
  have hr : Continuous (fun u => responseExtension R (x,u)) :=
    (responseExtension_continuous R).comp (continuous_const.prodMk continuous_id)
  have hleft := intervalIntegral.integral_hasDerivAt_left (hr.intervalIntegrable y x)
    hr.stronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hright : HasDerivWithinAt (fun v => 1-correlationProfile C (x-v))
      (-responseProfile R (x-y)) (Iic x) y := by
    have hc := profile_fdt hstat hint (sub_nonneg.mpr hyx)
    have hv : MapsTo (fun v : ℝ => x-v) (Iic x) (Ici 0) := by
      intro v hv
      change v≤x at hv
      change 0≤x-v
      exact sub_nonneg.mpr hv
    have hh := hc.comp y ((hasDerivAt_id y).const_sub x).hasDerivWithinAt hv
    simpa only [neg_mul,neg_neg,mul_one,mul_neg_one,Function.comp_def] using hh.const_sub 1
  have hright' := hright.congr (fun v hv => hrow v hv) (hrow y hyx)
  have hu : UniqueDiffWithinAt ℝ (Iic x) y :=
    (uniqueDiffWithinAt_Iic y).mono (Iic_subset_Iic.mpr hyx)
  have he := hright'.derivWithin hu
  have hl := (hleft.hasDerivWithinAt (s := Iic x)).derivWithin hu
  rw [hl] at he
  linarith only [he]

end SphericalAging.TranslatedProfileFDT
