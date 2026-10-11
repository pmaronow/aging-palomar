module

public import SphericalAging.StationaryEndpointBounds

public section

/-! Genuine causal convolution derivatives for one-sided C1 profiles. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryRayConvolution
noncomputable section
open StationaryNormalization StationaryPatchedProfiles StationaryConvolutionDerivative

structure RayC1Input (F F' : ℝ → ℝ) : Prop where
  derivative : ∀ t≥0,HasDerivWithinAt F (F' t) (Ici 0) t
  derivative_continuous : ContinuousOn F' (Ici 0)

@[expose] def rayExtension (F F' : ℝ → ℝ) := joinAt 0 (fun t => F 0+F' 0*t) F
@[expose] def rayDerivativeExtension (F' : ℝ → ℝ) := joinAt 0 (fun _ => F' 0) F'

theorem rayExtension_nonnegative (F F' : ℝ → ℝ) (t : ℝ) (ht : 0≤t) :
    rayExtension F F' t=F t := by
  by_cases hz : t=0
  · subst t; simp [rayExtension,joinAt]
  · unfold rayExtension
    rw [joinAt_right 0 _ F t (lt_of_le_of_ne ht (Ne.symm hz))]

theorem rayDerivativeExtension_nonnegative (F' : ℝ → ℝ) (t : ℝ) (ht : 0≤t) :
    rayDerivativeExtension F' t=F' t := by
  by_cases hz : t=0
  · subst t; simp [rayDerivativeExtension,joinAt]
  · unfold rayDerivativeExtension
    rw [joinAt_right 0 _ F' t (lt_of_le_of_ne ht (Ne.symm hz))]

/-- The extension has the actual matched two-sided derivative at zero. -/
theorem rayExtension_hasDerivAt_zero (F F' : ℝ → ℝ) (hF : RayC1Input F F') :
    HasDerivAt (rayExtension F F') (F' 0) 0 := by
  have hr := (hF.derivative 0 le_rfl).congr
    (fun t ht => rayExtension_nonnegative F F' t ht) (rayExtension_nonnegative F F' 0 le_rfl)
  have hl0 : HasDerivAt (fun t : ℝ => F 0+F' 0*t) (F' 0) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_mul (F' 0)).const_add (F 0) using 1 <;> simp
  have hl : HasDerivWithinAt (rayExtension F F') (F' 0) (Iic 0) 0 := hl0.hasDerivWithinAt (s:=Iic 0) |>.congr
    (fun t ht => by unfold rayExtension; rw [joinAt_left 0 _ F t ht])
    (by simp [rayExtension,joinAt])
  have hu := hl.union hr
  simpa only [Iic_union_Ici,hasDerivWithinAt_univ] using hu

/-- The derivative extension is actually continuous across the initial point. -/
theorem rayDerivativeExtension_continuous (F' : ℝ → ℝ) (hF' : ContinuousOn F' (Ici 0)) :
    Continuous (rayDerivativeExtension F') := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have he : rayDerivativeExtension F'=ᶠ[𝓝 t] (fun _ => F' 0) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact joinAt_left 0 _ F' s hs.le
    exact continuousAt_const.congr_of_eventuallyEq he
  · subst t
    have hr := (hF' 0 (by simp)).congr (fun t ht => rayDerivativeExtension_nonnegative F' t ht)
      (rayDerivativeExtension_nonnegative F' 0 le_rfl)
    have hl : ContinuousWithinAt (rayDerivativeExtension F') (Iic 0) 0 := (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => F' 0) (Iic 0) 0).congr
      (fun t ht => by unfold rayDerivativeExtension; rw [joinAt_left 0 _ F' t ht])
      (by simp [rayDerivativeExtension,joinAt])
    simpa only [Iic_union_Ici,continuousWithinAt_univ] using hl.union hr
  · have he : rayDerivativeExtension F'=ᶠ[𝓝 t] F' := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact joinAt_right 0 _ F' s hs
    exact (hF'.continuousAt (Ici_mem_nhds ht)).congr_of_eventuallyEq he

/-- One-sided C1 data give a genuine ordinary C1 extension across zero. -/
theorem rayExtension_C1Input (F F' : ℝ → ℝ) (hF : RayC1Input F F') :
    C1Input (rayExtension F F') (rayDerivativeExtension F') := by
  refine ⟨?_,(rayDerivativeExtension_continuous F' hF.derivative_continuous).continuousOn⟩
  intro t _
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have he : rayExtension F F'=ᶠ[𝓝 t] (fun s => F 0+F' 0*s) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact joinAt_left 0 _ F s hs.le
    have hd : HasDerivAt (fun s : ℝ => F 0+F' 0*s) (F' 0) t := by
      convert ((hasDerivAt_id t).const_mul (F' 0)).const_add (F 0) using 1 <;> simp
    rw [rayDerivativeExtension,joinAt_left 0 _ F' t ht.le]
    exact hd.congr_of_eventuallyEq he
  · subst t
    rw [rayDerivativeExtension_nonnegative F' 0 le_rfl]
    exact rayExtension_hasDerivAt_zero F F' hF
  · have he : rayExtension F F'=ᶠ[𝓝 t] F := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact joinAt_right 0 _ F s hs
    rw [rayDerivativeExtension_nonnegative F' t ht.le]
    exact ((hF.derivative t ht.le).hasDerivAt (Ici_mem_nhds ht)).congr_of_eventuallyEq he

/-- Nonnegative-time causal convolution sees only the genuine ray data. -/
theorem rayExtension_convolution_eq (F F' G G' : ℝ → ℝ) (t : ℝ) (ht : 0≤t) :
    causalConvolution (rayExtension F F') (rayExtension G G') t=causalConvolution F G t := by
  unfold causalConvolution
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  change rayExtension F F' (t-s)*rayExtension G G' s=F (t-s)*G s
  rw [rayExtension_nonnegative F F' (t-s) (by linarith [hs.2]),rayExtension_nonnegative G G' s hs.1]

/-- The actual convolution derivative formula on positive times requires
only the manuscript's one-sided C1 input, with no negative-time regularity. -/
theorem ray_causal_convolution_hasDerivAt (F F' G G' : ℝ → ℝ)
    (hF : RayC1Input F F') (hG : RayC1Input G G') (t : ℝ) (ht : 0<t) :
    HasDerivAt (causalConvolution F G) (F t*G 0+causalConvolution F G' t) t := by
  have hd := causal_convolution_hasDerivAt (rayExtension F F') (rayDerivativeExtension F')
    (rayExtension G G') (rayDerivativeExtension G') (rayExtension_C1Input F F' hF)
    (rayExtension_C1Input G G' hG) t ht.le
  have hc : causalConvolution (rayExtension F F') (rayDerivativeExtension G') t=causalConvolution F G' t := by
    unfold causalConvolution
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.le] at hs
    change rayExtension F F' (t-s)*rayDerivativeExtension G' s=F (t-s)*G' s
    rw [rayExtension_nonnegative F F' (t-s) (by linarith [hs.2]),rayDerivativeExtension_nonnegative G' s hs.1]
  rw [rayExtension_nonnegative F F' t ht.le,rayExtension_nonnegative G G' 0 le_rfl,hc] at hd
  have he : causalConvolution F G=ᶠ[𝓝 t] causalConvolution (rayExtension F F') (rayExtension G G') := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (rayExtension_convolution_eq F F' G G' s hs.le).symm
  exact hd.congr_of_eventuallyEq he

/-- The normalized profile supplies every one-sided C1 datum needed above. -/
theorem normalized_profile_RayC1Input (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) :
    RayC1Input (normalizedProfile q c) (fun t => -normalizedResponse q r t) := by
  refine ⟨?_,h.response_continuous.neg⟩
  intro t ht
  have hd := ((h.profile_C1.differentiableOn (by norm_num)) t ht).hasDerivWithinAt
  rw [h.derivative t ht] at hd
  exact hd


/-- The same exact derivative at zero is a right derivative, as in the
manuscript; this avoids imposing behavior at negative times on u. -/
theorem ray_causal_convolution_hasDerivWithinAt (F F' G G' : ℝ → ℝ)
    (hF : RayC1Input F F') (hG : RayC1Input G G') (t : ℝ) (ht : 0≤t) :
    HasDerivWithinAt (causalConvolution F G) (F t*G 0+causalConvolution F G' t) (Ici 0) t := by
  have hd := causal_convolution_hasDerivAt (rayExtension F F') (rayDerivativeExtension F')
    (rayExtension G G') (rayDerivativeExtension G') (rayExtension_C1Input F F' hF)
    (rayExtension_C1Input G G' hG) t ht
  have hc : causalConvolution (rayExtension F F') (rayDerivativeExtension G') t=causalConvolution F G' t := by
    unfold causalConvolution
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    change rayExtension F F' (t-s)*rayDerivativeExtension G' s=F (t-s)*G' s
    rw [rayExtension_nonnegative F F' (t-s) (by linarith [hs.2]),rayDerivativeExtension_nonnegative G' s hs.1]
  rw [rayExtension_nonnegative F F' t ht,rayExtension_nonnegative G G' 0 le_rfl,hc] at hd
  exact hd.hasDerivWithinAt.congr
    (fun s hs => (rayExtension_convolution_eq F F' G G' s hs).symm)
    (rayExtension_convolution_eq F F' G G' t ht).symm


theorem RayC1Input.continuousOn {F F' : ℝ → ℝ} (hF : RayC1Input F F') :
    ContinuousOn F (Ici 0) := fun t ht => (hF.derivative t ht).continuousWithinAt

/-- Powers preserve the genuine one-sided C1 data. -/
theorem RayC1Input.pow {F F' : ℝ → ℝ} (hF : RayC1Input F F') (j : ℕ) :
    RayC1Input (fun t => F t^j) (fun t => (j:ℝ)*F t^(j-1)*F' t) := by
  exact ⟨fun t ht => (hF.derivative t ht).fun_pow j,
    (continuousOn_const.mul (hF.continuousOn.pow (j-1))).mul hF.derivative_continuous⟩


/-- The ordinary derivative of the genuine C1 extension agrees with the
manuscript's right convolution slope throughout the nonnegative ray. -/
theorem rayExtension_convolution_deriv_formula (F F' G G' : ℝ → ℝ)
    (hF : RayC1Input F F') (hG : RayC1Input G G') (t : ℝ) (ht : 0≤t) :
    deriv (causalConvolution (rayExtension F F') (rayExtension G G')) t=
      F t*G 0+causalConvolution F G' t := by
  have hd := causal_convolution_hasDerivAt (rayExtension F F') (rayDerivativeExtension F')
    (rayExtension G G') (rayDerivativeExtension G') (rayExtension_C1Input F F' hF)
    (rayExtension_C1Input G G' hG) t ht
  have hc : causalConvolution (rayExtension F F') (rayDerivativeExtension G') t=causalConvolution F G' t := by
    unfold causalConvolution
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    change rayExtension F F' (t-s)*rayDerivativeExtension G' s=F (t-s)*G' s
    rw [rayExtension_nonnegative F F' (t-s) (by linarith [hs.2]),rayDerivativeExtension_nonnegative G' s hs.1]
  rw [hd.deriv,rayExtension_nonnegative F F' t ht,rayExtension_nonnegative G G' 0 le_rfl,hc]

end
end SphericalAging.StationaryRayConvolution
