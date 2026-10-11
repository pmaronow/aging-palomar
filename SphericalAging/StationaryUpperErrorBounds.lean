module

public import SphericalAging.StationaryUpperResidual

public section

/-! Actual quantitative upper-patch memory-error bounds. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryUpperErrorBounds
noncomputable section
open StationaryNormalization StationaryComparison StationaryPatchedProfiles
  StationaryPowerProfiles StationaryUpperResidual StationaryShiftCosts

/-- The local Lipschitz bound for the actual memory, with the ordered
argument difference preserved. -/
theorem memory_ordered_difference (M : ℝ → ℝ) (L : ℝ≥0) (hL : LipschitzOnWith L M (Icc 0 1))
    (y z : ℝ) (hy : y∈Icc 0 1) (hz : z∈Icc 0 1) (hyz : z≤y) :
    M y-M z≤(L:ℝ)*(y-z) := by
  have hl := hL.dist_le_mul y hy z hz
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyz)] at hl
  exact (le_abs_self _).trans hl

/-- The first actual upper-memory error has its source O(T0/tau) bound. -/
theorem upper_error_one_bound (M u : ℝ → ℝ) (L : ℝ≥0) (a ε h T0 τ x : ℝ)
    (hM : Continuous M) (hL : LipschitzOnWith L M (Icc 0 1))
    (hu : AdmissibleProfile u) (ha : 0<a) (hε : |ε|≤1/4)
    (hh : h∈Icc 0 1) (huT : u T0=h) (hT0 : 0≤T0) (hτ : 0<τ) (hTτ : T0≤τ) (hx : 0≤x) :
    upperErrorOne M u (correctedPower a ε) h T0 τ x≤
      (L:ℝ)*h*((5/4)*a*(2:ℝ)^(a+1))*(T0/τ)*(1+x)^(-a-1) := by
  have hh0 := hh.1
  let f := correctedPower a ε
  let C := (L:ℝ)*h*((5/4)*a*(2:ℝ)^(a+1))*(T0/τ)*(1+x)^(-a-1)
  have hf := correctedPower_admissible a ε ha hε
  have hui := (hu.locally_AC T0 hT0).intervalIntegrable_deriv.neg
  have hcont : ContinuousOn (fun s => M (h*f (max (x-s/τ) 0))-M (h*f x)) (uIcc 0 T0) :=
    (clipped_memory_continuousOn M f h τ x 0 T0 hM (correctedPower_contDiffOn a ε).continuousOn).sub continuousOn_const
  have hi := hui.continuousOn_mul hcont
  have hc := hui.const_mul C
  have he := intervalIntegral.integral_mono_on hT0 hi hc (fun s hs => ?_)
  · unfold upperErrorOne
    change (∫ s in 0..T0,(M (h*f (max (x-s/τ) 0))-M (h*f x))*(-deriv u s))≤_
    rw [intervalIntegral.integral_const_mul] at he
    change (∫ s in 0..T0,(M (h*f (max (x-s/τ) 0))-M (h*f x))*(-deriv u s))≤C*(∫ s in 0..T0,-deriv u s) at he
    rw [intervalIntegral.integral_neg,
      (hu.locally_AC T0 hT0).integral_deriv_eq_sub,huT,hu.initial] at he
    have hC : 0≤C := by dsimp [C]; positivity
    have hmass : -(h-1)≤1 := by linarith [hh.1]
    exact he.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass hC)
  · have hδ0 : 0≤s/τ := div_nonneg hs.1 hτ.le
    have hδ1 : s/τ≤1 := (div_le_one hτ).mpr (hs.2.trans hTτ)
    have hshift := correctedPower_shift_cost a ε (s/τ) x ha hε hδ0 hδ1 hx
    have hfx := hf.values x hx
    have hfy := hf.values (max (x-s/τ) 0) (mem_Ici.mpr (le_max_right _ _))
    have hargx : h*f x∈Icc 0 1 := ⟨mul_nonneg hh.1 hfx.1,(mul_le_mul_of_nonneg_left hfx.2 hh.1).trans (by simpa using hh.2)⟩
    have hargy : h*f (max (x-s/τ) 0)∈Icc 0 1 :=
      ⟨mul_nonneg hh.1 hfy.1,(mul_le_mul_of_nonneg_left hfy.2 hh.1).trans (by simpa using hh.2)⟩
    have hl := memory_ordered_difference M L hL _ _ hargy hargx
      (mul_le_mul_of_nonneg_left (sub_nonneg.mp hshift.1) hh.1)
    have hsτ := div_le_div_of_nonneg_right hs.2 hτ.le
    have hb : M (h*f (max (x-s/τ) 0))-M (h*f x)≤C := by
      have hs1 := mul_le_mul_of_nonneg_left hshift.2 (mul_nonneg L.coe_nonneg hh.1)
      have hs2 := mul_le_mul_of_nonneg_left hsτ
        (show 0≤(L:ℝ)*h*((5/4)*a*(2:ℝ)^(a+1))*(1+x)^(-a-1) by positivity)
      dsimp [C,f] at *
      nlinarith only [hl,hs1,hs2]
    exact mul_le_mul_of_nonneg_right hb (neg_nonneg.mpr (antitoneOn_deriv_nonpos u hu.nonincreasing s hs.1))


/-- The exact second upper-memory error has the two source costs: the
short initial interval and the clipped displacement of the tail. -/
theorem upper_error_two_bound (M u : ℝ → ℝ) (L : ℝ≥0) (a ε h T0 T1 τ x : ℝ)
    (hM : Continuous M) (hM0 : M 0=0) (hmono : MonotoneOn M (Icc 0 1))
    (hL : LipschitzOnWith L M (Icc 0 1)) (hu : AdmissibleProfile u)
    (huC1 : ContDiffOn ℝ 1 u (Ici 0)) (ha : 0<a) (hε : |ε|≤1/4)
    (hh : h∈Icc 0 1) (huT : u T0=h) (hT0 : 0≤T0) (hT1 : T0≤T1)
    (hτ : 0<τ) (hTτ : T1≤τ) (hx : 0≤x) :
    upperErrorTwo M (upperPatch u h T0 T1 τ (correctedPower a ε)) (correctedPower a ε) h τ x≤
      (h*M 1*((5/4)*a*(2:ℝ)^(a+1))*(T0/τ)+
        (L:ℝ)*h^2*((5/4)*a*(2:ℝ)^(a+1))*((5/4)*a)*(2*(2:ℝ)^(a+1)/a)*(T1/τ))*(1+x)^(-a-1) := by
  have hh0 := hh.1
  let f := correctedPower a ε
  let P := upperPatch u h T0 T1 τ f
  let d := fun z : ℝ => (1+z)^(-a-1)
  let J := (5/4)*a
  let K := J*(2:ℝ)^(a+1)
  let A := T0/τ
  let B := min x A
  let e := fun z : ℝ => (M (P (τ*z))-M (h*f z))*(-deriv f (x-z))
  have hf := correctedPower_admissible a ε ha hε
  have hfC1 := correctedPower_contDiffOn a ε
  have hP := upperPatch_admissible u f h T0 T1 τ hT0 hT1 hτ huC1 hfC1 hu hf huT
  have hT10 : 0≤T1 := hT0.trans hT1
  have hA0 : 0≤A := div_nonneg hT0 hτ.le
  have hA1 : A≤1 := (div_le_one hτ).mpr (hT1.trans hTτ)
  have hB0 : 0≤B := le_min hx hA0
  have hBx : B≤x := min_le_left _ _
  have hBA : B≤A := min_le_right _ _
  have hM1 : 0≤M 1 := by
    have he := hmono (show (0:ℝ)∈Icc 0 1 by norm_num) (show (1:ℝ)∈Icc 0 1 by norm_num) (by norm_num)
    simpa only [hM0] using he
  have hj0' (z : ℝ) (hz : 0≤z) : 0≤-deriv f z := neg_nonneg.mpr (antitoneOn_deriv_nonpos f hf.nonincreasing z hz)
  have hj (z : ℝ) (hz : 0≤z) : -deriv f z≤J*d z := by
    have hb := (correctedPower_derivative_bounds a ε z ha hε hz).2
    rw [abs_of_neg (correctedPower_deriv_neg a ε z ha hε hz)] at hb
    exact hb
  have hd : ContinuousOn d (uIcc 0 x) := by
    convert (shiftedPower_contDiffOn (a+1)).continuousOn.mono
      (show uIcc 0 x⊆Ici 0 by rw [uIcc_of_le hx]; exact Icc_subset_Ici_self) using 1
    funext z
    dsimp [d,shiftedPower]
    rw [show -(a+1)=-a-1 by ring]
  have hds : ContinuousOn (fun z => d (x-z)) (uIcc 0 x) := by
    apply hd.comp (by fun_prop)
    intro z hz
    rw [uIcc_of_le hx] at hz ⊢
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hdi := (hds.mul hd).intervalIntegrable (μ:=volume)
  have hji : IntervalIntegrable (fun z => -deriv f (x-z)) volume 0 x := by
    simpa only [f,Pi.neg_apply,sub_zero,sub_self] using (((hf.locally_AC x hx).intervalIntegrable_deriv.neg).comp_sub_left x).symm
  have hei : IntervalIntegrable e volume 0 x :=
    hji.continuousOn_mul ((scaled_memory_continuousOn M P τ x hM hP hτ hx).sub
      (ideal_memory_continuousOn M f h x hM hf hx))
  have hei0 := hei.mono (by rw [uIcc_of_le hB0,uIcc_of_le hx]; exact Icc_subset_Icc le_rfl hBx) le_rfl
  have hei1 := hei.mono (by rw [uIcc_of_le hBx,uIcc_of_le hx]; exact Icc_subset_Icc hB0 le_rfl) le_rfl
  have hearly : (∫ z in 0..B,e z)≤M 1*K*A*d x := by
    have hc : IntervalIntegrable (fun _ : ℝ => M 1*K*d x) volume 0 B := intervalIntegrable_const
    have hi := intervalIntegral.integral_mono_on hB0 hei0 hc (fun z hz => ?_)
    · rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
      have hm := mul_le_mul_of_nonneg_right hBA (show 0≤M 1*K*d x by dsimp [K,J,d]; positivity)
      nlinarith only [hi,hm]
    · have hz0 := hz.1
      have hzx : z≤x := hz.2.trans hBx
      have hz1 : z≤1 := hz.2.trans (hBA.trans hA1)
      have hzτ : 0≤τ*z := mul_nonneg hτ.le hz0
      have hpval := hP.values (τ*z) hzτ
      have hfval := hf.values z hz0
      have hfarg : h*f z∈Icc 0 1 := ⟨mul_nonneg hh.1 hfval.1,(mul_le_mul_of_nonneg_left hfval.2 hh.1).trans (by simpa using hh.2)⟩
      have hpm := hmono hpval (show (1:ℝ)∈Icc 0 1 by norm_num) hpval.2
      have hfm := hmono (show (0:ℝ)∈Icc 0 1 by norm_num) hfarg hfarg.1
      rw [hM0] at hfm
      have hdiff : M (P (τ*z))-M (h*f z)≤M 1 := by linarith
      have hpow := Real.rpow_le_rpow_of_nonpos (by linarith : 0<(1+x)/2)
        (by linarith : (1+x)/2≤1+(x-z)) (by linarith : -a-1≤0)
      rw [half_base_rpow (1+x) a (by linarith)] at hpow
      have hjb : -deriv f (x-z)≤K*d x := by
        have hs := mul_le_mul_of_nonneg_left hpow (show 0≤J by dsimp [J]; positivity)
        have hb := hj (x-z) (sub_nonneg.mpr hzx)
        dsimp [K,d] at *
        nlinarith only [hs,hb]
      dsimp [e]
      calc
        _ ≤ M 1*(-deriv f (x-z)) := mul_le_mul_of_nonneg_right hdiff (hj0' _ (sub_nonneg.mpr hzx))
        _ ≤ M 1*(K*d x) := mul_le_mul_of_nonneg_left hjb hM1
        _ = _ := by ring
  have hlate : (∫ z in B..x,e z)≤
      (L:ℝ)*h*K*(T1/τ)*J*(2*(2:ℝ)^(a+1)/a)*d x := by
    by_cases hxx : x≤A
    · rw [show B=x by exact min_eq_left hxx,intervalIntegral.integral_same]
      dsimp [K,J,d]
      positivity
    · have hAx : A≤x := le_of_not_ge hxx
      have hBe : B=A := min_eq_right hAx
      let C := (L:ℝ)*h*K*(T1/τ)*J
      have hC0 : 0≤C := by dsimp [C,K,J]; positivity
      have hci := hdi.const_mul C
      have hci1 := hci.mono (by rw [uIcc_of_le hBx,uIcc_of_le hx]; exact Icc_subset_Icc hB0 le_rfl) le_rfl
      have hi := intervalIntegral.integral_mono_on hBx hei1 hci1 (fun z hz => ?_)
      · rw [intervalIntegral.integral_const_mul] at hi
        have hn : 0≤ᵐ[volume.restrict (Ioc 0 x)] (fun z => d (x-z)*d z) := by
          apply (ae_restrict_iff' measurableSet_Ioc).mpr
          exact ae_of_all _ (fun z hz => by
            have hz0 := hz.1.le
            have hzx : 0≤x-z := by linarith [hz.2]
            change 0≤d (x-z)*d z
            dsimp [d]
            positivity)
        have hsub := intervalIntegral.integral_mono_interval hB0 hBx le_rfl hn hdi
        have he := mul_le_mul_of_nonneg_left hsub hC0
        have hconv := mul_le_mul_of_nonneg_left (shifted_decay_convolution_bound a x ha hx) hC0
        dsimp [C] at *
        exact hi.trans (he.trans (by simpa only [causalConvolution,d,mul_assoc] using hconv))
      · have hz0 : 0≤z := hB0.trans hz.1
        have hzx := hz.2
        have hzA : A≤z := by simpa only [hBe] using hz.1
        have hzτ : T0≤τ*z := by
          have he := (div_le_iff₀ hτ).mp hzA
          nlinarith only [he]
        have hp : P (τ*z)=h*f (max (z-T1/τ) 0) := by
          change upperPatch u h T0 T1 τ f (τ*z)=_
          rw [upperPatch_clipped_value u f h T0 T1 τ (τ*z) hT1 hτ huT hf.initial hzτ]
          rw [show (τ*z-T1)/τ=z-T1/τ by field_simp [hτ.ne']]
        have hδ0 : 0≤T1/τ := div_nonneg (hT0.trans hT1) hτ.le
        have hδ1 : T1/τ≤1 := (div_le_one hτ).mpr hTτ
        have hs := correctedPower_shift_cost a ε (T1/τ) z ha hε hδ0 hδ1 hz0
        have hfv := hf.values z hz0
        have hfy := hf.values (max (z-T1/τ) 0) (mem_Ici.mpr (le_max_right _ _))
        have hargx : h*f z∈Icc 0 1 := ⟨mul_nonneg hh.1 hfv.1,(mul_le_mul_of_nonneg_left hfv.2 hh.1).trans (by simpa using hh.2)⟩
        have hargy : h*f (max (z-T1/τ) 0)∈Icc 0 1 :=
          ⟨mul_nonneg hh.1 hfy.1,(mul_le_mul_of_nonneg_left hfy.2 hh.1).trans (by simpa using hh.2)⟩
        have hm := memory_ordered_difference M L hL _ _ hargy hargx
          (mul_le_mul_of_nonneg_left (sub_nonneg.mp hs.1) hh.1)
        have hdiff : M (P (τ*z))-M (h*f z)≤(L:ℝ)*h*K*(T1/τ)*d z := by
          rw [hp]
          have hb := mul_le_mul_of_nonneg_left hs.2 (mul_nonneg L.coe_nonneg hh.1)
          dsimp [K,J,d,f] at *
          nlinarith only [hm,hb]
        dsimp [e,C]
        calc
          _ ≤ ((L:ℝ)*h*K*(T1/τ)*d z)*(-deriv f (x-z)) := mul_le_mul_of_nonneg_right hdiff (hj0' _ (sub_nonneg.mpr hzx))
          _ ≤ ((L:ℝ)*h*K*(T1/τ)*d z)*(J*d (x-z)) :=
            mul_le_mul_of_nonneg_left (hj _ (sub_nonneg.mpr hzx)) (by dsimp [K,J,d]; positivity)
          _ = _ := by ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hei0 hei1
  unfold upperErrorTwo
  change h*(∫ z in 0..x,e z)≤_
  rw [← hsplit]
  have he := mul_le_mul_of_nonneg_left (add_le_add hearly hlate) hh.1
  dsimp [K,J,A,d] at he
  convert he using 1
  ring

end
end SphericalAging.StationaryUpperErrorBounds
