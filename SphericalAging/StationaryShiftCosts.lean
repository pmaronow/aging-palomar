module

public import SphericalAging.StationaryLowerEndpoint
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

/-! Actual shift and convolution error estimates for the upper comparison patch. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryShiftCosts
noncomputable section
open StationaryNormalization StationaryPowerProfiles

/-- Scaling a positive power by one half is handled exactly. -/
theorem half_base_rpow (x a : ℝ) (hx : 0≤x) :
    (x/2)^(-a-1)=(2:ℝ)^(a+1)*x^(-a-1) := by
  rw [Real.div_rpow hx (by norm_num),show -a-1=-(a+1) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤2) (a+1)]
  field_simp [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (a+1) |>.ne']

/-- The exact clipped-shift cost (16.7), uniform for every |eps|<=1/4. -/
theorem correctedPower_shift_cost (a ε δ x : ℝ) (ha : 0<a) (hε : |ε|≤1/4)
    (hδ0 : 0≤δ) (hδ1 : δ≤1) (hx : 0≤x) :
    0≤correctedPower a ε (max (x-δ) 0)-correctedPower a ε x ∧
      correctedPower a ε (max (x-δ) 0)-correctedPower a ε x≤
        ((5/4)*a*(2:ℝ)^(a+1))*δ*(1+x)^(-a-1) := by
  let y := max (x-δ) 0
  have hy0 : 0≤y := le_max_right _ _
  have hyx : y≤x := max_le (by linarith) hx
  have hxy : x-y≤δ := by have hh := le_max_left (x-δ) 0; dsimp [y]; linarith
  have hhalf : (1+x)/2≤1+y := by
    have h1 := le_max_left (x-δ) 0
    dsimp [y]
    linarith
  have hanti := (correctedPower_strictAntiOn a ε ha hε).antitoneOn hy0 hx hyx
  have hbound : ∀ z∈Ico y x,‖deriv (correctedPower a ε) z‖≤
      ((5/4)*a*(2:ℝ)^(a+1))*(1+x)^(-a-1) := by
    intro z hz
    have hz0 : 0≤z := hy0.trans hz.1
    have hb := (correctedPower_derivative_bounds a ε z ha hε hz0).2
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0<(1+x)/2)
      (by linarith [hz.1] : (1+x)/2≤1+z) (by linarith : -a-1≤0)
    rw [half_base_rpow (1+x) a (by linarith)] at hp
    have hc := mul_le_mul_of_nonneg_left hp (show 0≤(5/4)*a by positivity)
    rw [Real.norm_eq_abs]
    nlinarith only [hb,hc]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun z hz => (correctedPower_hasDerivAt a ε z (by linarith [hz.1,hy0])).differentiableAt.hasDerivAt.hasDerivWithinAt)
    hbound x ⟨hyx,le_rfl⟩
  rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hanti)] at hm
  have hC : 0≤((5/4)*a*(2:ℝ)^(a+1))*(1+x)^(-a-1) := by positivity
  have hc := mul_le_mul_of_nonneg_left hxy hC
  refine ⟨sub_nonneg.mpr hanti,?_⟩
  change correctedPower a ε y-correctedPower a ε x≤_
  nlinarith only [hm,hc]

/-- Finite shifted inverse-power mass, by an actual antiderivative. -/
theorem shifted_decay_integral_bound (a X : ℝ) (ha : 0<a) (hX : 0≤X) :
    (∫ s in 0..X,(1+s)^(-a-1))≤1/a := by
  have hd (s : ℝ) (hs : s∈uIcc 0 X) : HasDerivAt (fun s : ℝ => (1+s)^(-a)/(-a))
      ((1+s)^(-a-1)) s := by
    have hs0 : 0≤s := by simpa only [min_eq_left hX] using hs.1
    have hp := (((hasDerivAt_id s).const_add 1).rpow_const (p:=-a)
      (Or.inl (by change 1+s≠0; linarith))).div_const (-a)
    convert hp using 1
    · rfl
    · simp only [id_eq]
      field_simp [ha.ne']
  have hi : IntervalIntegrable (fun s : ℝ => (1+s)^(-a-1)) volume 0 X := by
    have hc : ContinuousOn (shiftedPower (a+1)) (uIcc 0 X) :=
      (shiftedPower_contDiffOn (a+1)).continuousOn.mono (by rw [uIcc_of_le hX]; exact Icc_subset_Ici_self)
    convert hc.intervalIntegrable (μ:=volume) using 1
    funext s
    unfold shiftedPower
    congr 1; ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [hf]
  simp only [add_zero,Real.one_rpow]
  have hp := Real.rpow_pos_of_pos (by linarith : 0<1+X) (-a)
  apply (le_div_iff₀ ha).mpr
  field_simp [ha.ne']
  nlinarith only [hp]


/-- The actual integrable-power convolution estimate used for upper-patch
memory errors, obtained by splitting and reflecting at the midpoint. -/
theorem shifted_decay_convolution_bound (a t : ℝ) (ha : 0<a) (ht : 0≤t) :
    causalConvolution (fun s => (1+s)^(-a-1)) (fun s => (1+s)^(-a-1)) t≤
      (2*(2:ℝ)^(a+1)/a)*(1+t)^(-a-1) := by
  let d := fun s : ℝ => (1+s)^(-a-1)
  let K := fun s : ℝ => d (t-s)*d s
  have hh : 0≤t/2 := by linarith
  have hht : t/2≤t := by linarith
  have hc : ContinuousOn K (uIcc 0 t) := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    have hs0 := hs.1
    have hts0 : 0≤t-s := by linarith [hs.2]
    have hdleft := (shiftedPower_hasDerivAt (a+1) (t-s) (by linarith)).continuousAt.comp_of_eq
      (show ContinuousAt (fun s : ℝ => t-s) s by fun_prop) rfl
    have hdright := (shiftedPower_hasDerivAt (a+1) s (by linarith)).continuousAt
    convert (hdleft.mul hdright).continuousWithinAt using 1
    funext y
    dsimp [K,d,shiftedPower]
    rw [show -(a+1)=-a-1 by ring]
  have hi : IntervalIntegrable K volume 0 t := hc.intervalIntegrable
  have hi0 := hi.mono (by rw [uIcc_of_le hh,uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hht) le_rfl
  have hi1 := hi.mono (by rw [uIcc_of_le hht,uIcc_of_le ht]; exact Icc_subset_Icc hh le_rfl) le_rfl
  have hmid : (∫ s in t/2..t,K s)=(∫ s in 0..t/2,K s) := by
    have he := intervalIntegral.integral_comp_sub_left K t (a:=t/2) (b:=t)
    rw [sub_self,show t-t/2=t/2 by ring] at he
    calc
      _ = ∫ s in t/2..t,K (t-s) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [K]
        rw [sub_sub_cancel]
        ring
      _ = _ := he
  have hsplit : (∫ s in 0..t,K s)=2*(∫ s in 0..t/2,K s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,hmid]
    ring
  have hid : IntervalIntegrable d volume 0 (t/2) := by
    have he := (shiftedPower_contDiffOn (a+1)).continuousOn.mono
      (show uIcc 0 (t/2)⊆Ici 0 by rw [uIcc_of_le hh]; exact Icc_subset_Ici_self)
    convert he.intervalIntegrable (μ:=volume) using 1
    funext s
    dsimp [d,shiftedPower]
    rw [show -(a+1)=-a-1 by ring]
  have hb : (∫ s in 0..t/2,K s)≤((2:ℝ)^(a+1)*d t)*(1/a) := by
    have he := intervalIntegral.integral_mono_on hh hi0 (hid.const_mul ((2:ℝ)^(a+1)*d t)) (fun s hs => ?_)
    · rw [intervalIntegral.integral_const_mul] at he
      exact he.trans (mul_le_mul_of_nonneg_left (shifted_decay_integral_bound a (t/2) ha hh) (by dsimp [d]; positivity))
    · have hhalf : (1+t)/2≤1+(t-s) := by linarith [hs.2]
      have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0<(1+t)/2) hhalf (by linarith : -a-1≤0)
      rw [half_base_rpow (1+t) a (by linarith)] at hp
      exact mul_le_mul_of_nonneg_right hp (Real.rpow_pos_of_pos (by linarith [hs.1] : 0<1+s) _).le
  unfold causalConvolution
  change (∫ s in 0..t,K s)≤_
  rw [hsplit]
  have he := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤2)
  dsimp [d] at he
  convert he using 1; ring

end
end SphericalAging.StationaryShiftCosts
