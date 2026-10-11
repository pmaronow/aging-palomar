module

public import SphericalAging.StationaryConvolutionDerivative
public import SphericalAging.StationaryShiftCosts

public section

/-! Genuine midpoint differentiation and uniform bounds for higher causal
convolutions, including powers with exponent at or beyond integrability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.MidpointConvolutionDerivative
open StationaryNormalization StationaryConvolutionDerivative StationaryPowerProfiles

/-- On a finite causal interval both a C1 function and its derivative are continuous. -/
theorem c1_function_on_interval {F F' : ℝ → ℝ} (h : C1Input F F') {t : ℝ} :
    ContinuousOn F (Icc 0 t) :=
  h.continuousOn.mono (fun x hs => by show -1 < x; linarith [hs.1])

theorem c1_derivative_on_interval {F F' : ℝ → ℝ} (h : C1Input F F') {t : ℝ} :
    ContinuousOn F' (Icc 0 t) :=
  h.derivative_continuous.mono (fun x hs => by show -1 < x; linarith [hs.1])

/-- The midpoint derivative formula is obtained from the actual convolution
and genuine integration by parts; it is not a premise. -/
theorem midpoint_derivative_identity {F F' G G' : ℝ → ℝ}
    (hF : C1Input F F') (hG : C1Input G G') {t : ℝ} (ht : 0 ≤ t) :
    deriv (causalConvolution F G) t=F (t/2)*G (t/2)+
      (∫ s in (0 : ℝ)..t/2,F' (t-s)*G s)+
      (∫ s in (0 : ℝ)..t/2,F s*G' (t-s)) := by
  have hh : 0 ≤ t/2 := by linarith
  have hht : t/2 ≤ t := by linarith
  have hmap : MapsTo (fun s : ℝ => t-s) (Icc 0 t) (Icc 0 t) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have hsub : ContinuousOn (fun s : ℝ => t-s) (Icc 0 t) := by fun_prop
  have hf := c1_function_on_interval hF (t := t)
  have hg := c1_function_on_interval hG (t := t)
  have hfp := c1_derivative_on_interval hF (t := t)
  have hgp := c1_derivative_on_interval hG (t := t)
  have hA : ContinuousOn (fun s => F' (t-s)*G s) (Icc 0 t) := (hfp.comp hsub hmap).mul hg
  have hB : ContinuousOn (fun s => F (t-s)*G' s) (Icc 0 t) := (hf.comp hsub hmap).mul hgp
  have hA0 : IntervalIntegrable (fun s => F' (t-s)*G s) volume 0 (t/2) :=
    (hA.mono (Icc_subset_Icc le_rfl hht)).intervalIntegrable_of_Icc hh
  have hB0 : IntervalIntegrable (fun s => F (t-s)*G' s) volume 0 (t/2) :=
    (hB.mono (Icc_subset_Icc le_rfl hht)).intervalIntegrable_of_Icc hh
  have hB1 : IntervalIntegrable (fun s => F (t-s)*G' s) volume (t/2) t :=
    (hB.mono (Icc_subset_Icc hh le_rfl)).intervalIntegrable_of_Icc hht
  have hd (s : ℝ) (hs : s ∈ uIcc 0 (t/2)) :
      HasDerivAt (fun s => F (t-s)*G s) (-F' (t-s)*G s+F (t-s)*G' s) s := by
    rw [uIcc_of_le hh] at hs
    have hts : -1 < t-s := by linarith [hs.2]
    have hs0 : -1 < s := by linarith [hs.1]
    have h := ((hF.derivative (t-s) hts).comp s ((hasDerivAt_id s).const_sub t)).mul (hG.derivative s hs0)
    convert h using 1
    · rfl
    · simp only [Function.comp_apply]
      ring
  have hneg : IntervalIntegrable (fun s => -F' (t-s)*G s) volume 0 (t/2) := by
    convert hA0.neg using 1
    funext s
    simp only [Pi.neg_apply,neg_mul]
  have hprime : IntervalIntegrable (fun s => -F' (t-s)*G s+F (t-s)*G' s) volume 0 (t/2) := by
    convert hneg.add hB0 using 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hprime
  change (∫ s in 0..t/2,-F' (t-s)*G s+F (t-s)*G' s)=F (t-t/2)*G (t/2)-F (t-0)*G 0 at hFTC
  rw [intervalIntegral.integral_add (f := fun s => -F' (t-s)*G s) (g := fun s => F (t-s)*G' s)
    hneg hB0] at hFTC
  have hn : (∫ s in 0..t/2,-F' (t-s)*G s)=-(∫ s in 0..t/2,F' (t-s)*G s) := by
    simpa only [neg_mul] using (intervalIntegral.integral_neg (f := fun s => F' (t-s)*G s) (a := 0) (b := t/2) (μ := volume))
  rw [hn,show t-t/2=t/2 by ring,sub_zero] at hFTC
  have hreflect : (∫ s in t/2..t,F (t-s)*G' s)=∫ s in 0..t/2,F s*G' (t-s) := by
    have he := intervalIntegral.integral_comp_sub_left (fun s => F s*G' (t-s)) t (a := t/2) (b := t)
    simpa only [sub_sub_cancel,sub_self,show t-t/2=t/2 by ring] using he
  rw [(causal_convolution_hasDerivAt F F' G G' hF hG t ht).deriv]
  unfold causalConvolution
  rw [←intervalIntegral.integral_add_adjacent_intervals hB0 hB1,hreflect]
  linarith only [hFTC]

/-- Actual antiderivative estimate for every shifted power below exponent one. -/
theorem shifted_power_mass_bound {c X t : ℝ} (hc : c < 1) (hX : 0 ≤ X) (hXt : X ≤ t) :
    (∫ s in (0 : ℝ)..X,(1+s)^(-c)) ≤ (1+t)^(1-c)/(1-c) := by
  have hd (s : ℝ) (hs : s ∈ uIcc 0 X) :
      HasDerivAt (fun s : ℝ => (1+s)^(1-c)/(1-c)) ((1+s)^(-c)) s := by
    rw [uIcc_of_le hX] at hs
    have hh := (((hasDerivAt_id s).const_add 1).rpow_const (p := 1-c)
      (Or.inl (show 1+s ≠ 0 by linarith [hs.1]))).div_const (1-c)
    convert hh using 1
    · rfl
    · simp only [id_eq,one_mul]
      rw [show 1-c-1=-c by ring]
      field_simp [ne_of_gt (sub_pos.mpr hc)]
  have hi : IntervalIntegrable (fun s : ℝ => (1+s)^(-c)) volume 0 X := by
    exact ((shiftedPower_contDiffOn c).continuousOn.mono (by
      rw [uIcc_of_le hX]
      exact Icc_subset_Ici_self)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [he]
  simp only [add_zero,Real.one_rpow]
  have hpow := Real.rpow_le_rpow (by linarith : 0 ≤ 1+X) (by linarith : 1+X ≤ 1+t)
    (sub_pos.mpr hc).le
  have hh := div_le_div_of_nonneg_right hpow (sub_pos.mpr hc).le
  linarith [div_pos (by norm_num : (0 : ℝ) < 1) (sub_pos.mpr hc)]

theorem half_base_power {x b : ℝ} (hx : 0 ≤ x) :
    (x/2)^(-b)=(2 : ℝ)^b*x^(-b) := by
  have hh := StationaryShiftCosts.half_base_rpow x (b-1) hx
  rw [show -(b-1)-1=-b by ring,show b-1+1=b by ring] at hh
  exact hh

/-- Generic half-interval product estimate. One factor is kept at the short
argument and the other differentiated factor is evaluated at the long argument. -/
theorem half_integral_product_bound {F H : ℝ → ℝ} {AF AH c b t : ℝ}
    (hF : ContinuousOn F (Ici 0)) (hH : ContinuousOn H (Ici 0))
    (hAF : 0 ≤ AF) (hAH : 0 ≤ AH) (hc : c < 1) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hFb : ∀ s ≥ 0,|F s| ≤ AF*(1+s)^(-c))
    (hHb : ∀ s ≥ 0,|H s| ≤ AH*(1+s)^(-b)) :
    |∫ s in (0 : ℝ)..t/2,F s*H (t-s)| ≤
      (AF*AH*(2 : ℝ)^b/(1-c))*(1+t)^(1-c-b) := by
  have hh : 0 ≤ t/2 := by linarith
  have hmap : MapsTo (fun s : ℝ => t-s) (Icc 0 (t/2)) (Ici 0) := by
    intro s hs
    change 0 ≤ t-s
    linarith [hs.2]
  have hi : IntervalIntegrable (fun s => F s*H (t-s)) volume 0 (t/2) :=
    ((hF.mono Icc_subset_Ici_self).mul (hH.comp (by fun_prop) hmap)).intervalIntegrable_of_Icc hh
  have hpower : IntervalIntegrable (fun s : ℝ => (1+s)^(-c)) volume 0 (t/2) :=
    ((shiftedPower_contDiffOn c).continuousOn.mono (by
      rw [uIcc_of_le hh]
      exact Icc_subset_Ici_self)).intervalIntegrable
  let K := AF*AH*(2 : ℝ)^b*(1+t)^(-b)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbound (s : ℝ) (hs : s ∈ Icc 0 (t/2)) :
      |F s*H (t-s)| ≤ K*(1+s)^(-c) := by
    have hlong := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (1+t)/2)
      (by linarith [hs.2] : (1+t)/2 ≤ 1+(t-s)) (neg_nonpos.mpr hb)
    rw [half_base_power (show 0 ≤ 1+t by linarith)] at hlong
    have hHlong := (hHb (t-s) (by linarith [hs.2])).trans (mul_le_mul_of_nonneg_left hlong hAH)
    rw [abs_mul]
    have hx := mul_le_mul (hFb s hs.1) hHlong (abs_nonneg _) (mul_nonneg hAF (Real.rpow_nonneg (by linarith [hs.1] : 0 ≤ 1+s) _))
    dsimp only [K]
    nlinarith only [hx]
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s => F s*H (t-s)) hh
  have hm := intervalIntegral.integral_mono_on hh hi.norm (hpower.const_mul K)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s hs)
  rw [intervalIntegral.integral_const_mul] at hm
  have hmass := shifted_power_mass_bound hc hh (show t/2 ≤ t by linarith)
  have hmK := mul_le_mul_of_nonneg_left hmass hK
  have hresult : |∫ s in (0 : ℝ)..t/2,F s*H (t-s)| ≤ K*((1+t)^(1-c)/(1-c)) := by
    simpa only [Real.norm_eq_abs] using (hn.trans hm).trans hmK
  have he : K*((1+t)^(1-c)/(1-c))=
      (AF*AH*(2 : ℝ)^b/(1-c))*(1+t)^(1-c-b) := by
    dsimp only [K]
    have hp : (1+t)^(-b)*(1+t)^(1-c)=(1+t)^(1-c-b) := by
      rw [←Real.rpow_add (by linarith : 0 < 1+t)]
      congr 1
      ring
    calc
      _ = (AF*AH*(2 : ℝ)^b/(1-c))*((1+t)^(-b)*(1+t)^(1-c)) := by ring
      _ = _ := by rw [hp]
  exact hresult.trans_eq he

theorem c1_function_on_ray {F F' : ℝ → ℝ} (h : C1Input F F') : ContinuousOn F (Ici 0) :=
  h.continuousOn.mono (fun x hx => by show -1 < x; change 0 ≤ x at hx; linarith)

theorem c1_derivative_on_ray {F F' : ℝ → ℝ} (h : C1Input F F') : ContinuousOn F' (Ici 0) :=
  h.derivative_continuous.mono (fun x hx => by show -1 < x; change 0 ≤ x at hx; linarith)

theorem midpoint_power_bound {t e : ℝ} (ht : 0 ≤ t) (he : 0 ≤ e) :
    (1+t/2)^(-e) ≤ (2 : ℝ)^e*(1+t)^(-e) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (1+t)/2)
    (by linarith : (1+t)/2 ≤ 1+t/2) (neg_nonpos.mpr he)
  rw [half_base_power (show 0 ≤ 1+t by linarith)] at hh
  exact hh

/-- One common bound covers every high power, including alpha=1 and alpha>1. -/
@[expose] def midpointConstant (AF BF AG BG a α : ℝ) :=
  AF*AG*(2 : ℝ)^(α+a)+AF*BG*(2 : ℝ)^(a+1)/(1-2*a)+BF*AG*(2 : ℝ)^(α+1)/(1-a)

theorem midpoint_convolution_derivative_bound {F F' G G' : ℝ → ℝ}
    (hF : C1Input F F') (hG : C1Input G G') {AF BF AG BG a α : ℝ}
    (hAF : 0 ≤ AF) (hBF : 0 ≤ BF) (hAG : 0 ≤ AG) (hBG : 0 ≤ BG)
    (ha0 : 0 < a) (ha1 : a < 1/2) (hα : 2*a ≤ α)
    (hFb : ∀ s ≥ 0,|F s| ≤ AF*(1+s)^(-α))
    (hFpb : ∀ s ≥ 0,|F' s| ≤ BF*(1+s)^(-α-1))
    (hGb : ∀ s ≥ 0,|G s| ≤ AG*(1+s)^(-a))
    (hGpb : ∀ s ≥ 0,|G' s| ≤ BG*(1+s)^(-a-1)) :
    0 ≤ midpointConstant AF BF AG BG a α ∧ ∀ t ≥ 0,
      |deriv (causalConvolution F G) t| ≤
        midpointConstant AF BF AG BG a α*(1+t)^(-3*a) := by
  have hα0 : 0 ≤ α := by linarith
  have hden1 : 0 < 1-2*a := by linarith
  have hden2 : 0 < 1-a := by linarith
  refine ⟨by unfold midpointConstant; positivity,?_⟩
  intro t ht
  have hshort (s : ℝ) (hs : 0 ≤ s) : |F s| ≤ AF*(1+s)^(-(2*a)) := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1+s)
      (by linarith : -α ≤ -(2*a))
    exact (hFb s hs).trans (mul_le_mul_of_nonneg_left hp hAF)
  have hI1 := half_integral_product_bound (c1_function_on_ray hF) (c1_derivative_on_ray hG)
    hAF hBG (by linarith : 2*a < 1) (by linarith : 0 ≤ a+1) ht hshort
    (fun s hs => by simpa only [show -a-1=-(a+1) by ring] using hGpb s hs)
  rw [show 1-2*a-(a+1)=-3*a by ring] at hI1
  have hI2 := half_integral_product_bound (c1_function_on_ray hG) (c1_derivative_on_ray hF)
    hAG hBF (by linarith : a < 1) (by linarith : 0 ≤ α+1) ht hGb
    (fun s hs => by simpa only [show -α-1=-(α+1) by ring] using hFpb s hs)
  rw [show 1-a-(α+1)=-α-a by ring] at hI2
  have hpower : (1+t)^(-α-a) ≤ (1+t)^(-3*a) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1+t) (by linarith)
  have hI2final : |∫ s in (0 : ℝ)..t/2,F' (t-s)*G s| ≤
      (BF*AG*(2 : ℝ)^(α+1)/(1-a))*(1+t)^(-3*a) := by
    have he : (∫ s in (0 : ℝ)..t/2,F' (t-s)*G s)=∫ s in (0 : ℝ)..t/2,G s*F' (t-s) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact mul_comm _ _
    rw [he]
    exact hI2.trans (by
      have hh := mul_le_mul_of_nonneg_left hpower
        (show 0 ≤ AG*BF*(2 : ℝ)^(α+1)/(1-a) by positivity)
      convert hh using 1
      ring)
  have hboundary : |F (t/2)*G (t/2)| ≤
      (AF*AG*(2 : ℝ)^(α+a))*(1+t)^(-3*a) := by
    have hhalf : 0 ≤ t/2 := by linarith
    have hf := (hFb (t/2) hhalf).trans
      (mul_le_mul_of_nonneg_left (midpoint_power_bound ht hα0) hAF)
    have hg := (hGb (t/2) hhalf).trans
      (mul_le_mul_of_nonneg_left (midpoint_power_bound ht ha0.le) hAG)
    have hmul := mul_le_mul hf hg (abs_nonneg _) (by positivity : 0 ≤ AF*((2 : ℝ)^α*(1+t)^(-α)))
    have he : (AF*((2 : ℝ)^α*(1+t)^(-α)))*(AG*((2 : ℝ)^a*(1+t)^(-a)))=
        (AF*AG*(2 : ℝ)^(α+a))*(1+t)^(-α-a) := by
      calc
        _ = AF*AG*((2 : ℝ)^α*(2 : ℝ)^a)*((1+t)^(-α)*(1+t)^(-a)) := by ring
        _ = _ := by
          rw [←Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ←Real.rpow_add (by linarith : 0 < 1+t)]
          congr 1
    rw [he] at hmul
    rw [abs_mul]
    exact hmul.trans (mul_le_mul_of_nonneg_left hpower (by positivity))
  rw [midpoint_derivative_identity hF hG ht]
  have htri := (abs_add_le (F (t/2)*G (t/2)+(∫ s in (0 : ℝ)..t/2,F' (t-s)*G s))
    (∫ s in (0 : ℝ)..t/2,F s*G' (t-s))).trans
      (add_le_add (abs_add_le (F (t/2)*G (t/2)) (∫ s in (0 : ℝ)..t/2,F' (t-s)*G s)) le_rfl)
  unfold midpointConstant
  nlinarith only [htri,hboundary,hI1,hI2final]

/-- The same estimate in the manuscript's cubic shifted-profile notation. -/
theorem midpoint_convolution_cubic_profile_bound {F F' G G' : ℝ → ℝ}
    (hF : C1Input F F') (hG : C1Input G G') {AF BF AG BG a α : ℝ}
    (hAF : 0 ≤ AF) (hBF : 0 ≤ BF) (hAG : 0 ≤ AG) (hBG : 0 ≤ BG)
    (ha0 : 0 < a) (ha1 : a < 1/2) (hα : 2*a ≤ α)
    (hFb : ∀ s ≥ 0,|F s| ≤ AF*(1+s)^(-α))
    (hFpb : ∀ s ≥ 0,|F' s| ≤ BF*(1+s)^(-α-1))
    (hGb : ∀ s ≥ 0,|G s| ≤ AG*(1+s)^(-a))
    (hGpb : ∀ s ≥ 0,|G' s| ≤ BG*(1+s)^(-a-1)) :
    ∀ t ≥ 0,|deriv (causalConvolution F G) t| ≤
      midpointConstant AF BF AG BG a α*shiftedPower a t^3 := by
  intro t ht
  have hh := (midpoint_convolution_derivative_bound hF hG hAF hBF hAG hBG ha0 ha1 hα
    hFb hFpb hGb hGpb).2 t ht
  have he := StationaryPowerAsymptotics.shiftedPower_nat a t 3 (by linarith : -1 < t)
  dsimp only [shiftedPower] at he
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [shiftedPower]
  rw [←he]
  simpa only [neg_mul] using hh

end SphericalAging.MidpointConvolutionDerivative
