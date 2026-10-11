module

public import SphericalAging.StationaryDerivativeEnvelope
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public section

/-! The monotone density argument is proved by actual FTC secant bounds.
All signed-derivative asymptotics follow from an actual amplitude limit and
spectral complete monotonicity, without an asymptotic derivative hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.CompleteMonotoneDerivativeAsymptotics
open StationaryDerivativeEnvelope StationaryNormalization

@[expose] def powerScaled (F : ℝ → ℝ) (b t : ℝ) := t^b*F t

@[expose] def lowerSecant (F : ℝ → ℝ) (b k t : ℝ) :=
  (powerScaled F b t-k^(-b)*powerScaled F b (k*t))/(k-1)

@[expose] def upperSecant (F : ℝ → ℝ) (b k t : ℝ) :=
  (k^b*powerScaled F b (t/k)-powerScaled F b t)/(1-1/k)

@[expose] def lowerCoefficient (b A k : ℝ) := (A-k^(-b)*A)/(k-1)
@[expose] def upperCoefficient (b A k : ℝ) := (k^b*A-A)/(1-1/k)

theorem scaled_dilation_inverse (F : ℝ → ℝ) (b : ℝ) {k t : ℝ}
    (hk : 0<k) (ht : 0<t) :
    k^(-b)*powerScaled F b (k*t)=t^b*F (k*t) := by
  unfold powerScaled
  rw [Real.mul_rpow hk.le ht.le,Real.rpow_neg hk.le]
  have hn : k^b≠0 := (Real.rpow_pos_of_pos hk b).ne'
  field_simp

theorem scaled_division (F : ℝ → ℝ) (b : ℝ) {k t : ℝ}
    (hk : 0<k) (ht : 0<t) :
    k^b*powerScaled F b (t/k)=t^b*F (t/k) := by
  unfold powerScaled
  rw [Real.div_rpow ht.le hk.le]
  have hn : k^b≠0 := (Real.rpow_pos_of_pos hk b).ne'
  field_simp

/-- The lower secant bound is an actual consequence of FTC and monotonicity. -/
theorem lowerSecant_le_scaled_derivative (F G : ℝ → ℝ) (b : ℝ) {k t : ℝ}
    (hk : 1<k) (ht : 0<t) (hG : ContinuousOn G (Ioi 0))
    (hanti : AntitoneOn G (Ioi 0)) (hd : ∀ s>0,HasDerivAt F (-G s) s) :
    lowerSecant F b k t ≤ powerScaled G (b+1) t := by
  have hk0 : 0<k := by linarith
  have htk : t≤k*t := by nlinarith
  have hi : IntervalIntegrable G volume t (k*t) :=
    (hG.mono (by rw [uIcc_of_le htk]; exact fun u hu => ht.trans_le hu.1)).intervalIntegrable
  have hb := intervalIntegral.integral_mono_on htk hi
    (intervalIntegrable_const (c := G t)) (fun u hu => hanti ht (ht.trans_le hu.1) hu.1)
  rw [derivative_integral_difference F G t (k*t) ht htk hG hd,
    intervalIntegral.integral_const,smul_eq_mul] at hb
  unfold lowerSecant
  rw [scaled_dilation_inverse F b hk0 ht]
  apply (div_le_iff₀ (show 0<k-1 by linarith)).mpr
  unfold powerScaled
  rw [Real.rpow_add ht,Real.rpow_one]
  have hp := mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos ht b).le
  nlinarith only [hp]

/-- The upper secant bound is an actual consequence of FTC and monotonicity. -/
theorem scaled_derivative_le_upperSecant (F G : ℝ → ℝ) (b : ℝ) {k t : ℝ}
    (hk : 1<k) (ht : 0<t) (hG : ContinuousOn G (Ioi 0))
    (hanti : AntitoneOn G (Ioi 0)) (hd : ∀ s>0,HasDerivAt F (-G s) s) :
    powerScaled G (b+1) t ≤ upperSecant F b k t := by
  have hk0 : 0<k := by linarith
  have htk : t/k≤t := div_le_self ht.le hk.le
  have htk0 : 0<t/k := div_pos ht hk0
  have hi : IntervalIntegrable G volume (t/k) t :=
    (hG.mono (by rw [uIcc_of_le htk]; exact fun u hu => htk0.trans_le hu.1)).intervalIntegrable
  have hb := intervalIntegral.integral_mono_on htk
    (intervalIntegrable_const (c := G t)) hi (fun u hu => hanti (htk0.trans_le hu.1) ht hu.2)
  rw [derivative_integral_difference F G (t/k) t htk0 htk hG hd,
    intervalIntegral.integral_const,smul_eq_mul] at hb
  have hkInv : 1/k<1 := (div_lt_one hk0).mpr hk
  unfold upperSecant
  rw [scaled_division F b hk0 ht]
  apply (le_div_iff₀ (show 0<1-1/k by linarith)).mpr
  unfold powerScaled
  rw [Real.rpow_add ht,Real.rpow_one]
  have hp := mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos ht b).le
  simp only [div_eq_mul_inv,one_mul] at hp ⊢
  nlinarith only [hp]

/-- Each finite lower secant has the limit dictated by the predecessor amplitude. -/
theorem lowerSecant_tendsto {F : ℝ → ℝ} {b A k : ℝ} (hk : 0<k)
    (hF : Tendsto (powerScaled F b) atTop (nhds A)) :
    Tendsto (lowerSecant F b k) atTop (nhds (lowerCoefficient b A k)) :=
  (hF.sub ((hF.comp ((tendsto_const_mul_atTop_of_pos hk).mpr tendsto_id)).const_mul
    (k^(-b)))).div_const (k-1)

/-- Each finite upper secant has the limit dictated by the predecessor amplitude. -/
theorem upperSecant_tendsto {F : ℝ → ℝ} {b A k : ℝ} (hk : 0<k)
    (hF : Tendsto (powerScaled F b) atTop (nhds A)) :
    Tendsto (upperSecant F b k) atTop (nhds (upperCoefficient b A k)) :=
  (((hF.comp ((tendsto_div_const_atTop_of_pos hk).mpr tendsto_id)).const_mul (k^b)).sub
    hF).div_const (1-1/k)

/-- The lower secant coefficient tends to b*A as the dilation tends to one. -/
theorem lowerCoefficient_tendsto (b A : ℝ) :
    Tendsto (lowerCoefficient b A) (nhdsWithin 1 (Ioi 1)) (nhds (b*A)) := by
  have hd : HasDerivAt (fun k : ℝ => k^(-b)) (-b) 1 := by
    simpa only [Real.one_rpow,mul_one] using
      (Real.hasDerivAt_rpow_const (x := 1) (p := -b) (Or.inl one_ne_zero))
  have hh := (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 1)).const_mul (-A)
  convert hh using 1
  · funext k
    simp only [lowerCoefficient,slope_def_field,Real.one_rpow,div_eq_mul_inv]
    ring
  · congr 1
    ring

/-- The upper secant coefficient has the same limiting value. -/
theorem upperCoefficient_tendsto (b A : ℝ) :
    Tendsto (upperCoefficient b A) (nhdsWithin 1 (Ioi 1)) (nhds (b*A)) := by
  have hd : HasDerivAt (fun k : ℝ => k^b) b 1 := by
    simpa only [Real.one_rpow,mul_one] using
      (Real.hasDerivAt_rpow_const (x := 1) (p := b) (Or.inl one_ne_zero))
  have hs := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 1)
  have hi : Tendsto (fun k : ℝ => k) (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := hi.mul hs |>.const_mul A
  have he : (fun k : ℝ => A*(k*slope (fun z : ℝ => z^b) 1 k)) =ᶠ[nhdsWithin 1 (Ioi 1)]
      upperCoefficient b A := by
    filter_upwards [self_mem_nhdsWithin] with k hk
    change 1<k at hk
    have hk0 : k≠0 := ne_of_gt (show 0<k by linarith)
    have hk1 : k-1≠0 := ne_of_gt (show 0<k-1 by linarith)
    simp only [upperCoefficient,slope_def_field,Real.one_rpow]
    field_simp
  have hl := hh.congr' he
  simpa only [one_mul,mul_comm A b] using hl

/-- Actual monotone density theorem for an asymptotic power amplitude. -/
theorem monotone_density_step {F G : ℝ → ℝ} {b A : ℝ}
    (hG : ContinuousOn G (Ioi 0)) (hanti : AntitoneOn G (Ioi 0))
    (hd : ∀ t>0,HasDerivAt F (-G t) t)
    (hF : Tendsto (powerScaled F b) atTop (nhds A)) :
    Tendsto (powerScaled G (b+1)) atTop (nhds (b*A)) := by
  apply tendsto_order.mpr
  have hkE : ∀ᶠ k : ℝ in 𝓝[>] 1,1<k := self_mem_nhdsWithin
  constructor
  · intro l hl
    have he := (lowerCoefficient_tendsto b A).eventually (Ioi_mem_nhds hl)
    obtain ⟨k,hk,hkl⟩ := (hkE.and he).exists
    have hk0 : 0<k := by linarith
    have hs := (lowerSecant_tendsto hk0 hF).eventually (Ioi_mem_nhds hkl)
    filter_upwards [hs,eventually_gt_atTop (0 : ℝ)] with t htl ht
    exact htl.trans_le (lowerSecant_le_scaled_derivative F G b hk ht hG hanti hd)
  · intro u hu
    have he := (upperCoefficient_tendsto b A).eventually (Iio_mem_nhds hu)
    obtain ⟨k,hk,hku⟩ := (hkE.and he).exists
    have hk0 : 0<k := by linarith
    have hs := (upperSecant_tendsto hk0 hF).eventually (Iio_mem_nhds hku)
    filter_upwards [hs,eventually_gt_atTop (0 : ℝ)] with t htu ht
    exact (scaled_derivative_le_upperSecant F G b hk ht hG hanti hd).trans_lt htu


/-- The rising factorial appearing in every successive density asymptotic. -/
@[expose] def risingFactor (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (a+(n : ℝ))*risingFactor a n

theorem risingFactor_eq_prod (a : ℝ) (n : ℕ) :
    risingFactor a n=∏ j ∈ Finset.range n,(a+(j : ℝ)) := by
  induction n with
  | zero => simp [risingFactor]
  | succ n ih => rw [risingFactor,Finset.prod_range_succ,ih,mul_comm]

/-- A genuine consecutive-derivative induction, using the proved monotone
 density step at every order. -/
theorem all_order_density_asymptotics {F : ℕ → ℝ → ℝ} {a A : ℝ}
    (hcont : ∀ n,ContinuousOn (F n) (Ioi 0))
    (hanti : ∀ n,AntitoneOn (F n) (Ioi 0))
    (hd : ∀ n t,0<t → HasDerivAt (F n) (-F (n+1) t) t)
    (hAmp : Tendsto (powerScaled (F 0) a) atTop (nhds A)) (n : ℕ) :
    Tendsto (powerScaled (F n) (a+(n : ℝ))) atTop (nhds (A*risingFactor a n)) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero,risingFactor,mul_one] using hAmp
  | succ n ih =>
    have hh := monotone_density_step (hcont (n+1)) (hanti (n+1)) (hd n) ih
    convert hh using 1
    · congr 1
      push_cast
      ring
    · congr 1
      rw [risingFactor]
      ring

/-- Complete monotonicity supplies every monotonicity and FTC hypothesis,
so an actual normalized-profile amplitude limit yields all derivative limits. -/
theorem normalized_all_order_derivative_asymptotics (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) {a A : ℝ}
    (hAmp : Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (nhds A)) (n : ℕ) :
    Tendsto (fun t : ℝ => t^(a+(n : ℝ))*
      ((-1 : ℝ)^n*iteratedDeriv n (normalizedProfile q c) t))
      atTop (nhds (A*risingFactor a n)) := by
  apply all_order_density_asymptotics
    (F := signedDerivative (normalizedProfile q c))
  · intro n t ht
    exact (normalized_signedDerivative_hasDerivAt p β γ q c r h n t ht).continuousAt.continuousWithinAt
  · exact normalized_signedDerivative_antitone p β γ q c r h
  · exact normalized_signedDerivative_hasDerivAt p β γ q c r h
  · change Tendsto (fun t : ℝ => t^a*((-1 : ℝ)^0*iteratedDeriv 0 (normalizedProfile q c) t)) atTop (nhds A)
    simpa only [pow_zero,iteratedDeriv_zero,one_mul] using hAmp

/-- The same exact rising-factor coefficient, displayed as a finite product. -/
theorem normalized_all_order_derivative_asymptotics_product (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) {a A : ℝ}
    (hAmp : Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (nhds A)) (n : ℕ) :
    Tendsto (fun t : ℝ => t^(a+(n : ℝ))*
      ((-1 : ℝ)^n*iteratedDeriv n (normalizedProfile q c) t))
      atTop (nhds (A*(∏ j ∈ Finset.range n,(a+(j : ℝ))))) := by
  simpa only [risingFactor_eq_prod] using normalized_all_order_derivative_asymptotics p β γ q c r h hAmp n

end SphericalAging.CompleteMonotoneDerivativeAsymptotics
