module

public import SphericalAging.StationaryUpperErrorBounds
public import SphericalAging.StationaryUpperPlateau

public section

/-! The genuine long-scale upper endpoint comparison profile. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryUpperEndpoint
noncomputable section
open StationaryNormalization StationaryComparison StationaryPatchedProfiles
  StationaryPowerProfiles StationaryUpperResidual StationaryShiftCosts
  StationaryUpperErrorBounds StationaryUpperPlateau StationaryLowerResidual
  StationaryCorrectedCriticalProfiles

/-- The derivative-scale decay is below the critical cubic scale. -/
theorem derivative_decay_le_cube (a x : ℝ) (ha : a<1/2) (hx : 0≤x) :
    (1+x)^(-a-1)≤shiftedPower a x^3 := by
  have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤1+x)
    (by linarith : -a-1≤3*(-a))
  unfold shiftedPower
  rw [mul_comm (3:ℝ) (-a),Real.rpow_mul (by linarith : 0≤1+x)] at hp
  rw [← Real.rpow_natCast ((1+x)^(-a)) 3]
  exact hp

/-- A single sufficiently long scale makes the actual entire upper tail
strictly positive, after both genuine memory costs have been estimated. -/
theorem exists_upper_tail_scale (M u : ℝ → ℝ) (L : ℝ≥0) (a ε h T0 T1 η : ℝ)
    (hM : Continuous M) (hM0 : M 0=0) (hmono : MonotoneOn M (Icc 0 1))
    (hL : LipschitzOnWith L M (Icc 0 1)) (hu : AdmissibleProfile u)
    (huC1 : ContDiffOn ℝ 1 u (Ici 0)) (ha0 : 0<a) (ha1 : a<1/2) (hε : |ε|≤1/4)
    (hh : 0<h) (hh1 : h≤1) (huT : u T0=h) (hT0 : 0≤T0) (hT1 : 2*T0≤T1) (hη : 0<η)
    (hI : ∀ x≥0,η*h^3*shiftedPower a x^3≤generalIdealResidual M h (correctedPower a ε) x) :
    ∃ τ : ℝ, 0<τ ∧ T1≤τ ∧ ∀ t>T1,
      0<profileResidual M (upperPatch u h T0 T1 τ (correctedPower a ε)) t := by
  let J := (5/4)*a
  let K := J*(2:ℝ)^(a+1)
  let D := 2*(2:ℝ)^(a+1)/a
  let C := J+(L:ℝ)*K*T0+M 1*K*T0+(L:ℝ)*h*K*J*D*T1
  have hT01 : T0≤T1 := by linarith
  have hT10 : 0≤T1 := hT0.trans hT01
  have hM1 : 0≤M 1 := by
    have hb := hmono (show (0:ℝ)∈Icc 0 1 by norm_num) (show (1:ℝ)∈Icc 0 1 by norm_num) (by norm_num)
    simpa only [hM0] using hb
  have hC : 0<C := by dsimp [C,K,J,D]; positivity
  let τ := max T1 (2*C/(η*h^2))+1
  have hτ : 0<τ := by dsimp [τ]; have hm := le_max_left T1 (2*C/(η*h^2)); linarith
  have hTτ : T1≤τ := by dsimp [τ]; have hm := le_max_left T1 (2*C/(η*h^2)); linarith
  have hCτ : (h/τ)*C≤η*h^3/2 := by
    have hb : 2*C/(η*h^2)≤τ := by dsimp [τ]; have hm := le_max_right T1 (2*C/(η*h^2)); linarith
    have hb' := (div_le_iff₀ (show 0<η*h^2 by positivity)).mp hb
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have he := (div_le_iff₀ hτ).mpr (show 2*h*C≤η*h^3*τ by nlinarith only [hb',hh])
    convert he using 1
    ring
  have hf := correctedPower_admissible a ε ha0 hε
  have hfC1 := correctedPower_contDiffOn a ε
  refine ⟨τ,hτ,hTτ,?_⟩
  intro t ht
  let x := (t-T1)/τ
  have hx : 0≤x := (div_pos (sub_pos.mpr ht) hτ).le
  have hdec := upperPatch_residual_decomposition M u (correctedPower a ε) h T0 T1 τ t
    hM hu hf huC1 hfC1 huT hT0 hT1 hτ ht
  have he1 := upper_error_one_bound M u L a ε h T0 τ x hM hL hu ha0 hε ⟨hh.le,hh1⟩ huT hT0 hτ (hT01.trans hTτ) hx
  have he2 := upper_error_two_bound M u L a ε h T0 T1 τ x hM hM0 hmono hL hu huC1 ha0 hε ⟨hh.le,hh1⟩ huT hT0 hT01 hτ hTτ hx
  have hd := (correctedPower_derivative_bounds a ε x ha0 hε hx).2
  rw [abs_of_neg (correctedPower_deriv_neg a ε x ha0 hε hx)] at hd
  have hdd := mul_le_mul_of_nonneg_left hd (div_pos hh hτ).le
  have hb : (h/τ)*deriv (correctedPower a ε) x+
      generalIdealResidual M h (correctedPower a ε) x-
        upperErrorOne M u (correctedPower a ε) h T0 τ x-
          upperErrorTwo M (upperPatch u h T0 T1 τ (correctedPower a ε)) (correctedPower a ε) h τ x≥
      η*h^3*shiftedPower a x^3-(h/τ)*C*(1+x)^(-a-1) := by
    have hi := hI x hx
    dsimp [C,K,J,D] at *
    have hreshape : (L:ℝ)*h*((5/4)*a*2^(a+1))*(T0/τ)*(1+x)^(-a-1)+
        (h*M 1*((5/4)*a*2^(a+1))*(T0/τ)+(L:ℝ)*h^2*((5/4)*a*2^(a+1))*((5/4)*a)*(2*2^(a+1)/a)*(T1/τ))*(1+x)^(-a-1)+
          (h/τ)*((5/4)*a)*(1+x)^(-a-1)=
      (h/τ)*((5/4)*a+(L:ℝ)*((5/4)*a*2^(a+1))*T0+M 1*((5/4)*a*2^(a+1))*T0+
        (L:ℝ)*h*((5/4)*a*2^(a+1))*((5/4)*a)*(2*2^(a+1)/a)*T1)*(1+x)^(-a-1) := by ring
    linarith only [hi,he1,he2,hdd,hreshape]
  have hpow := derivative_decay_le_cube a x ha1 hx
  have hcost := mul_le_mul_of_nonneg_left hpow (mul_pos (div_pos hh hτ) hC).le
  have hscale := mul_le_mul_of_nonneg_right hCτ (pow_pos (shiftedPower_pos a x hx) 3).le
  have hgap : 0<η*h^3*shiftedPower a x^3/2 := by
    have hg := shiftedPower_pos a x hx
    positivity
  rw [hdec]
  change 0<(h/τ)*deriv (correctedPower a ε) x+generalIdealResidual M h (correctedPower a ε) x-
    upperErrorOne M u (correctedPower a ε) h T0 τ x-
      upperErrorTwo M (upperPatch u h T0 T1 τ (correctedPower a ε)) (correctedPower a ε) h τ x
  nlinarith only [hb,hcost,hscale,hgap]


/-- The entire upper comparison profile is constructed from the stationary
solution and the proved corrected critical profile. -/
theorem exists_normalized_upper_patch (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ hscale T0 T1 τ ε : ℝ, 0<hscale ∧ 1≤T0 ∧ T1=2*T0 ∧ 0<τ ∧ T1≤τ ∧ |ε|≤1/4 ∧
      normalizedProfile q c T0=hscale ∧
      AdmissibleProfile (upperPatch (normalizedProfile q c) hscale T0 T1 τ (correctedPower a ε)) ∧
      (∀ᵐ t ∂volume,t∈Ici 0 → 0≤profileResidual (normalizedMemory q (purePhi p (β^2) γ))
        (upperPatch (normalizedProfile q c) hscale T0 T1 τ (correctedPower a ε)) t) := by
  obtain ⟨κ,η,h0,hprof⟩ := normalized_critical_corrected_profiles p β γ q a c r hp h ha0 ha1 hbalance
  have he := h.profile_limit.eventually (Iio_mem_nhds hprof.scale_positive)
  obtain ⟨T',hT'⟩ := eventually_atTop.mp he
  let T0 := max T' 1
  have hT0 : 1≤T0 := le_max_right _ _
  have hT00 : 0≤T0 := by linarith
  let T1 := 2*T0
  have hT1 : 2*T0≤T1 := le_rfl
  have hT01 : T0≤T1 := by dsimp [T1]; linarith
  let hscale := normalizedProfile q c T0
  have hh : 0<hscale := h.profile_positive T0 hT00
  have hh0 : hscale≤h0 := (hT' T0 (le_max_left _ _)).le
  have hh1 : hscale≤1 := hh0.trans hprof.scale_le_one
  let ε := κ*hscale
  have hε : |ε|≤1/4 := by
    dsimp [ε]
    rw [abs_of_pos (mul_pos hprof.correction_positive hh)]
    exact (mul_le_mul_of_nonneg_left hh0 hprof.correction_positive.le).trans hprof.correction_small
  let M := normalizedMemory q (purePhi p (β^2) γ)
  obtain ⟨hu,huRes⟩ := normalized_profile_admissible p β γ q c r h
  obtain ⟨hM0,hm,L,hL⟩ := normalized_memory_properties p β γ q c r h
  have hM := normalized_memory_continuous p β γ q c r h
  have hI : ∀ x≥0,η*hscale^3*shiftedPower a x^3≤generalIdealResidual M hscale (correctedPower a ε) x := by
    intro x hx
    change η*hscale^3*shiftedPower a x^3≤normalizedIdealResidual p β γ q hscale (correctedPower a ε) x
    rw [normalizedIdealResidual_eq p β γ q hscale c r _ hp h x]
    exact hprof.upper_residual hscale hh hh0 x hx
  obtain ⟨τ,hτ,hTτ,hTail⟩ := exists_upper_tail_scale M (normalizedProfile q c) L a ε hscale T0 T1 η
    hM hM0 hm hL hu h.profile_C1 ha0 ha1 hε hh hh1 rfl hT00 hT1 hprof.gap_positive hI
  have hf := correctedPower_admissible a ε ha0 hε
  have hfC1 := correctedPower_contDiffOn a ε
  have hP := upperPatch_admissible (normalizedProfile q c) (correctedPower a ε) hscale T0 T1 τ
    hT00 hT01 hτ h.profile_C1 hfC1 hu hf rfl
  refine ⟨hscale,T0,T1,τ,ε,hh,hT0,rfl,hτ,hTτ,hε,rfl,hP,?_⟩
  filter_upwards [volume.ae_ne T0,volume.ae_ne T1,huRes] with t ht0ne ht1ne hut ht
  change 0≤t at ht
  by_cases htt0 : t<T0
  · rw [upperPatch,joinAt_early_residual _ _ _ T0 t ht htt0,hut ht]
  · have ht0 : T0<t := lt_of_le_of_ne (le_of_not_gt htt0) (Ne.symm ht0ne)
    by_cases htt1 : t<T1
    · exact (normalized_upperPatch_plateau_positive p β γ q c r (correctedPower a ε) h hscale T0 T1 τ t
        hf hfC1 rfl (by linarith) hT01 hτ ht0 htt1).le
    · exact (hTail t (lt_of_le_of_ne (le_of_not_gt htt1) (Ne.symm ht1ne))).le

/-- The actual upper patch is bounded by a fixed shifted critical power at
all times, including both initial and waiting segments. -/
theorem upperPatch_power_upper_bound (u : ℝ → ℝ) (a ε h T0 T1 τ : ℝ)
    (ha : 0<a) (hε : |ε|≤1/4) (hh : 0≤h) (hT0 : 0≤T0) (hT1 : T0≤T1) (hτ : 0<τ)
    (hP : AdmissibleProfile (upperPatch u h T0 T1 τ (correctedPower a ε))) :
    ∃ A : ℝ, 0<A ∧ ∀ t≥0,upperPatch u h T0 T1 τ (correctedPower a ε) t≤A*shiftedPower a t := by
  let B := 1+T1+τ
  let A := (1+T1)^a+(5/4)*h*B^a
  have hT10 : 0≤T1 := hT0.trans hT1
  have hB : 0<B := by dsimp [B]; linarith
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro t ht
  by_cases htt : t≤T1
  · have hv := (hP.values t ht).2
    have hg := Real.rpow_le_rpow_of_nonpos (by linarith : 0<1+t) (by linarith : 1+t≤1+T1) (by linarith : -a≤0)
    have hp := mul_le_mul_of_nonneg_left hg (Real.rpow_pos_of_pos (by linarith : 0<1+T1) a).le
    have hid : (1+T1)^a*(1+T1)^(-a)=1 := by
      rw [← Real.rpow_add (by linarith : 0<1+T1),add_neg_cancel,Real.rpow_zero]
    rw [hid] at hp
    have hAA : (1+T1)^a≤A := by
      dsimp [A]
      exact le_add_of_nonneg_right (by positivity)
    have hgmul := mul_le_mul_of_nonneg_right hAA (shiftedPower_pos a t ht).le
    exact hv.trans (hp.trans hgmul)
  · have htT : T1<t := lt_of_not_ge htt
    rw [upperPatch_tail_value u (correctedPower a ε) h T0 T1 τ t hT1 htT]
    let x := (t-T1)/τ
    have hx : 0≤x := (div_pos (sub_pos.mpr htT) hτ).le
    have hf := mul_le_mul_of_nonneg_left (correctedPower_bounds a ε x ha.le hε hx).2 hh
    have hbase : 1+t≤B*(1+x) := by
      have hxt : τ*x=t-T1 := by dsimp [x]; field_simp [hτ.ne']
      have hBτ : τ≤B := by dsimp [B]; linarith
      have hBinit : 1+T1≤B := by dsimp [B]; linarith
      nlinarith only [hxt,hBτ,hBinit,hx]
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0<1+t) hbase (by linarith : -a≤0)
    rw [Real.mul_rpow hB.le (by linarith : 0≤1+x)] at hp
    have hs := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hB a).le
    have hid : B^a*B^(-a)=1 := by rw [← Real.rpow_add hB,add_neg_cancel,Real.rpow_zero]
    have hs' : shiftedPower a x≤B^a*shiftedPower a t := by
      unfold shiftedPower
      rw [← mul_assoc,hid,one_mul] at hs
      exact hs
    have hscale := mul_le_mul_of_nonneg_left hs' (show 0≤(5/4)*h by positivity)
    have hAA : (5/4)*h*B^a≤A := by
      dsimp [A]
      exact le_add_of_nonneg_left (by positivity)
    have hgmul := mul_le_mul_of_nonneg_right hAA (shiftedPower_pos a t ht).le
    change h*correctedPower a ε x≤A*shiftedPower a t
    nlinarith only [hf,hscale,hgmul]

/-- The complete upper half of Proposition16.7, from exact stationary inputs
and the selected exponent, with no assumed comparison profile or residual sign. -/
theorem normalized_critical_endpoint_upper_bound (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ A : ℝ, 0<A ∧ ∀ t≥0,normalizedProfile q c t≤A*(1+t)^(-a) := by
  obtain ⟨hscale,T0,T1,τ,ε,hh,hT0,hT1,hτ,hTτ,hε,huT,hP,hRes⟩ := exists_normalized_upper_patch p β γ q a c r hp h ha0 ha1 hbalance
  have hT00 : 0≤T0 := by linarith
  have hT01 : T0≤T1 := by rw [hT1]; linarith
  have hCompare := normalized_comparison_upper p β γ q c r _ h hP hRes
  obtain ⟨A,hA,hbound⟩ := upperPatch_power_upper_bound (normalizedProfile q c) a ε hscale T0 T1 τ
    ha0 hε hh.le hT00 hT01 hτ hP
  refine ⟨A,hA,?_⟩
  intro t ht
  exact (hCompare t ht).trans (hbound t ht)

end
end SphericalAging.StationaryUpperEndpoint
