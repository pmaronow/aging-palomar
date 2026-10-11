module

public import SphericalAging.StationaryLowerResidual

public section

/-! Actual lower endpoint bound by a short-time comparison patch. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryLowerEndpoint
noncomputable section
open StationaryNormalization StationaryComparison StationaryPowerProfiles
  StationaryConvolutionDerivative StationaryPatchedProfiles StationaryLowerResidual
  StationaryCorrectedCriticalProfiles

theorem c1Input_of_contDiffOn (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Ioi (-1))) :
    C1Input f (deriv f) := by
  refine ⟨?_,hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)⟩
  intro t ht
  exact ((hf.differentiableOn (by norm_num)) t ht).differentiableAt (Ioi_mem_nhds ht) |>.hasDerivAt

theorem correctedPower_C2_open (a ε : ℝ) : ContDiffOn ℝ 2 (correctedPower a ε) (Ioi (-1)) := by
  have hc : ContDiffOn ℝ 2 (fun t : ℝ => 1+t) (Ioi (-1)) := (contDiff_const.add contDiff_id).contDiffOn
  have hg : ContDiffOn ℝ 2 (shiftedPower a) (Ioi (-1)) :=
    hc.rpow_const_of_ne (fun t ht => by change -1<t at ht; linarith)
  exact (contDiffOn_const.mul hg).sub (contDiffOn_const.mul (hg.pow 2))

/-- The ideal residual's compact maximum is justified by actual continuity. -/
theorem normalizedIdealResidual_continuousOn (p : ℕ) (β γ q a ε hscale : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) :
    ContinuousOn (normalizedIdealResidual p β γ q hscale (correctedPower a ε)) (Ici 0) := by
  let M := normalizedMemory q (purePhi p (β^2) γ)
  let f := correctedPower a ε
  have hf : ContDiffOn ℝ 1 f (Ioi (-1)) := (correctedPower_C2_open a ε).of_le (by norm_num)
  have hdf : ContDiffOn ℝ 1 (deriv f) (Ioi (-1)) := (correctedPower_C2_open a ε).deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hMexpr : M=(fun y => y+∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*y^(j+2)) := funext h.memory_expansion
  have hMcd : ContDiff ℝ 1 M := by rw [hMexpr]; fun_prop
  have hMf : ContDiffOn ℝ 1 (fun s => M (hscale*f s)) (Ioi (-1)) :=
    hMcd.comp_contDiffOn (contDiffOn_const.mul hf)
  have hconv : ContinuousOn (causalConvolution (fun s => M (hscale*f s)) (deriv f)) (Ici 0) := by
    intro t ht
    exact (causal_convolution_hasDerivAt _ _ _ _ (c1Input_of_contDiffOn _ hMf)
      (c1Input_of_contDiffOn _ hdf) t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Ici 0) := (correctedPower_contDiffOn a ε).continuousOn
  exact ((continuousOn_const.mul hfc).sub
    (continuousOn_const.mul (hMcd.continuous.comp_continuousOn (continuousOn_const.mul hfc)))).add
    (continuousOn_const.mul hconv)


/-- A compact actual residual maximum can be absorbed by an actual short
scale when the derivative is uniformly strictly negative there. -/
theorem exists_short_scale (h δ X : ℝ) (f I : ℝ → ℝ)
    (hh : 0<h) (hδ : 0<δ) (_hX : 0≤X) (hI : ContinuousOn I (Icc 0 X))
    (hfcompact : ∀ x∈Icc 0 X,deriv f x≤-δ)
    (hfnegative : ∀ x≥0,deriv f x≤0) (hItail : ∀ x≥X,I x≤0) :
    ∃ τ : ℝ, 0<τ ∧ ∀ x≥0,(h/τ)*deriv f x+I x≤0 := by
  obtain ⟨L,hL⟩ := isCompact_Icc.bddAbove_image hI
  let A := max L 0+1
  have hA : 0<A := by dsimp [A]; positivity
  let τ := h*δ/A
  have hτ : 0<τ := div_pos (mul_pos hh hδ) hA
  have hcoef : (h/τ)*δ=A := by dsimp [τ]; field_simp [hh.ne',hδ.ne',hA.ne']
  refine ⟨τ,hτ,?_⟩
  intro x hx
  by_cases hxx : x≤X
  · have hid := hL ⟨x,⟨hx,hxx⟩,rfl⟩
    have hfd := mul_le_mul_of_nonneg_left (hfcompact x ⟨hx,hxx⟩) (div_pos hh hτ).le
    rw [mul_neg,hcoef] at hfd
    dsimp [A] at hfd
    linarith only [hfd,hid,le_max_left L 0]
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (div_pos hh hτ).le (hfnegative x hx))
      (hItail x (le_of_not_ge hxx))

/-- The actual corrected derivative has a uniform negative gap on every
specified compact interval. -/
theorem corrected_derivative_compact_gap (a ε X : ℝ) (ha : 0<a) (hε : |ε|≤1/4) (hX : 0≤X) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x∈Icc 0 X,deriv (correctedPower a ε) x≤-δ := by
  let δ := (3/4)*a*(1+X)^(-a-1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro x hx
  have hb := (correctedPower_derivative_bounds a ε x ha hε hx.1).1
  rw [abs_of_neg (correctedPower_deriv_neg a ε x ha hε hx.1)] at hb
  have hp := Real.rpow_le_rpow_of_nonpos (by linarith [hx.1] : 0<1+x)
    (by linarith [hx.2] : 1+x≤1+X) (by linarith : -a-1≤0)
  have hd := mul_le_mul_of_nonneg_left hp (show 0≤(3/4)*a by positivity)
  dsimp [δ]
  linarith

/-- Existence of a genuine nonpositive-residual lower patch at the critical
endpoint, including all admissibility requirements of Lemma16.4. -/
theorem exists_normalized_lower_patch (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ hscale T τ ε : ℝ, 0<hscale ∧ 1≤T ∧ 0<τ ∧ |ε|≤1/4 ∧ normalizedProfile q c T=hscale ∧
      AdmissibleProfile (lowerPatch (normalizedProfile q c) hscale T τ (correctedPower a ε)) ∧
      (∀ᵐ t ∂volume,t∈Ici 0 → profileResidual (normalizedMemory q (purePhi p (β^2) γ))
        (lowerPatch (normalizedProfile q c) hscale T τ (correctedPower a ε)) t≤0) := by
  obtain ⟨κ,η,h0,hprof⟩ := normalized_critical_corrected_profiles p β γ q a c r hp h ha0 ha1 hbalance
  have he := h.profile_limit.eventually (Iio_mem_nhds hprof.scale_positive)
  obtain ⟨T',hT'⟩ := eventually_atTop.mp he
  let T := max T' 1
  have hT : 1≤T := le_max_right _ _
  have hT0 : 0≤T := by linarith
  let hscale := normalizedProfile q c T
  have hh : 0<hscale := h.profile_positive T hT0
  have hh0 : hscale≤h0 := (hT' T (le_max_left _ _)).le
  let ε := -κ*hscale
  have hε : |ε|≤1/4 := by
    dsimp [ε]
    rw [neg_mul,abs_neg,abs_of_pos (mul_pos hprof.correction_positive hh)]
    exact (mul_le_mul_of_nonneg_left hh0 hprof.correction_positive.le).trans hprof.correction_small
  obtain ⟨X,hX,hTail⟩ := hprof.lower_residual hscale hh hh0
  let I := normalizedIdealResidual p β γ q hscale (correctedPower a ε)
  have hItail : ∀ x≥X,I x≤0 := by
    intro x hx
    dsimp [I,ε]
    rw [normalizedIdealResidual_eq p β γ q hscale c r _ hp h x]
    have hx0 : 0≤x := hX.trans hx
    have hnn : 0≤η*hscale^3*shiftedPower a x^3 :=
      mul_nonneg (mul_nonneg hprof.gap_positive.le (pow_pos hh 3).le) (pow_pos (shiftedPower_pos a x hx0) 3).le
    exact (hTail x hx).trans (by simpa only [neg_mul] using neg_nonpos.mpr hnn)
  obtain ⟨δ,hδ,hdf⟩ := corrected_derivative_compact_gap a ε X ha0 hε hX
  have hIf : ContinuousOn I (Icc 0 X) := (normalizedIdealResidual_continuousOn p β γ q a ε hscale c r h).mono (fun x hx => hx.1)
  obtain ⟨τ,hτ,hτbound⟩ := exists_short_scale hscale δ X (correctedPower a ε) I hh hδ hX hIf hdf
    (fun x hx => (correctedPower_deriv_neg a ε x ha0 hε hx).le) hItail
  obtain ⟨hu,huRes⟩ := normalized_profile_admissible p β γ q c r h
  have hf := correctedPower_admissible a ε ha0 hε
  have hfC1 := correctedPower_contDiffOn a ε
  have hP := lowerPatch_admissible (normalizedProfile q c) (correctedPower a ε) hscale T τ hT0 hτ
    h.profile_C1 hfC1 hu hf rfl
  refine ⟨hscale,T,τ,ε,hh,hT,hτ,hε,rfl,hP,?_⟩
  filter_upwards [volume.ae_ne T,huRes] with t htne hut ht
  change 0≤t at ht
  by_cases htt : t<T
  · rw [lowerPatch,joinAt_early_residual _ _ _ T t ht htt,hut ht]
  · have hTt : T<t := lt_of_le_of_ne (le_of_not_gt htt) (Ne.symm htne)
    have hb := normalized_lowerPatch_residual_bound p β γ q c r (correctedPower a ε)
      hscale T τ t h hf hfC1 rfl hT0 hτ hTt
    exact hb.trans (hτbound _ (div_pos (sub_pos.mpr hTt) hτ).le)


/-- The actual lower comparison patch dominates a fixed positive power law
at every time, including its initial segment. -/
theorem lowerPatch_power_lower_bound (u : ℝ → ℝ) (a ε h T τ : ℝ)
    (ha : 0<a) (hε : |ε|≤1/4) (hh : 0<h) (hT : 0≤T) (hτ : 0<τ)
    (hu : AdmissibleProfile u) (huT : u T=h) :
    ∀ t≥0, ((3/4)*h*(1+1/τ)^(-a))*shiftedPower a t≤
      lowerPatch u h T τ (correctedPower a ε) t := by
  have hτinv : 0<1/τ := one_div_pos.mpr hτ
  have hfactor : (1+1/τ)^(-a)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hfacpos : 0<(1+1/τ)^(-a) := Real.rpow_pos_of_pos (by linarith) _
  have hA : (3/4)*h*(1+1/τ)^(-a)≤h := by
    have hf := mul_le_mul_of_nonneg_left hfactor (show 0≤(3/4)*h by positivity)
    nlinarith only [hf,hh]
  intro t ht
  by_cases htt : t≤T
  · rw [lowerPatch,joinAt_left T u _ t htt]
    have huord := hu.nonincreasing ht hT htt
    rw [huT] at huord
    have hg := shiftedPower_le_one a t ha.le ht
    have hb := mul_le_mul_of_nonneg_left hg (show 0≤(3/4)*h*(1+1/τ)^(-a) by positivity)
    simp only [mul_one] at hb
    exact hb.trans (hA.trans huord)
  · have hTt : T<t := lt_of_not_ge htt
    rw [lowerPatch,joinAt_right T u _ t hTt]
    let x := (t-T)/τ
    have hx : 0≤x := (div_pos (sub_pos.mpr hTt) hτ).le
    have hb := mul_le_mul_of_nonneg_left (correctedPower_bounds a ε x ha.le hε hx).1 hh.le
    have hbase : 1+x≤(1+1/τ)*(1+t) := by
      dsimp [x]
      have hpos := div_nonneg hT hτ.le
      have htpos := div_nonneg ht hτ.le
      field_simp [hτ.ne']
      nlinarith
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0<1+x) hbase (by linarith : -a≤0)
    rw [Real.mul_rpow (by linarith : 0≤1+1/τ) (by linarith : 0≤1+t)] at hp
    have hpow := mul_le_mul_of_nonneg_left hp (show 0≤(3/4)*h by positivity)
    change ((3/4)*h*(1+1/τ)^(-a))*shiftedPower a t≤h*correctedPower a ε x
    unfold shiftedPower at *
    nlinarith only [hpow,hb]

/-- The complete lower half of Proposition16.7 for the actual stationary
profile, with no comparison profile or residual inequality assumed. -/
theorem normalized_critical_endpoint_lower_bound (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ A : ℝ, 0<A ∧ ∀ t≥0,A*(1+t)^(-a)≤normalizedProfile q c t := by
  obtain ⟨hscale,T,τ,ε,hh,hT,hτ,hε,huT,hP,hRes⟩ := exists_normalized_lower_patch p β γ q a c r hp h ha0 ha1 hbalance
  have hT0 : 0≤T := by linarith
  have hcompare := normalized_comparison_lower p β γ q c r _ h hP hRes
  obtain ⟨hu,huRes⟩ := normalized_profile_admissible p β γ q c r h
  have hbound := lowerPatch_power_lower_bound (normalizedProfile q c) a ε hscale T τ ha0 hε hh hT0 hτ hu huT
  refine ⟨(3/4)*hscale*(1+1/τ)^(-a),by positivity,?_⟩
  intro t ht
  exact (hbound t ht).trans (hcompare t ht)

end
end SphericalAging.StationaryLowerEndpoint
