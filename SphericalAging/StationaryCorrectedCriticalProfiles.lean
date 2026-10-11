module

public import SphericalAging.StationaryIdealResidual

public section

/-! Corrected critical profile residual estimates (manuscript Lemma16.6). -/

open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.StationaryCorrectedCriticalProfiles
noncomputable section
open StationaryNormalization StationaryPowerProfiles StationaryShiftedResidual
  StationaryPowerAsymptotics StationaryQuadraticDecay StationaryIdealResidual

theorem quadraticResidual_cube_quotient_continuousOn (a : ℝ) (ha : a < 1/2) :
    ContinuousOn (fun t => quadraticResidual a t / shiftedPower a t^3) (Ici 0) := by
  have hcoord : ContinuousOn (fun t : ℝ => 1/(t+2)) (Ici 0) := by
    apply continuousOn_const.div (continuousOn_id.add continuousOn_const)
    intro t ht
    change 0 ≤ t at ht
    change t+2 ≠ 0
    linarith
  have hmap : MapsTo (fun t : ℝ => 1/(t+2)) (Ici 0) (Icc (0:ℝ) (1/2)) := by
    intro t ht
    change 0≤t at ht
    exact ⟨(one_div_pos.mpr (by linarith [ht] : 0<t+2)).le,
      one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (by linarith [ht])⟩
  have hQ := (quadraticQuotient_continuousOn_closed a (by linarith)).comp hcoord hmap
  have hcont := (hQ.sub (continuousOn_const (c:=CriticalEndpoint.exponentCoefficient a))).div (shiftedPower_contDiffOn a).continuousOn
    (fun t ht => (shiftedPower_pos a t ht).ne')
  apply hcont.congr
  intro t ht
  have hd := shifted_convolution_quotient a t ht
  have hg := (shiftedPower_pos a t ht).ne'
  change quadraticResidual a t / shiftedPower a t^3 =
    (quadraticQuotient a (1/(t+2))-CriticalEndpoint.exponentCoefficient a)/shiftedPower a t
  rw [← hd]
  unfold quadraticResidual
  field_simp [hg]

/-- Strict positivity has a genuine uniform positive minimum on each compact
initial interval; the minimum is derived rather than assumed. -/
theorem quadraticResidual_compact_lower_bound (a T : ℝ) (ha0 : 0<a) (ha1 : a<1/2) (hT : 0≤T) :
    ∃ μ : ℝ, 0<μ ∧ ∀ t ∈ Icc 0 T, μ*shiftedPower a t^3 ≤ quadraticResidual a t := by
  obtain ⟨t₀,ht₀,hmin⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_isMinOn ⟨0,⟨le_rfl,hT⟩⟩
    ((quadraticResidual_cube_quotient_continuousOn a ha1).mono (fun t ht => ht.1))
  have hp : 0<quadraticResidual a t₀ / shiftedPower a t₀^3 :=
    div_pos (quadraticResidual_pos a t₀ ha0 ha1 ht₀.1) (pow_pos (shiftedPower_pos a t₀ ht₀.1) 3)
  refine ⟨_,hp,?_⟩
  intro t ht
  exact (le_div_iff₀ (pow_pos (shiftedPower_pos a t ht.1) 3)).mp (hmin ht)

/-- The actual cross residual has a global normalized bound. -/
theorem crossResidual_global_bound (a : ℝ) (ha0 : 0<a) (ha1 : a<1/2) :
    ∃ K : ℝ, 0<K ∧ ∀ t≥0, |crossResidual a t|≤K*shiftedPower a t^3 := by
  obtain ⟨C,hC,hbound⟩ := shifted_convolution_quotient_bounded a (2*a) (by linarith) (by linarith)
  let θ := CriticalEndpoint.exponentCoefficient a
  have hθ : 0<θ := CriticalEndpoint.exponentCoefficient_pos a ha1
  refine ⟨C+|θ|,by positivity,?_⟩
  intro t ht
  have hg := shiftedPower_pos a t ht
  have hd := power_convolution_derivative_eq a t 1 2 (by linarith)
  simp only [pow_one,Nat.cast_one,one_mul,Nat.cast_ofNat] at hd
  have hp := shiftedPower_nat a t 2 (by linarith)
  norm_num only [Nat.cast_ofNat] at hp
  have hb := hbound t ht
  rw [hp,show shiftedPower a t*shiftedPower a t^2=shiftedPower a t^3 by ring,
    abs_div,abs_of_pos (pow_pos hg 3)] at hb
  have hb' := (div_le_iff₀ (pow_pos hg 3)).mp hb
  unfold crossResidual
  rw [hd]
  calc
    _ ≤ |deriv (causalConvolution (shiftedPower a) (shiftedPower (2*a))) t|+|θ*shiftedPower a t^3| := abs_sub _ _
    _ ≤ C*shiftedPower a t^3+|θ| *shiftedPower a t^3 := by
      rw [abs_mul,abs_of_pos (pow_pos hg 3)]
      exact add_le_add hb' le_rfl
    _ = _ := by ring

/-- The strictly negative actual limit supplies an eventual cubic sign gap. -/
theorem crossResidual_eventual_negative (a : ℝ) (ha0 : 0<a) (ha1 : a<1/2) :
    ∃ Δ T : ℝ, 0<Δ ∧ 0≤T ∧ ∀ t≥T, crossResidual a t≤-(Δ/2)*shiftedPower a t^3 := by
  let L := (1-3*a)*ProbabilityTheory.beta (1-a) (1-2*a)-CriticalEndpoint.exponentCoefficient a
  have hL : L<0 := critical_cross_limit_negative a ha0 ha1
  have he := (crossResidual_quotient_tendsto a ha1).eventually (Iio_mem_nhds (by dsimp [L]; linarith : L<L/2))
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  refine ⟨-L,max T 0,by linarith,le_max_right _ _,?_⟩
  intro t ht
  have ht0 : 0≤t := (le_max_right T 0).trans ht
  have hb := (hT t ((le_max_left T 0).trans ht)).le
  have hb' := (div_le_iff₀ (pow_pos (shiftedPower_pos a t ht0) 3)).mp hb
  convert hb' using 1; ring


/-- The actual ideal residual normalized by h³g³, before choosing ε. -/
theorem idealResidual_scaled_expansion (a ε h t : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (hθ : lam 0=CriticalEndpoint.exponentCoefficient a) (hh : h≠0) (ht : 0≤t) :
    idealResidual (n+1) lam h (correctedPower a ε) t / (h^3*shiftedPower a t^3) =
      (1+ε)^2*(quadraticResidual a t/shiftedPower a t^3)/h -
        (2*ε*(1+ε)/h)*(crossResidual a t/shiftedPower a t^3)+
          (ε^2/h)*(quarticResidual a t/shiftedPower a t^3)+
            idealRemainder a ε h n lam t/(h^3*shiftedPower a t^3) := by
  rw [idealResidual_critical_expansion a ε h t n lam hθ ht,corrected_quadratic_expansion a ε t ht]
  field_simp [hh,(shiftedPower_pos a t ht).ne']

/-- This specialization reduces the positive correction to scalar estimates. -/
theorem idealResidual_scaled_positive (a κ h t : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (hθ : lam 0=CriticalEndpoint.exponentCoefficient a) (hh : h≠0) (ht : 0≤t) :
    idealResidual (n+1) lam h (correctedPower a (κ*h)) t/(h^3*shiftedPower a t^3) =
      (1+κ*h)^2*(quadraticResidual a t/shiftedPower a t^3)/h -
        2*κ*(1+κ*h)*(crossResidual a t/shiftedPower a t^3)+
          κ^2*h*(quarticResidual a t/shiftedPower a t^3)+
            idealRemainder a (κ*h) h n lam t/(h^3*shiftedPower a t^3) := by
  rw [idealResidual_scaled_expansion a (κ*h) h t n lam hθ hh ht]
  field_simp [hh]

/-- The corresponding exact formula for the negative correction. -/
theorem idealResidual_scaled_negative (a κ h t : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (hθ : lam 0=CriticalEndpoint.exponentCoefficient a) (hh : h≠0) (ht : 0≤t) :
    idealResidual (n+1) lam h (correctedPower a (-κ*h)) t/(h^3*shiftedPower a t^3) =
      (1-κ*h)^2*(quadraticResidual a t/shiftedPower a t^3)/h +
        2*κ*(1-κ*h)*(crossResidual a t/shiftedPower a t^3)+
          κ^2*h*(quarticResidual a t/shiftedPower a t^3)+
            idealRemainder a (-κ*h) h n lam t/(h^3*shiftedPower a t^3) := by
  rw [idealResidual_scaled_expansion a (-κ*h) h t n lam hθ hh ht]
  field_simp [hh]
  ring

/-- The tail scalar lower bound, independent of any analytic profile. -/
theorem positive_correction_tail_bound (κ h Δ KD K0 d H D2 N : ℝ)
    (hκ : 0≤κ) (hh : 0<h) (hΔ : 0≤Δ) (hd : 0≤d)
    (hH : H≤-(Δ/2)) (hD2 : -KD≤D2) (hN : -K0≤N) :
    κ*Δ-κ^2*h*KD-K0 ≤ (1+κ*h)^2*d/h-2*κ*(1+κ*h)*H+κ^2*h*D2+N := by
  have hfirst : 0≤(1+κ*h)^2*d/h := by positivity
  have hcross := mul_le_mul_of_nonpos_left hH (show -2*κ*(1+κ*h)≤0 by nlinarith [mul_nonneg hκ (mul_nonneg hκ hh.le)])
  have hcross' : κ*Δ≤-2*κ*(1+κ*h)*H := by
    nlinarith [mul_nonneg (sq_nonneg κ) (mul_nonneg hh.le hΔ)]
  have hd2 := mul_le_mul_of_nonneg_left hD2 (show 0≤κ^2*h by positivity)
  nlinarith

/-- Compact-interval scalar lower bound for the positive correction. -/
theorem positive_correction_compact_bound (κ h KH KD K0 d H D2 N : ℝ)
    (hκ : 0≤κ) (hh : 0<h) (hh1 : h≤1) (hquarter : κ*h≤1/4)
    (hKH : 0≤KH) (hKD : 0≤KD) (hd : 0≤d)
    (hH : H≤KH) (hD2 : -KD≤D2) (hN : -K0≤N) :
    d/h-((5/2)*κ*KH+κ^2*KD+K0) ≤
      (1+κ*h)^2*d/h-2*κ*(1+κ*h)*H+κ^2*h*D2+N := by
  have hep : 0≤κ*h := mul_nonneg hκ hh.le
  have hp : 1≤(1+κ*h)^2 := by nlinarith
  have hddiv : 0≤d/h := div_nonneg hd hh.le
  have hfirst := mul_le_mul_of_nonneg_right hp hddiv
  have hfirst' : d/h≤(1+κ*h)^2*d/h := by convert hfirst using 1 <;> ring
  have hcross := mul_le_mul_of_nonpos_left hH (show -2*κ*(1+κ*h)≤0 by nlinarith [mul_nonneg hκ (mul_nonneg hκ hh.le)])
  have hc : -((5/2)*κ*KH)≤-2*κ*(1+κ*h)*H := by
    nlinarith [mul_nonneg hκ hKH,mul_le_mul_of_nonneg_left hquarter (mul_nonneg hκ hKH)]
  have hd2 := mul_le_mul_of_nonneg_left hD2 (show 0≤κ^2*h by positivity)
  have hd2' : -κ^2*KD≤κ^2*h*D2 := by
    nlinarith [mul_le_mul_of_nonneg_left hh1 (mul_nonneg (sq_nonneg κ) hKD)]
  nlinarith

/-- The tail scalar upper bound for the negative correction. -/
theorem negative_correction_tail_bound (κ h Δ KD K0 d H D2 N : ℝ)
    (hκ : 0≤κ) (hh : 0<h) (hΔ : 0≤Δ) (hquarter : κ*h≤1/4) (hd : 0≤d)
    (hH : H≤-(Δ/2)) (hD2 : D2≤KD) (hN : N≤K0) :
    (1-κ*h)^2*d/h+2*κ*(1-κ*h)*H+κ^2*h*D2+N ≤
      d/h-(3/4)*κ*Δ+κ^2*h*KD+K0 := by
  have hep : 0≤κ*h := mul_nonneg hκ hh.le
  have hp : (1-κ*h)^2≤1 := by nlinarith
  have hddiv : 0≤d/h := div_nonneg hd hh.le
  have hfirst := mul_le_mul_of_nonneg_right hp hddiv
  have hfirst' : (1-κ*h)^2*d/h≤d/h := by convert hfirst using 1 <;> ring
  have hcross := mul_le_mul_of_nonneg_left hH (show 0≤2*κ*(1-κ*h) by exact mul_nonneg (mul_nonneg (by norm_num) hκ) (by linarith))
  have hc : 2*κ*(1-κ*h)*H≤-(3/4)*κ*Δ := by
    nlinarith [mul_le_mul_of_nonneg_left hquarter (mul_nonneg hκ hΔ)]
  have hd2 := mul_le_mul_of_nonneg_left hD2 (show 0≤κ^2*h by positivity)
  nlinarith


/-- A concrete finite choice of all small-correction constants. -/
theorem critical_correction_constants (K0 KD KH μ Δ : ℝ)
    (hK0 : 0<K0) (hKD : 0<KD) (hKH : 0<KH) (hμ : 0<μ) (hΔ : 0<Δ) :
    ∃ κ η h0 : ℝ, 0<κ ∧ 0<η ∧ 0<h0 ∧ h0≤1 ∧ κ*h0≤1/4 ∧
      K0≤κ*Δ/4 ∧ κ^2*KD*h0≤κ*Δ/4 ∧
      ((5/2)*κ*KH+κ^2*KD+K0)*h0≤μ/2 ∧ η≤κ*Δ/8 ∧ η≤μ/2 := by
  let κ := 1+4*K0/Δ
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hκΔ : κ*Δ=Δ+4*K0 := by dsimp [κ]; field_simp [hΔ.ne']
  let B := (5/2)*κ*KH+κ^2*KD+K0
  have hB : 0<B := by dsimp [B]; positivity
  let h0 := min 1 (min (1/(4*κ)) (min (Δ/(4*κ*KD)) (μ/(2*B))))
  have hh0 : 0<h0 := by dsimp [h0]; positivity
  have hh1 : h0≤1 := min_le_left _ _
  have hh2 : h0≤1/(4*κ) := (min_le_right _ _).trans (min_le_left _ _)
  have hh3 : h0≤Δ/(4*κ*KD) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh4 : h0≤μ/(2*B) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc2 := (le_div_iff₀ (show 0<4*κ by positivity)).mp hh2
  have hc3 := (le_div_iff₀ (show 0<4*κ*KD by positivity)).mp hh3
  have hc3' := mul_le_mul_of_nonneg_left hc3 hκ.le
  have hc4 := (le_div_iff₀ (show 0<2*B by positivity)).mp hh4
  let η := min (κ*Δ/8) (μ/2)
  refine ⟨κ,η,h0,hκ,by dsimp [η]; positivity,hh0,hh1,?_,?_,?_,?_,min_le_left _ _,min_le_right _ _⟩
  · linarith
  · nlinarith
  · nlinarith
  · dsimp [B] at hc4
    linarith

theorem abs_quotient_bound (x y C : ℝ) (hy : 0<y) (hx : |x|≤C*y) : |x/y|≤C := by
  rw [abs_div,abs_of_pos hy]
  exact (div_le_iff₀ hy).mpr hx

/-- Complete critical residual signs for the actual polynomial ideal memory.
This is Lemma16.6; polynomial coefficients are arbitrary except the exact
critical quadratic coefficient, so it also covers every p>=3. -/
theorem corrected_critical_profiles (a : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (ha0 : 0<a) (ha1 : a<1/2) (hθ : lam 0=CriticalEndpoint.exponentCoefficient a) :
    ∃ κ η h0 : ℝ, 0<κ ∧ 0<η ∧ 0<h0 ∧ h0≤1 ∧ κ*h0≤1/4 ∧
      ∀ h : ℝ, 0<h → h≤h0 →
        (∀ t≥0, η*h^3*shiftedPower a t^3≤ idealResidual (n+1) lam h (correctedPower a (κ*h)) t) ∧
        (∃ X : ℝ, 0≤X ∧ ∀ t≥X,
          idealResidual (n+1) lam h (correctedPower a (-κ*h)) t≤-η*h^3*shiftedPower a t^3) := by
  obtain ⟨K0,hK0,hN⟩ := idealRemainder_bound a n lam ha0 ha1
  obtain ⟨KD,hKD,hD⟩ := quarticResidual_bound a ha0 ha1
  obtain ⟨KH,hKH,hH⟩ := crossResidual_global_bound a ha0 ha1
  obtain ⟨Δ,T,hΔ,hT,hTail⟩ := crossResidual_eventual_negative a ha0 ha1
  obtain ⟨μ,hμ,hCompact⟩ := quadraticResidual_compact_lower_bound a T ha0 ha1 hT
  obtain ⟨κ,η,h0,hκ,hη,hh0,hh01,hQuarter,hKκ,hDκ,hBκ,hηΔ,hημ⟩ :=
    critical_correction_constants K0 KD KH μ Δ hK0 hKD hKH hμ hΔ
  refine ⟨κ,η,h0,hκ,hη,hh0,hh01,hQuarter,?_⟩
  intro h hh hhh0
  have hh1 : h≤1 := hhh0.trans hh01
  have hep0 : 0<κ*h := mul_pos hκ hh
  have hep : κ*h≤1/4 := (mul_le_mul_of_nonneg_left hhh0 hκ.le).trans hQuarter
  have hepos : |κ*h|≤1/4 := by rw [abs_of_pos hep0]; exact hep
  have heneg : |-κ*h|≤1/4 := by simpa only [neg_mul,abs_neg] using hepos
  have hDh : κ^2*h*KD≤κ*Δ/4 := by
    have hd := mul_le_mul_of_nonneg_left hhh0 (mul_nonneg (sq_nonneg κ) hKD.le)
    nlinarith
  have hBh : ((5/2)*κ*KH+κ^2*KD+K0)*h≤μ/2 := by
    have hb := mul_le_mul_of_nonneg_left hhh0
      (show 0≤(5/2)*κ*KH+κ^2*KD+K0 by positivity)
    exact hb.trans hBκ
  have hData (ε t : ℝ) (hε : |ε|≤1/4) (ht : 0≤t) :
      0≤quadraticResidual a t/shiftedPower a t^3 ∧
      |crossResidual a t/shiftedPower a t^3|≤KH ∧
      |quarticResidual a t/shiftedPower a t^3|≤KD ∧
      |idealRemainder a ε h n lam t/(h^3*shiftedPower a t^3)|≤K0 := by
    have hg := pow_pos (shiftedPower_pos a t ht) 3
    refine ⟨(div_pos (quadraticResidual_pos a t ha0 ha1 ht) hg).le,
      abs_quotient_bound _ _ _ hg (hH t ht),abs_quotient_bound _ _ _ hg (hD t ht),?_⟩
    have hn := hN ε hε h hh.le hh1 t ht
    have hn' : |idealRemainder a ε h n lam t|≤K0*(h^3*shiftedPower a t^3) := by convert hn using 1; ring
    exact abs_quotient_bound _ _ _ (mul_pos (pow_pos hh 3) hg) hn'
  constructor
  · intro t ht
    obtain ⟨hd,hHr,hDr,hNr⟩ := hData (κ*h) t hepos ht
    rw [abs_le] at hHr hDr hNr
    have hI : η≤ idealResidual (n+1) lam h (correctedPower a (κ*h)) t/(h^3*shiftedPower a t^3) := by
      rw [idealResidual_scaled_positive a κ h t n lam hθ hh.ne' ht]
      by_cases hTt : T≤t
      · have hc := (div_le_iff₀ (pow_pos (shiftedPower_pos a t ht) 3)).mpr (hTail t hTt)
        have hb := positive_correction_tail_bound κ h Δ KD K0 _ _ _ _ hκ.le hh hΔ.le hd hc hDr.1 hNr.1
        have hη' : η≤κ*Δ-κ^2*h*KD-K0 := by nlinarith only [hKκ,hDh,hηΔ,mul_pos hκ hΔ]
        exact hη'.trans hb
      · have htm : t∈Icc 0 T := ⟨ht,(le_of_not_ge hTt)⟩
        have hμd := (le_div_iff₀ (pow_pos (shiftedPower_pos a t ht) 3)).mpr (hCompact t htm)
        have hb := positive_correction_compact_bound κ h KH KD K0 _ _ _ _ hκ.le hh hh1 hep hKH.le hKD.le hd hHr.2 hDr.1 hNr.1
        have hμdiv : μ/h≤quadraticResidual a t/shiftedPower a t^3/h := div_le_div_of_nonneg_right hμd hh.le
        have hsmall : ((5/2)*κ*KH+κ^2*KD+K0)≤μ/(2*h) := by
          apply (le_div_iff₀ (show 0<2*h by positivity)).mpr
          nlinarith
        have hbase : μ≤μ/h := by
          exact (le_div_iff₀ hh).mpr (by nlinarith)
        have hdivhalf : μ/(2*h)=μ/h/2 := by field_simp [hh.ne']
        rw [hdivhalf] at hsmall
        have hη' : η≤quadraticResidual a t/shiftedPower a t^3/h-((5/2)*κ*KH+κ^2*KD+K0) := by linarith only [hημ,hsmall,hμdiv,hbase]
        exact hη'.trans hb
    have hi := (le_div_iff₀ (mul_pos (pow_pos hh 3) (pow_pos (shiftedPower_pos a t ht) 3))).mp hI
    convert hi using 1; ring
  · have hdlim := (quadraticResidual_isLittleO_cube a ha0 ha1).tendsto_div_nhds_zero
    have he := hdlim.eventually (Iio_mem_nhds (show 0<(κ*Δ/8)*h by positivity))
    obtain ⟨X,hX⟩ := eventually_atTop.mp he
    refine ⟨max X T,(hT.trans (le_max_right _ _)),?_⟩
    intro t htX
    have ht : 0≤t := hT.trans ((le_max_right X T).trans htX)
    obtain ⟨hd,hHr,hDr,hNr⟩ := hData (-κ*h) t heneg ht
    rw [abs_le] at hHr hDr hNr
    have hc := (div_le_iff₀ (pow_pos (shiftedPower_pos a t ht) 3)).mpr (hTail t ((le_max_right X T).trans htX))
    have hdlow := (hX t ((le_max_left X T).trans htX)).le
    have hddiv : quadraticResidual a t/shiftedPower a t^3/h≤κ*Δ/8 := by
      apply (div_le_iff₀ hh).mpr
      exact hdlow
    have hI : idealResidual (n+1) lam h (correctedPower a (-κ*h)) t/(h^3*shiftedPower a t^3)≤-η := by
      rw [idealResidual_scaled_negative a κ h t n lam hθ hh.ne' ht]
      have hb := negative_correction_tail_bound κ h Δ KD K0 _ _ _ _ hκ.le hh hΔ.le hep hd hc hDr.2 hNr.2
      have hη' : quadraticResidual a t/shiftedPower a t^3/h-(3/4)*κ*Δ+κ^2*h*KD+K0≤-η := by nlinarith only [hηΔ,hKκ,hDh,hddiv]
      exact hb.trans hη'
    have hi := (div_le_iff₀ (mul_pos (pow_pos hh 3) (pow_pos (shiftedPower_pos a t ht) 3))).mp hI
    convert hi using 1; ring


/-- Every assertion of the corrected critical profile lemma. -/
structure CorrectedCriticalConclusions (a : ℝ) (n : ℕ) (lam : ℕ → ℝ) (κ η h0 : ℝ) : Prop where
  correction_positive : 0<κ
  gap_positive : 0<η
  scale_positive : 0<h0
  scale_le_one : h0≤1
  correction_small : κ*h0≤1/4
  upper_positive : ∀ h : ℝ, 0<h → h≤h0 → ∀ t≥0, 0<correctedPower a (κ*h) t
  lower_positive : ∀ h : ℝ, 0<h → h≤h0 → ∀ t≥0, 0<correctedPower a (-κ*h) t
  upper_strictAnti : ∀ h : ℝ, 0<h → h≤h0 → StrictAntiOn (correctedPower a (κ*h)) (Ici 0)
  lower_strictAnti : ∀ h : ℝ, 0<h → h≤h0 → StrictAntiOn (correctedPower a (-κ*h)) (Ici 0)
  upper_initial : ∀ h : ℝ, correctedPower a (κ*h) 0=1
  lower_initial : ∀ h : ℝ, correctedPower a (-κ*h) 0=1
  upper_residual : ∀ h : ℝ, 0<h → h≤h0 → ∀ t≥0,
    η*h^3*shiftedPower a t^3≤ idealResidual (n+1) lam h (correctedPower a (κ*h)) t
  lower_residual : ∀ h : ℝ, 0<h → h≤h0 → ∃ X : ℝ, 0≤X ∧ ∀ t≥X,
    idealResidual (n+1) lam h (correctedPower a (-κ*h)) t≤-η*h^3*shiftedPower a t^3

/-- Full manuscript Lemma16.6 for the actual normalized finite memory. -/
theorem critical_corrected_profiles (a : ℝ) (n : ℕ) (lam : ℕ → ℝ)
    (ha0 : 0<a) (ha1 : a<1/2) (hθ : lam 0=CriticalEndpoint.exponentCoefficient a) :
    ∃ κ η h0 : ℝ, CorrectedCriticalConclusions a n lam κ η h0 := by
  obtain ⟨κ,η,h0,hκ,hη,hh0,hh01,hQuarter,hres⟩ := corrected_critical_profiles a n lam ha0 ha1 hθ
  have hε (h : ℝ) (hh : 0<h) (hhh0 : h≤h0) : |κ*h|≤1/4 := by
    rw [abs_of_pos (mul_pos hκ hh)]
    exact (mul_le_mul_of_nonneg_left hhh0 hκ.le).trans hQuarter
  have hεneg (h : ℝ) (hh : 0<h) (hhh0 : h≤h0) : |-κ*h|≤1/4 := by
    simpa only [neg_mul,abs_neg] using hε h hh hhh0
  exact ⟨κ,η,h0,{
    correction_positive := hκ
    gap_positive := hη
    scale_positive := hh0
    scale_le_one := hh01
    correction_small := hQuarter
    upper_positive := fun h hh hhh0 t ht => correctedPower_pos a (κ*h) t ha0.le (hε h hh hhh0) ht
    lower_positive := fun h hh hhh0 t ht => correctedPower_pos a (-κ*h) t ha0.le (hεneg h hh hhh0) ht
    upper_strictAnti := fun h hh hhh0 => correctedPower_strictAntiOn a (κ*h) ha0 (hε h hh hhh0)
    lower_strictAnti := fun h hh hhh0 => correctedPower_strictAntiOn a (-κ*h) ha0 (hεneg h hh hhh0)
    upper_initial := fun h => correctedPower_zero a (κ*h)
    lower_initial := fun h => correctedPower_zero a (-κ*h)
    upper_residual := fun h hh hhh0 => (hres h hh hhh0).1
    lower_residual := fun h hh hhh0 => (hres h hh hhh0).2
  }⟩

/-- The selected exponent and Lemma16.3 supply the exact degree-two
coefficient for every p>=3, with no additional memory hypotheses. -/
theorem normalized_critical_corrected_profiles (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (_hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ κ η h0 : ℝ,
      CorrectedCriticalConclusions a (p-3) (fun j => memoryCoefficient p q (j+2)) κ η h0 := by
  apply critical_corrected_profiles a (p-3) (fun j => memoryCoefficient p q (j+2)) ha0 ha1
  change memoryCoefficient p q 2=CriticalEndpoint.exponentCoefficient a
  exact h.quadratic_coefficient.trans hbalance.symm


/-- Direct bridge to the manuscript's actual normalized memory polynomial. -/
theorem normalized_memory_polynomial (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r) (y : ℝ) :
    normalizedMemory q (purePhi p (β^2) γ) y =
      polynomialMemory (p-3+1) (fun j => memoryCoefficient p q (j+2)) y := by
  rw [h.memory_expansion]
  unfold polynomialMemory
  rw [show p-3+1=p-2 by omega]

@[expose] def normalizedIdealResidual (p : ℕ) (β γ q h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  h*f t-(1-h)*normalizedMemory q (purePhi p (β^2) γ) (h*f t)+
    h*causalConvolution (fun s => normalizedMemory q (purePhi p (β^2) γ) (h*f s)) (deriv f) t

theorem normalizedIdealResidual_eq (p : ℕ) (β γ q hscale : ℝ) (c r f : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r) (t : ℝ) :
    normalizedIdealResidual p β γ q hscale f t =
      idealResidual (p-3+1) (fun j => memoryCoefficient p q (j+2)) hscale f t := by
  have hm := normalized_memory_polynomial p β γ q c r hp h
  have hfun : (fun s => normalizedMemory q (purePhi p (β^2) γ) (hscale*f s)) =
      (fun s => polynomialMemory (p-3+1) (fun j => memoryCoefficient p q (j+2)) (hscale*f s)) := by
    funext s
    exact hm _
  unfold normalizedIdealResidual idealResidual
  rw [hm (hscale*f t),hfun]

/-- The actual normalized-memory residual signs asserted by Lemma16.6,
valid for all integer p>=3 and the uniquely selected exponent. -/
theorem normalized_critical_residual_signs (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ κ η h0 : ℝ, 0<κ ∧ 0<η ∧ 0<h0 ∧ h0≤1 ∧ κ*h0≤1/4 ∧
      ∀ hscale : ℝ, 0<hscale → hscale≤h0 →
        (∀ t≥0, η*hscale^3*shiftedPower a t^3≤ normalizedIdealResidual p β γ q hscale (correctedPower a (κ*hscale)) t) ∧
        (∃ X : ℝ, 0≤X ∧ ∀ t≥X,
          normalizedIdealResidual p β γ q hscale (correctedPower a (-κ*hscale)) t≤-η*hscale^3*shiftedPower a t^3) := by
  obtain ⟨κ,η,h0,hprof⟩ := normalized_critical_corrected_profiles p β γ q a c r hp h ha0 ha1 hbalance
  refine ⟨κ,η,h0,hprof.correction_positive,hprof.gap_positive,hprof.scale_positive,hprof.scale_le_one,hprof.correction_small,?_⟩
  intro hscale hh hh0
  constructor
  · intro t ht
    rw [normalizedIdealResidual_eq p β γ q hscale c r _ hp h t]
    exact hprof.upper_residual hscale hh hh0 t ht
  · obtain ⟨X,hX,hbound⟩ := hprof.lower_residual hscale hh hh0
    refine ⟨X,hX,?_⟩
    intro t ht
    rw [normalizedIdealResidual_eq p β γ q hscale c r _ hp h t]
    exact hbound t ht

end
end SphericalAging.StationaryCorrectedCriticalProfiles
