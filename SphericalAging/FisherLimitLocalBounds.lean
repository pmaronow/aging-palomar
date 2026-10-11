module

public import SphericalAging.FisherLimitClockDecay

public section

/-! Local bounds and the exact moving-window estimate for the actual
extracted Fisher clock, including the zero-rate case. -/
noncomputable section
namespace SphericalAging.FisherLimitLocalBounds
open Set Filter MeasureTheory FisherLimitClockDecay
open scoped Topology

 theorem pointwise_local_bound {f : ℝ→ℝ} {K T s : ℝ} (hK : 0≤K)
    (hn : ∀t,0≤f t) (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0))
    (hs : s∈Icc 0 T) : |f s|≤Real.exp (K*T)*f 0 := by
  rw [abs_of_nonneg (hn s)]
  have hh := exponential_comparison hc (s:=0) le_rfl hs.1
  simp only [sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hK)) (hn 0))

 theorem locally_bounded_on_ray {f : ℝ→ℝ} {K : ℝ} (hK : 0≤K)
    (hn : ∀t,0≤f t) (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0)) :
    ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,|f s|≤M := by
  intro T _
  exact ⟨Real.exp (K*T)*f 0,mul_nonneg (Real.exp_nonneg _) (hn 0),
    fun _ hs => pointwise_local_bound hK hn hc hs⟩

 theorem zero_rate_window_bound {f : ℝ→ℝ} {ε t : ℝ} (hε : 0<ε) (hεt : ε≤t)
    (hi : IntegrableOn f (Ioi 0)) (hc : AntitoneOn f (Ici 0)) :
    f t≤ε⁻¹*(∫u in (t-ε)..t,f u) := by
  have hlo : 0≤t-ε := sub_nonneg.mpr hεt
  have hab : t-ε≤t := by linarith
  have hfi : IntervalIntegrable f volume (t-ε) t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (hi.mono_set fun u hu => lt_of_le_of_lt hlo hu.1)
  have hh := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f t) volume (t-ε) t) hfi
    (fun u hu => hc (hlo.trans hu.1) (hlo.trans hab) hu.2)
  rw [intervalIntegral.integral_const] at hh
  simp only [smul_eq_mul] at hh
  have he : t-(t-ε)=ε := by ring
  rw [he] at hh
  have hd := (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv,mul_comm] using hd

@[expose]  def windowFactor (K ε : ℝ) : ℝ := if K=0 then ε⁻¹ else K/(1-Real.exp (-K*ε))

 theorem moving_window_bound {f : ℝ→ℝ} {K ε t : ℝ} (hK : 0≤K)
    (hε : 0<ε) (hεt : ε≤t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun u => Real.exp (-K*u)*f u) (Ici 0)) :
    f t≤windowFactor K ε*(∫u in (t-ε)..t,f u) := by
  by_cases h0 : K=0
  · subst K
    simp only [neg_zero,zero_mul,Real.exp_zero,one_mul] at hc
    simpa [windowFactor] using zero_rate_window_bound hε hεt hi hc
  · simpa [windowFactor,h0] using
      exact_window_bound (lt_of_le_of_ne hK (Ne.symm h0)) hε hεt hi hc

 theorem clock_consequences {f : ℝ→ℝ} {K : ℝ} (hK : 0≤K)
    (hn : ∀t,0≤f t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0))
    (hrc : ∀s,ContinuousWithinAt f (Ici s) s) :
    (∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,|f s|≤M) ∧
      (∀s,ContinuousWithinAt f (Ici s) s) ∧
      (∀ε t : ℝ,0<ε → ε≤t → f t≤windowFactor K ε*(∫u in (t-ε)..t,f u)) ∧
      Tendsto (lateSup f) atTop (𝓝 0) :=
  ⟨locally_bounded_on_ray hK hn hc,hrc,fun _ _ hε hεt => moving_window_bound hK hε hεt hi hc,
    lateSup_tendsto_zero hK hn hi hc⟩

end SphericalAging.FisherLimitLocalBounds
