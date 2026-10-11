module

public import SphericalAging.SphereFisherHelly

public section

/-! Pointwise and uniform late decay of the genuinely constructed Fisher
limit. Only the properties already proved by the actual Helly extraction are
needed; no late-decay or tail bound is among the hypotheses. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.FisherLimitClockDecay
open Set Filter MeasureTheory
open scoped Topology

theorem exponential_comparison {f : ℝ → ℝ} {K : ℝ}
    (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0))
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) : f t≤Real.exp (K*(t-s))*f s := by
  have h := mul_le_mul_of_nonneg_left (hc hs (hs.trans hst) hst) (Real.exp_nonneg (K*t))
  have ht : Real.exp (K*t)*Real.exp (-K*t)=1 := by
    rw [← Real.exp_add]
    simp
  have he : Real.exp (K*t)*Real.exp (-K*s)=Real.exp (K*(t-s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc,ht,he,one_mul] using h

/-- Exact source point-to-window estimate for every positive window length.
The exponential normalization is evaluated by genuine one-dimensional FTC. -/
theorem exact_window_bound {f : ℝ → ℝ} {K ε t : ℝ} (hK : 0<K) (hε : 0<ε)
    (hεt : ε≤t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun u => Real.exp (-K*u)*f u) (Ici 0)) :
    f t≤K/(1-Real.exp (-K*ε))*(∫ u in (t-ε)..t,f u) := by
  have hlo : 0≤t-ε := sub_nonneg.mpr hεt
  have hab : t-ε≤t := by linarith
  have hloc : IntegrableOn f (Ioc (t-ε) t) := hi.mono_set fun u hu => lt_of_le_of_lt hlo hu.1
  have hfi : IntervalIntegrable f volume (t-ε) t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hloc
  have hweight : Continuous (fun u : ℝ => f t*Real.exp (K*(u-t))) := by fun_prop
  have hp u (hu : u∈Icc (t-ε) t) : f t*Real.exp (K*(u-t))≤f u := by
    have hh := mul_le_mul_of_nonneg_left
      (hc (hlo.trans hu.1) (hlo.trans (hu.1.trans hu.2)) hu.2) (Real.exp_nonneg (K*u))
    have he1 : Real.exp (K*u)*Real.exp (-K*u)=1 := by
      rw [← Real.exp_add];simp
    have he2 : Real.exp (K*u)*Real.exp (-K*t)=Real.exp (K*(u-t)) := by
      rw [← Real.exp_add];congr 1;ring
    simpa only [← mul_assoc,he1,he2,one_mul,mul_comm (f t)] using hh
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (hweight.intervalIntegrable (t-ε) t) hfi hp
  have hder u : HasDerivAt (fun v : ℝ => f t/K*Real.exp (K*(v-t)))
      (f t*Real.exp (K*(u-t))) u := by
    convert ((((hasDerivAt_id u).sub_const t).const_mul K).exp.const_mul (f t/K)) using 1
    · funext v
      rfl
    · simp only [id_eq,mul_one]
      field_simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hder u) (hweight.intervalIntegrable (t-ε) t)
  have he : (∫ u in (t-ε)..t,f t*Real.exp (K*(u-t)))=
      f t*(1-Real.exp (-K*ε))/K := by
    rw [hFTC]
    have harg : K*((t-ε)-t)= -K*ε := by ring
    rw [sub_self,mul_zero,Real.exp_zero,harg]
    ring
  rw [he] at hm
  have hd : 0<1-Real.exp (-K*ε) := by
    apply sub_pos.mpr
    rw [← Real.exp_zero,Real.exp_lt_exp]
    nlinarith
  have hm' := (div_le_iff₀ hK).mp hm
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hm')

theorem tail_bound {f : ℝ → ℝ} {K : ℝ} (hK : 0≤K)
    (hn : ∀ t,0≤f t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0))
    {t : ℝ} (ht : 1≤t) : f t≤Real.exp K*(∫ u in Ioi (t-1),f u) := by
  have hlo : 0≤t-1 := by linarith
  have hab : t-1≤t := by linarith
  have hloc : IntegrableOn f (Ioc (t-1) t) := hi.mono_set fun u hu => lt_of_le_of_lt hlo hu.1
  have hfi : IntervalIntegrable f volume (t-1) t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hloc
  have hp u (hu : u∈Icc (t-1) t) : f t≤Real.exp K*f u := by
    have h := exponential_comparison hc (by linarith [hu.1]) hu.2
    exact h.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [hu.1])) (hn u))
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f t) volume (t-1) t)
    (hfi.const_mul (Real.exp K)) hp
  have he : (∫ u in (t-1)..t,f t)=f t := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [he,intervalIntegral.integral_const_mul] at hm
  have htInt := hi.mono_set (Ioi_subset_Ioi hlo)
  have hb := setIntegral_mono_set htInt (ae_of_all _ hn)
    (ae_of_all volume (show Ioc (t-1) t⊆Ioi (t-1) from fun _ hu => hu.1))
  rw [← intervalIntegral.integral_of_le hab] at hb
  exact hm.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))

theorem tendsto_zero {f : ℝ → ℝ} {K : ℝ} (hK : 0≤K)
    (hn : ∀ t,0≤f t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0)) :
    Tendsto f atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => ∫ u in Ioi (t-1),f u) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  apply squeeze_zero' (Eventually.of_forall hn)
    ((eventually_ge_atTop (1 : ℝ)).mono fun t ht => tail_bound hK hn hi hc ht)
  simpa only [mul_zero] using ht.const_mul (Real.exp K)

@[expose] def lateSup (f : ℝ → ℝ) (T : ℝ) : ℝ := sSup (f '' Ici T)

theorem uniform_tail_bound {f : ℝ → ℝ} {K : ℝ} (hK : 0≤K)
    (hn : ∀ t,0≤f t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0))
    {T s : ℝ} (hT : 1≤T) (hs : T≤s) : f s≤Real.exp K*(∫ u in Ioi (T-1),f u) := by
  have hh := tail_bound hK hn hi hc (hT.trans hs)
  have hib : IntegrableOn f (Ioi (T-1)) := hi.mono_set (Ioi_subset_Ioi (by linarith))
  have hmass := setIntegral_mono_set hib (ae_of_all _ hn)
    (ae_of_all volume (Ioi_subset_Ioi (show T-1≤s-1 by linarith)))
  exact hh.trans (mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _))

theorem lateSup_bound {f : ℝ → ℝ} {K : ℝ} (hK : 0≤K)
    (hn : ∀ t,0≤f t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0))
    {T : ℝ} (hT : 1≤T) : 0≤lateSup f T ∧ lateSup f T≤Real.exp K*(∫ u in Ioi (T-1),f u) := by
  have hb : BddAbove (f '' Ici T) := ⟨Real.exp K*(∫ u in Ioi (T-1),f u),by
    rintro _ ⟨s,hs,rfl⟩
    exact uniform_tail_bound hK hn hi hc hT hs⟩
  refine ⟨(hn T).trans (le_csSup hb (mem_image_of_mem f (le_refl T))),?_⟩
  apply csSup_le (Nonempty.image f ⟨T,le_refl T⟩)
  rintro _ ⟨s,hs,rfl⟩
  exact uniform_tail_bound hK hn hi hc hT hs

/-- Literal supremum over every sufficiently late time tends to zero. -/
theorem lateSup_tendsto_zero {f : ℝ → ℝ} {K : ℝ} (hK : 0≤K)
    (hn : ∀ t,0≤f t) (hi : IntegrableOn f (Ioi 0))
    (hc : AntitoneOn (fun t => Real.exp (-K*t)*f t) (Ici 0)) :
    Tendsto (lateSup f) atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ => ∫ u in Ioi (T-1),f u) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  apply squeeze_zero' ((eventually_ge_atTop (1 : ℝ)).mono fun T hT => (lateSup_bound hK hn hi hc hT).1)
    ((eventually_ge_atTop (1 : ℝ)).mono fun T hT => (lateSup_bound hK hn hi hc hT).2)
  simpa only [mul_zero] using ht.const_mul (Real.exp K)

end SphericalAging.FisherLimitClockDecay
