module

public import SphericalAging.CausalFrameTraceBound
public import SphericalAging.PositiveRowAverage
public import SphericalAging.CenterAverageReal

public section

/-! The colored old-row trace mass is an actual positive response average. Its
limit follows from the fixed-age reflected prefix limit and whole-row L²
localization, rather than assuming a trace/susceptibility identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CausalTraceMassLimit
open CausalTree CausalTree.HilbertDatum CKSpecification CKPhysicalConsequences GreenCovariance
open PrefixReflection CausalCenterAverage CenterAverageReal PrefixRectangleStability
open CausalStripDistance CausalStripIntegralBound CausalFrameTraceBound
open WhitePrefixResponse ThermalRowConvergence OldResponseL2 BackwardRowL2

theorem early_response_mass_tendsto_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0)) (t : ℕ→ℝ) (ht : Tendsto t atTop atTop)
    {K : ℝ} (hK : 0≤K) :
    Tendsto (fun n => ∫u in (0:ℝ)..K,d.R (t n) u) atTop (𝓝 0) := by
  have hLag : Tendsto (fun n => t n-K) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-K) ht
  have hE := old_response_square_tendsto_zero h hr hrow t (fun n => t n-K) ht hLag (fun n => by linarith)
  have he : Tendsto (fun n => ∫u in (0:ℝ)..K,(d.R (t n) u)^2) atTop (𝓝 0) := by
    simpa only [remoteTail,sub_sub_cancel,max_eq_right hK] using hE
  have hb := physical_bounds_of_equations h
  have hs : Tendsto (fun n => Real.sqrt K*Real.sqrt (∫u in (0:ℝ)..K,(d.R (t n) u)^2)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero] using he.sqrt.const_mul (Real.sqrt K)
  have hm : Tendsto (fun n => ∫u in (0:ℝ)..K,d.R (t n) u) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hs
    · filter_upwards [ht.eventually (eventually_ge_atTop K)] with n hn
      exact intervalIntegral.integral_nonneg hK (fun u hu => hb.2 (t n) u hu.1 (hu.2.trans hn))
    · filter_upwards [ht.eventually (eventually_ge_atTop K)] with n hn
      have hc : Continuous (fun u : ℝ => clampedResponse d (t n) u) :=
        (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
      have hcs := IntervalL2Bounds.integral_abs_le_sqrt hc hK
      have hR : (∫u in (0:ℝ)..K,|clampedResponse d (t n) u|)=∫u in (0:ℝ)..K,d.R (t n) u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hK] at hu
        dsimp only
        rw [clampedResponse_eq hu.1 (hu.2.trans hn),abs_of_nonneg (hb.2 _ _ hu.1 (hu.2.trans hn))]
      have hR2 : (∫u in (0:ℝ)..K,(clampedResponse d (t n) u)^2)=∫u in (0:ℝ)..K,(d.R (t n) u)^2 := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hK] at hu
        dsimp only
        rw [clampedResponse_eq hu.1 (hu.2.trans hn)]
      simpa only [hR,hR2,sub_zero] using hcs
  exact hm

theorem initial_interval_response_mass_tendsto_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0)) (t : ℕ→ℝ) (ht : Tendsto t atTop atTop)
    {D K : ℝ} (hD : 0≤D) (hDK : D≤K) :
    Tendsto (fun n => ∫u in D..K,d.R (t n) u) atTop (𝓝 0) := by
  have h0 := early_response_mass_tendsto_zero h hr hrow t ht (hD.trans hDK)
  have hb := physical_bounds_of_equations h
  have hK := hD.trans hDK
  apply squeeze_zero' _ _ h0
  · filter_upwards [ht.eventually (eventually_ge_atTop K)] with n hn
    exact intervalIntegral.integral_nonneg hDK (fun u hu => hb.2 (t n) u (hD.trans hu.1) (hu.2.trans hn))
  · filter_upwards [ht.eventually (eventually_ge_atTop K)] with n hn
    apply intervalIntegral.integral_mono_interval hD hDK le_rfl
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu; exact hb.2 (t n) u hu.1.le (hu.2.trans hn)) ((response_continuousOn_interval h le_rfl hn).intervalIntegrable_of_Icc hK)

 theorem prefixTraceMass_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r c : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0)) {D : ℝ} (hD : 0≤D)
    (hc : c (2*D)∈Icc (0:ℝ) 1)
    (hQ : TendstoUniformlyOn (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square D))
    (t T : ℕ→ℝ) (ht : Tendsto t atTop atTop) (hT : Tendsto T atTop atTop)
    (hDT : ∀n,D≤T n) (hTt : ∀n,T n≤t n) {M : ℝ}
    (hmass : Tendsto (fun n => ∫u in (0:ℝ)..T n,d.R (t n) u) atTop (𝓝 M)) :
    Tendsto (fun n => prefixTraceMass h D (t n) (T n)) atTop (𝓝 (c (2*D)*M)) := by
  have hb := physical_bounds_of_equations h
  have hf : ContinuousOn (fun u => ‖prefixVector h (u-D) u‖^2) (Ici D) := by
    have hn := (prefixRankOne_continuousOn h hb D).norm
    apply (hn.mono (Ici_subset_Ici.mpr hD)).congr
    intro u hu
    simp only [DisjointCausalStrips.prefixRankOne,HilbertSchmidtTensor.rankOne,norm_pure,pow_two]
  have hf01 : ∀u∈Ici D,‖prefixVector h (u-D) u‖^2∈Icc (0:ℝ) 1 := by
    intro u hu
    have hn := prefixVector_norm_le_one h hb (u-D) (hD.trans hu)
    exact ⟨sq_nonneg _,by nlinarith [norm_nonneg (prefixVector h (u-D) u)]⟩
  have hflim : Tendsto (fun u : ℝ => ‖prefixVector h (u-D) u‖^2) atTop (𝓝 (c (2*D))) := by
    have hshift : Tendsto (fun u : ℝ => u-D) atTop atTop := by
      simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-D) tendsto_id
    have hh := ((center_real_norm_limit h hD hQ).comp hshift).pow 2
    simpa only [localCenter,sub_add_cancel,Real.sq_sqrt hc.1,Function.comp_def] using hh
  have he := initial_interval_response_mass_tendsto_zero h hr hrow t ht hD le_rfl
  have hmass' : Tendsto (fun n => ∫u in D..T n,d.R (t n) u) atTop (𝓝 M) := by
    have hDmass := initial_interval_response_mass_tendsto_zero h hr hrow t ht le_rfl hD
    have hs : Tendsto (fun n => (∫u in (0:ℝ)..T n,d.R (t n) u)-(∫u in (0:ℝ)..D,d.R (t n) u)) atTop (𝓝 M) := by
      simpa only [sub_zero] using hmass.sub hDmass
    apply hs.congr'
    exact Eventually.of_forall (fun n => by
      dsimp only
      rw [←intervalIntegral.integral_add_adjacent_intervals
        ((response_continuousOn_interval h le_rfl (hDT n |>.trans (hTt n))).intervalIntegrable_of_Icc hD)
        ((response_continuousOn_interval h hD (hTt n)).intervalIntegrable_of_Icc (hDT n))]
      ring)
  exact PositiveRowAverage.positive_row_average_tendsto hT hDT
    (fun n => response_continuousOn_interval h hD (hTt n))
    (fun n u hu => hb.2 (t n) u (hD.trans hu.1) (hu.2.trans (hTt n))) hf hf01 hc hflim hmass'
    (fun K hDK => initial_interval_response_mass_tendsto_zero h hr hrow t ht hD hDK)

end SphericalAging.CausalTraceMassLimit
