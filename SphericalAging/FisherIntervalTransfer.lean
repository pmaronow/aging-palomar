module

public import SphericalAging.FisherLimitClockDecay
public import Mathlib.Analysis.Calculus.Deriv.Slope

public section

/-! Analytic transfer of finite Fisher interval estimates to a genuine
derivative. The right-continuity supplied by the constructed Fisher limit is
enough; a pointwise convergence premise for finite Fisher values is unnecessary. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.FisherIntervalTransfer
open Set Filter MeasureTheory
open scoped Topology

theorem interval_integral_tendsto_of_L1loc {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hi : ∀ n,IntegrableOn (F n) (Ioi 0)) (hfi : IntegrableOn f (Ioi 0))
    (hL1 : ∀ T : ℝ,Tendsto (fun n => ∫ u in Ioc 0 T,|F n u-f u|) atTop (𝓝 0))
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    Tendsto (fun n => ∫ u in s..t,F n u) atTop (𝓝 (∫ u in s..t,f u)) := by
  have hsub : Ioc s t⊆Ioc 0 t := fun u hu => ⟨lt_of_le_of_lt hs hu.1,hu.2⟩
  have hzero : Ioc (0 : ℝ) t⊆Ioi 0 := fun _ hu => hu.1
  have hbound n : |(∫ u in s..t,F n u)-(∫ u in s..t,f u)|≤
      (∫ u in Ioc 0 t,|F n u-f u|) := by
    have hdi : IntegrableOn (fun u => F n u-f u) (Ioc 0 t) :=
      ((hi n).sub hfi).mono_set hzero
    have hni : IntervalIntegrable (F n) volume s t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr ((hi n).mono_set (hsub.trans hzero))
    have hfi' : IntervalIntegrable f volume s t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr (hfi.mono_set (hsub.trans hzero))
    rw [← intervalIntegral.integral_sub hni hfi',intervalIntegral.integral_of_le hst]
    exact (abs_integral_le_integral_abs).trans
      (setIntegral_mono_set hdi.abs (ae_of_all _ fun u => abs_nonneg _)
        (ae_of_all volume hsub))
  have hh : Tendsto (fun n => |(∫ u in s..t,F n u)-(∫ u in s..t,f u)|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hbound (hL1 t)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using hh

/-- A true one-sided derivative follows from the integrated square estimate.
This is the final analytic step converting the limiting interval current
estimate to the source Fisher majorant. -/
theorem derivative_square_le_of_interval_bound {U f : ℝ → ℝ} {D s t : ℝ}
    (hst : s<t) (hU : HasDerivAt U D s) (hfm : StronglyMeasurable f)
    (hfc : ContinuousWithinAt f (Ici s) s)
    (hbound : ∀ v,s<v → v≤t → (U v-U s)^2≤(v-s)*(∫ u in s..v,f u)) :
    D^2≤f s := by
  have hp : HasDerivWithinAt (fun v => ∫ u in s..v,f u) (f s) (Ici s) s :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (by simp : IntervalIntegrable f volume s s)
      hfm.stronglyMeasurableAtFilter (hfc.mono Ioi_subset_Ici_self)
  have hAvg : Tendsto (fun v => (∫ u in s..v,f u)/(v-s)) (𝓝[>] s) (𝓝 (f s)) := by
    have he : Ici s\{s}=Ioi s := by ext v;simp
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hp
    rw [he] at h
    have heFun : slope (fun v => ∫ u in s..v,f u) s=
        (fun v => (∫ u in s..v,f u)/(v-s)) := by
      funext v
      rw [slope_def_field,intervalIntegral.integral_same,sub_zero]
    rw [heFun] at h
    exact h
  have hSlope := (hU.tendsto_slope.mono_left (nhdsGT_le_nhdsNE s)).pow 2
  apply le_of_tendsto_of_tendsto hSlope hAvg
  filter_upwards [Ioo_mem_nhdsGT hst] with v hv
  rw [slope_def_field,div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hv.1))).mpr
  have he : (∫ u in s..v,f u)/(v-s)*(v-s)^2=(v-s)*(∫ u in s..v,f u) := by
    field_simp
  rw [he]
  exact hbound v hv.1 hv.2.le

/-- Passage of actual finite interval estimates to the limit, followed by
the true derivative estimate. The finite interval bound can be supplied by
the already proved spherical PDE current identity and its Fisher estimate. -/
theorem derivative_square_le_of_finite_intervals
    {U : ℕ → ℝ → ℝ} {V f : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {D s t : ℝ}
    (hs : 0≤s) (hst : s<t)
    (hU : ∀ x,0≤x → x≤t → Tendsto (fun n => U n x) atTop (𝓝 (V x)))
    (hi : ∀ n,IntegrableOn (F n) (Ioi 0)) (hfi : IntegrableOn f (Ioi 0))
    (hL1 : ∀ T : ℝ,Tendsto (fun n => ∫ u in Ioc 0 T,|F n u-f u|) atTop (𝓝 0))
    (hfm : StronglyMeasurable f) (hfc : ContinuousWithinAt f (Ici s) s)
    (hV : HasDerivAt V D s)
    (hbound : ∀ n v,s<v → v≤t → (U n v-U n s)^2≤(v-s)*(∫ u in s..v,F n u)) :
    D^2≤f s := by
  apply derivative_square_le_of_interval_bound hst hV hfm hfc
  intro v hsv hvt
  exact le_of_tendsto_of_tendsto (((hU v (hs.trans hsv.le) hvt).sub (hU s hs hst.le)).pow 2)
    ((interval_integral_tendsto_of_L1loc hi hfi hL1 hs hsv.le).const_mul (v-s))
    (Eventually.of_forall fun n => hbound n v hsv hvt)

end SphericalAging.FisherIntervalTransfer
