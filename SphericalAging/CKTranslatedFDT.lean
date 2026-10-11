module

public import SphericalAging.CKTranslatedStationarity

public section

/-! The integral FDT relation of a genuine translated cluster is derived
by passing the actual late CK defect and response integrals to the limit. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.CKTranslatedFDT
open Set Filter MeasureTheory CKSpecification EarlierCovariance GreenCovariance
open CKPhysicalConsequences CKKernelBounds ResponseCompactness CKUniformLateEstimates StrongBackwardDefect
open scoped Topology

@[expose] def responseExtension (R : C(CausalOffsets,ℝ)) (z : ℝ×ℝ) : ℝ :=
  R ⟨(max z.1 z.2,z.2),le_max_right _ _⟩

theorem responseExtension_continuous (R : C(CausalOffsets,ℝ)) :
    Continuous (responseExtension R) :=
  R.continuous.comp (((continuous_fst.max continuous_snd).prodMk continuous_snd).subtype_mk _)

theorem responseExtension_eq (R : C(CausalOffsets,ℝ)) {x y : ℝ} (hyx : y≤x) :
    responseExtension R (x,y)=R ⟨(x,y),hyx⟩ := by
  unfold responseExtension
  congr 1
  apply Subtype.ext
  simp only [max_eq_left hyx]

theorem translated_response_integral_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {R : C(CausalOffsets,ℝ)}
    (hR : ∀ z : CausalOffsets,Tendsto
      (fun n => d.R (T n+z.1.1) (T n+z.1.2)) atTop (𝓝 (R z)))
    {x y : ℝ} (hyx : y≤x) :
    Tendsto (fun n => ∫ u in y..x,d.R (T n+x) (T n+u)) atTop
      (𝓝 (∫ u in y..x,responseExtension R (x,u))) := by
  let F : ℕ → ℝ → ℝ := fun n u => clampedResponse d (T n+x) (T n+u)
  have hfc n : Continuous (F n) := (clampedResponse_continuous h).comp
    (continuous_const.prodMk (continuous_const.add continuous_id))
  have hc : Continuous (fun u => responseExtension R (x,u)) :=
    (responseExtension_continuous R).comp (continuous_const.prodMk continuous_id)
  have hd := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc y x))
    (F := F) (f := fun u => responseExtension R (x,u)) (fun _ => (1:ℝ))
    (fun n => (hfc n).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact clampedResponse_abs_le_one h (physical_bounds_of_equations h) _ _) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [responseExtension_eq R hu.2]
      apply (hR ⟨(x,u),hu.2⟩).congr'
      filter_upwards [hT.eventually_ge_atTop (-y)] with n hn
      simpa only [F] using (clampedResponse_eq (u := T n+u) (t := T n+x)
        (by linarith [hu.1]) (by linarith [hu.2])).symm)
  rw [← intervalIntegral.integral_of_le hyx] at hd
  have he : (fun n => ∫ u in Ioc y x,F n u)=ᶠ[atTop]
      (fun n => ∫ u in y..x,d.R (T n+x) (T n+u)) := by
    filter_upwards [hT.eventually_ge_atTop (-y)] with n hn
    rw [← intervalIntegral.integral_of_le hyx]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hyx] at hu
    exact clampedResponse_eq (by linarith [hu.1]) (by linarith [hu.2])
  exact hd.congr' he

theorem translated_integratedDefect_tendsto_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {x y : ℝ} (hyx : y≤x) :
    Tendsto (fun n => integratedDefect d (T n+x) (T n+y)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => T n+y) atTop atTop := tendsto_atTop_add_const_right _ y hT
  have hb : Tendsto (fun n => Real.sqrt ((x-y)*tail a (T n+y))) atTop (𝓝 0) := by
    simpa only [mul_zero,Real.sqrt_zero,Function.comp_def] using
      ((tail_tendsto_zero a).comp hs).const_mul (x-y) |>.sqrt
  have hh : ∀ᶠ n in atTop,|integratedDefect d (T n+x) (T n+y)|≤
      Real.sqrt ((x-y)*tail a (T n+y)) := by
    filter_upwards [hs.eventually_ge_atTop 0] with n hn
    have hd := uniform_late_integrated_fdt h ha han (sub_nonneg.mpr hyx) hn le_rfl
      (sub_nonneg.mpr hyx) le_rfl
    have he : T n+y+(x-y)=T n+x := by ring
    simpa only [he] using hd
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hh) hb

theorem cluster_integrated_fdt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {C : ℝ×ℝ → ℝ} (hC : ∀ z : ℝ×ℝ,Tendsto
      (fun n => d.C (T n+z.1) (T n+z.2)) atTop (𝓝 (C z)))
    {R : C(CausalOffsets,ℝ)} (hR : ∀ z : CausalOffsets,Tendsto
      (fun n => d.R (T n+z.1.1) (T n+z.1.2)) atTop (𝓝 (R z)))
    {x y : ℝ} (hyx : y≤x) :
    (∫ u in y..x,responseExtension R (x,u))=1-C (x,y) := by
  have hp := ((tendsto_const_nhds (x := (1:ℝ))).sub (hC (x,y))).sub
    (translated_response_integral_tendsto h hT hR hyx)
  have hz := translated_integratedDefect_tendsto_zero h ha han hT hyx
  have he : (fun n => 1-d.C (T n+x) (T n+y)-
      (∫ u in y..x,d.R (T n+x) (T n+u)))=
      (fun n => integratedDefect d (T n+x) (T n+y)) := by
    funext n
    unfold integratedDefect
    rw [intervalIntegral.integral_comp_add_left]
  rw [he] at hp
  have hh := tendsto_nhds_unique hp hz
  linarith

end SphericalAging.CKTranslatedFDT
