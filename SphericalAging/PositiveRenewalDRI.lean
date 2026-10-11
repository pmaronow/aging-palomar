module

public import SphericalAging.PositiveRenewalStepLimit
public import SphericalAging.DirectRiemannCriterion

public section

/-! Genuine full first-moment key renewal theorem for the literal source
Darboux definition of direct Riemann integrability. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalDRI
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalStepLimit PositiveRenewalNormalization PositiveRenewalSeries
open DirectRiemannGrid DirectRiemannCriterion RenewalFirstMoment AbsorptionCutoff.Renewal

@[expose] def causalDensity (Z : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ := (Ici 0).indicator Z

theorem causalDensity_darboux_bounds (Z : ℝ → ℝ≥0∞) {h : ℝ} (hh : 0<h) (t : ℝ) :
    lowerDensity Z h t≤causalDensity Z t ∧ causalDensity Z t≤upperDensity Z h t := by
  by_cases ht : 0≤t
  · rw [causalDensity,indicator_of_mem (show t∈Ici (0:ℝ) from ht),lowerDensity,upperDensity,
      gridDensity_at hh ht,gridDensity_at hh ht]
    have hc : t∈closedCell h ⌊t/h⌋₊ := ⟨(gridCell_floor hh ht).1,(gridCell_floor hh ht).2.le⟩
    exact ⟨lowerCell_le hc,le_upperCell hc⟩
  · rw [causalDensity,indicator_of_notMem (show t∉Ici (0:ℝ) from ht),lowerDensity,upperDensity,
      gridDensity_negative hh (lt_of_not_ge ht),gridDensity_negative hh (lt_of_not_ge ht)]
    exact ⟨le_rfl,le_rfl⟩

theorem dri_upper_weights_finite {Z : ℝ → ℝ≥0∞} (hdri : DirectlyRiemannIntegrable Z)
    {h : ℝ} (hh : 0<h) : (∑'n : ℕ,upperCell Z h n)≠∞ := by
  intro hbad
  apply (hdri.1 h hh).1
  rw [upperSum,hbad,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hh))]

theorem dri_lower_weights_finite {Z : ℝ → ℝ≥0∞} (hdri : DirectlyRiemannIntegrable Z)
    {h : ℝ} (hh : 0<h) : (∑'n : ℕ,lowerCell Z h n)≠∞ :=
  ne_top_of_le_ne_top (dri_upper_weights_finite hdri hh)
    (ENNReal.tsum_le_tsum (lowerCell_le_upperCell hh))

theorem dri_causal_integral_finite {Z : ℝ → ℝ≥0∞} (hdri : DirectlyRiemannIntegrable Z) :
    (∫⁻t in Ici 0,Z t)≠∞ := by
  apply ne_top_of_le_ne_top (hdri.1 1 (by norm_num)).1
  rw [←lintegral_indicator measurableSet_Ici]
  change (∫⁻t,causalDensity Z t)≤upperSum Z 1
  rw [upperSum,←lintegral_gridDensity _ (by norm_num : (0:ℝ)<1)]
  exact lintegral_mono (fun t => (causalDensity_darboux_bounds Z (by norm_num) t).2)

theorem dri_renewal_integral_finite {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {Z : ℝ → ℝ≥0∞} (hdri : DirectlyRiemannIntegrable Z) (x : ℝ) :
    nnAverage μ (causalDensity Z) x≠∞ := by
  apply ne_top_of_le_ne_top (nnAverage_gridDensity_finite hp
    (dri_upper_weights_finite hdri (by norm_num : (0:ℝ)<1)) 1 x)
  exact lintegral_mono (fun y => (causalDensity_darboux_bounds Z (by norm_num) (x-y)).2)

/-- Literal source DRI key renewal limit, proved from positive support,
source nonarithmeticity and finite first moment only. The test need not be
continuous or Lipschitz; all Darboux grid approximation is derived. -/
theorem first_moment_dri_key_renewal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ)
    {Z : ℝ → ℝ≥0∞} (hdri : DirectlyRiemannIntegrable Z) :
    Tendsto (fun x : ℝ => (nnAverage μ (causalDensity Z) x).toReal) atTop
      (𝓝 ((∫⁻t in Ici 0,Z t).toReal/(∫y : ℝ,y ∂μ))) := by
  let F := fun x : ℝ => (nnAverage μ (causalDensity Z) x).toReal
  let m := ∫y : ℝ,y ∂μ
  let A := (∫⁻t in Ici 0,Z t).toReal/m
  have hm : 0<m := mean_positive_of_positive_integrable hp hi
  have hgridU (h : ℝ) (hh : 0<h) : Tendsto (fun x : ℝ => (nnAverage μ (upperDensity Z h) x).toReal)
      atTop (𝓝 ((upperSum Z h).toReal/m)) := by
    have ht := first_moment_grid_renewal hp hna hi (dri_upper_weights_finite hdri hh) hh
    simpa only [upperDensity,upperSum,ENNReal.toReal_mul,ENNReal.toReal_ofReal hh.le,m] using ht
  have hgridL (h : ℝ) (hh : 0<h) : Tendsto (fun x : ℝ => (nnAverage μ (lowerDensity Z h) x).toReal)
      atTop (𝓝 ((lowerSum Z h).toReal/m)) := by
    have ht := first_moment_grid_renewal hp hna hi (dri_lower_weights_finite hdri hh) hh
    simpa only [lowerDensity,lowerSum,ENNReal.toReal_mul,ENNReal.toReal_ofReal hh.le,m] using ht
  have hcompU (h : ℝ) (hh : 0<h) (x : ℝ) : F x≤(nnAverage μ (upperDensity Z h) x).toReal :=
    ENNReal.toReal_mono (nnAverage_gridDensity_finite hp (dri_upper_weights_finite hdri hh) h x)
      (lintegral_mono (fun y => (causalDensity_darboux_bounds Z hh (x-y)).2))
  have hcompL (h : ℝ) (hh : 0<h) (x : ℝ) : (nnAverage μ (lowerDensity Z h) x).toReal≤F x :=
    ENNReal.toReal_mono (dri_renewal_integral_finite hp hdri x)
      (lintegral_mono (fun y => (causalDensity_darboux_bounds Z hh (x-y)).1))
  have hupper : atTop.IsBoundedUnder (·≤·) F :=
    (hgridU 1 (by norm_num)).isBoundedUnder_le.mono_le (Eventually.of_forall (hcompU 1 (by norm_num)))
  have hlower : atTop.IsBoundedUnder (·≥·) F :=
    ⟨0,show ∀ᶠx : ℝ in atTop,0≤F x from Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)⟩
  have hSup : limsup F atTop≤A := by
    have hlim : Tendsto (fun h : ℝ => (upperSum Z h).toReal/m) (𝓝[>] (0:ℝ)) (𝓝 A) :=
      ((ENNReal.tendsto_toReal (dri_causal_integral_finite hdri)).comp hdri.2.1).div_const m
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hl := limsup_le_limsup (Eventually.of_forall (hcompU h hh))
      hlower.isCoboundedUnder_le (hgridU h hh).isBoundedUnder_le
    rwa [(hgridU h hh).limsup_eq] at hl
  have hInf : A≤liminf F atTop := by
    have hlim : Tendsto (fun h : ℝ => (lowerSum Z h).toReal/m) (𝓝[>] (0:ℝ)) (𝓝 A) :=
      ((ENNReal.tendsto_toReal (dri_causal_integral_finite hdri)).comp hdri.2.2).div_const m
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hl := liminf_le_liminf (Eventually.of_forall (hcompL h hh))
      (hgridL h hh).isBoundedUnder_ge hupper.isCoboundedUnder_ge
    rwa [(hgridL h hh).liminf_eq] at hl
  exact tendsto_of_le_liminf_of_limsup_le hInf hSup hupper hlower

end
end SphericalAging.PositiveRenewalDRI
