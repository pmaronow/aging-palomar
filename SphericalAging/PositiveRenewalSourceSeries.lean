module

public import SphericalAging.PositiveRenewalDRI
public import SphericalAging.PositiveRenewalWalk

public section

/-! The measurable-test version of the manuscript renewal series with its
[0,x] cutoff and ordinary real Bochner integrals, under full DRI and only
the first moment. The source Darboux definition alone does not guarantee
measurability for arbitrary singular increment laws. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalSourceSeries
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalDRI PositiveRenewalNormalization PositiveRenewalSeries PositiveRenewalWalk
open DirectRiemannGrid DirectRiemannCriterion RenewalFirstMoment AbsorptionCutoff.Renewal

@[expose] def causalReal (z : ℝ → ℝ) : ℝ → ℝ := (Ici 0).indicator z

theorem causalReal_nonnegative {z : ℝ → ℝ} (hn : ∀t : ℝ,0≤t → 0≤z t) (t : ℝ) :
    0≤causalReal z t := indicator_nonneg hn t

theorem causalReal_ofReal (z : ℝ → ℝ) (t : ℝ) :
    ENNReal.ofReal (causalReal z t)=causalDensity (fun s => ENNReal.ofReal (z s)) t := by
  by_cases ht : t∈Ici (0:ℝ)
  · rw [causalReal,causalDensity,indicator_of_mem ht,indicator_of_mem ht]
  · rw [causalReal,causalDensity,indicator_of_notMem ht,indicator_of_notMem ht,ENNReal.ofReal_zero]

theorem dri_causalReal_bound {z : ℝ → ℝ} (hn : ∀t : ℝ,0≤t → 0≤z t)
    (hdri : DirectlyRiemannIntegrable (fun t => ENNReal.ofReal (z t))) :
    ∀t : ℝ,‖causalReal z t‖≤(∑'n : ℕ,upperCell (fun s => ENNReal.ofReal (z s)) 1 n).toReal := by
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (causalReal_nonnegative hn t)]
  by_cases ht : 0≤t
  · rw [causalReal,indicator_of_mem (show t∈Ici (0:ℝ) from ht)]
    have hcell : t∈closedCell 1 ⌊t⌋₊ := by
      change (⌊t⌋₊:ℝ)*1≤t ∧ t≤((⌊t⌋₊:ℝ)+1)*1
      simpa only [mul_one] using ⟨Nat.floor_le ht,(Nat.lt_floor_add_one t).le⟩
    have hb := (le_upperCell (z:=fun s => ENNReal.ofReal (z s)) hcell).trans (ENNReal.le_tsum ⌊t⌋₊)
    have hreal := ENNReal.toReal_mono (dri_upper_weights_finite hdri (by norm_num : (0:ℝ)<1)) hb
    simpa only [ENNReal.toReal_ofReal (hn t ht)] using hreal
  · rw [causalReal,indicator_of_notMem (show t∉Ici (0:ℝ) from ht)]
    exact ENNReal.toReal_nonneg

theorem convPow_nonnegative_ae {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (n : ℕ) : ∀ᵐ y ∂convPow μ n,0≤y := by
  rw [←partialSum_map_law μ n]
  apply (ae_map_iff (partialSum_measurable n).aemeasurable measurableSet_Ici).mpr
  exact (positive_increments_ae hp).mono (fun ω hω => partialSum_nonnegative hω n)

theorem renewalTerm_eq_causalReal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (z : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    renewalTerm μ z x n=∫y,causalReal z (x-y) ∂convPow μ n := by
  unfold renewalTerm
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [convPow_nonnegative_ae hp n] with y hy
  by_cases hyx : y≤x
  · rw [indicator_of_mem (show y∈Icc 0 x from ⟨hy,hyx⟩),causalReal,
      indicator_of_mem (show x-y∈Ici (0:ℝ) from sub_nonneg.mpr hyx)]
  · rw [indicator_of_notMem (show y∉Icc 0 x from fun h => hyx h.2),causalReal,
      indicator_of_notMem (show x-y∉Ici (0:ℝ) from not_le.mpr (sub_neg.mpr (lt_of_not_ge hyx)))]

theorem ofReal_renewalTerm_causal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {z : ℝ → ℝ}
    (hm : Measurable (causalReal z)) (hn : ∀t : ℝ,0≤t → 0≤z t)
    (hdri : DirectlyRiemannIntegrable (fun t => ENNReal.ofReal (z t))) (x : ℝ) (n : ℕ) :
    ENNReal.ofReal (renewalTerm μ z x n)=
      ∫⁻y,causalDensity (fun t => ENNReal.ofReal (z t)) (x-y) ∂convPow μ n := by
  rw [renewalTerm_eq_causalReal hp]
  have hi : Integrable (fun y : ℝ => causalReal z (x-y)) (convPow μ n) :=
    Integrable.of_bound ((hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      _ (Eventually.of_forall (fun y => dri_causalReal_bound hn hdri (x-y)))
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun y => causalReal_nonnegative hn (x-y)))]
  simp_rw [causalReal_ofReal]

theorem source_renewal_hasSum {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {z : ℝ → ℝ}
    (hm : Measurable (causalReal z)) (hn : ∀t : ℝ,0≤t → 0≤z t)
    (hdri : DirectlyRiemannIntegrable (fun t => ENNReal.ofReal (z t))) (x : ℝ) :
    HasSum (renewalTerm μ z x) (nnAverage μ (causalDensity (fun t => ENNReal.ofReal (z t))) x).toReal := by
  have heq : (∑'n : ℕ,ENNReal.ofReal (renewalTerm μ z x n))=
      nnAverage μ (causalDensity (fun t => ENNReal.ofReal (z t))) x := by
    simp_rw [ofReal_renewalTerm_causal hp hm hn hdri x]
    exact (lintegral_renewalMeasure μ _).symm
  have hfinite : (∑'n : ℕ,ENNReal.ofReal (renewalTerm μ z x n))≠∞ :=
    heq ▸ dri_renewal_integral_finite hp hdri x
  have hs : Summable (renewalTerm μ z x) := by
    have ht := ENNReal.summable_toReal hfinite
    simpa only [ENNReal.toReal_ofReal (renewalTerm_nonnegative hn x _)] using ht
  have hsum : (∑'n : ℕ,renewalTerm μ z x n)=
      (nnAverage μ (causalDensity (fun t => ENNReal.ofReal (z t))) x).toReal := by
    have ht := congrArg ENNReal.toReal heq
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at ht
    simpa only [ENNReal.toReal_ofReal (renewalTerm_nonnegative hn x _)] using ht
  exact hsum ▸ hs.hasSum

/-- The explicit measurable-test version of source Theorem 16.10: its actual
[0,x] renewal series, full direct Riemann integrability, source arithmetic
definition, and only an actual finite first moment. Causal Borel measurability
is visible because the original Darboux definition alone does not imply it. -/
theorem first_moment_source_key_renewal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ)
    {z : ℝ → ℝ} (hm : Measurable (causalReal z)) (hn : ∀t : ℝ,0≤t → 0≤z t)
    (hdri : DirectlyRiemannIntegrable (fun t => ENNReal.ofReal (z t))) :
    (∀x : ℝ,Summable (renewalTerm μ z x)) ∧
    Tendsto (fun x : ℝ => ∑'n : ℕ,renewalTerm μ z x n) atTop
      (𝓝 ((∫t in Ici 0,z t)/(∫y : ℝ,y ∂μ))) := by
  have hci : Integrable (causalReal z) := by
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Eventually.of_forall (causalReal_nonnegative hn))).mp
    simp_rw [causalReal_ofReal]
    rw [causalDensity,lintegral_indicator measurableSet_Ici]
    exact dri_causal_integral_finite hdri
  have hIntegral : (∫⁻t in Ici 0,ENNReal.ofReal (z t)).toReal=∫t in Ici 0,z t := by
    have he := ofReal_integral_eq_lintegral_ofReal hci (Eventually.of_forall (causalReal_nonnegative hn))
    simp_rw [causalReal_ofReal] at he
    rw [causalDensity,lintegral_indicator measurableSet_Ici] at he
    have ht := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal (integral_nonneg (causalReal_nonnegative hn))] at ht
    rw [causalReal,integral_indicator measurableSet_Ici] at ht
    exact ht.symm
  refine ⟨fun x => (source_renewal_hasSum hp hm hn hdri x).summable,?_⟩
  have ht := first_moment_dri_key_renewal hp hna hi hdri
  rw [hIntegral] at ht
  exact ht.congr' (Eventually.of_forall (fun x => (source_renewal_hasSum hp hm hn hdri x).tsum_eq.symm))

end
end SphericalAging.PositiveRenewalSourceSeries
