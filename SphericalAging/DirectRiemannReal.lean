module

public import SphericalAging.DirectRiemannCriterion
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

/-! Exact real-valued upper/lower Darboux sums and the source DRI criterion. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.DirectRiemannReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
open DirectRiemannGrid DirectRiemannCriterion

@[expose] def realUpperCell (z : ℝ → ℝ) (h : ℝ) (n : ℕ) : ℝ := sSup (z '' closedCell h n)
@[expose] def realLowerCell (z : ℝ → ℝ) (h : ℝ) (n : ℕ) : ℝ := sInf (z '' closedCell h n)
@[expose] def realUpperSum (z : ℝ → ℝ) (h : ℝ) : ℝ := h*∑' n,realUpperCell z h n
@[expose] def realLowerSum (z : ℝ → ℝ) (h : ℝ) : ℝ := h*∑' n,realLowerCell z h n

theorem closedCell_continuous {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    {h : ℝ} (hh : 0<h) (n : ℕ) : ContinuousOn z (closedCell h n) :=
  hz.mono (fun t ht => closedCell_nonnegative hh ht)

theorem realUpperCell_attained {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    {h : ℝ} (hh : 0<h) (n : ℕ) :
    ∃ t∈closedCell h n,realUpperCell z h n=z t ∧ ∀s∈closedCell h n,z s≤z t := by
  obtain ⟨t,ht,htmax⟩ := (isCompact_Icc : IsCompact (closedCell h n)).exists_isMaxOn
    (closedCell_nonempty hh n) (closedCell_continuous hz hh n)
  have hgreat : IsGreatest (z '' closedCell h n) (z t) := by
    refine ⟨mem_image_of_mem _ ht,?_⟩
    rintro y ⟨s,hs,rfl⟩
    exact htmax hs
  exact ⟨t,ht,hgreat.csSup_eq,fun s hs => htmax hs⟩

theorem realLowerCell_attained {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    {h : ℝ} (hh : 0<h) (n : ℕ) :
    ∃ t∈closedCell h n,realLowerCell z h n=z t ∧ ∀s∈closedCell h n,z t≤z s := by
  obtain ⟨t,ht,htmin⟩ := (isCompact_Icc : IsCompact (closedCell h n)).exists_isMinOn
    (closedCell_nonempty hh n) (closedCell_continuous hz hh n)
  have hleast : IsLeast (z '' closedCell h n) (z t) := by
    refine ⟨mem_image_of_mem _ ht,?_⟩
    rintro y ⟨s,hs,rfl⟩
    exact htmin hs
  exact ⟨t,ht,hleast.csInf_eq,fun s hs => htmin hs⟩

theorem upperCell_ofReal {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    {h : ℝ} (hh : 0<h) (n : ℕ) :
    upperCell (fun t => ENNReal.ofReal (z t)) h n=ENNReal.ofReal (realUpperCell z h n) := by
  obtain ⟨t,ht,heq,hmax⟩ := realUpperCell_attained hz hh n
  rw [heq]
  apply le_antisymm
  · exact iSup₂_le fun s hs => ENNReal.ofReal_le_ofReal (hmax s hs)
  · exact le_upperCell (z:=fun t => ENNReal.ofReal (z t)) ht

theorem lowerCell_ofReal {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    {h : ℝ} (hh : 0<h) (n : ℕ) :
    lowerCell (fun t => ENNReal.ofReal (z t)) h n=ENNReal.ofReal (realLowerCell z h n) := by
  obtain ⟨t,ht,heq,hmin⟩ := realLowerCell_attained hz hh n
  rw [heq]
  apply le_antisymm
  · exact lowerCell_le ht
  · exact le_iInf fun s => ENNReal.ofReal_le_ofReal (hmin s s.property)

theorem realUpperCell_nonnegative {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (hn : ∀t : ℝ,0≤t → 0≤z t) {h : ℝ} (hh : 0<h) (n : ℕ) :
    0≤realUpperCell z h n := by
  obtain ⟨t,ht,heq,hmax⟩ := realUpperCell_attained hz hh n
  rw [heq]
  exact hn t (closedCell_nonnegative hh ht)

theorem realLowerCell_nonnegative {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (hn : ∀t : ℝ,0≤t → 0≤z t) {h : ℝ} (hh : 0<h) (n : ℕ) :
    0≤realLowerCell z h n := by
  obtain ⟨t,ht,heq,hmin⟩ := realLowerCell_attained hz hh n
  rw [heq]
  exact hn t (closedCell_nonnegative hh ht)

theorem realUpperSum_eq_toReal {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (hn : ∀t : ℝ,0≤t → 0≤z t) {h : ℝ} (hh : 0<h) :
    realUpperSum z h=(upperSum (fun t => ENNReal.ofReal (z t)) h).toReal := by
  rw [upperSum,ENNReal.toReal_mul,ENNReal.tsum_toReal_eq]
  · simp only [upperCell_ofReal hz hh,ENNReal.toReal_ofReal (realUpperCell_nonnegative hz hn hh _),
      ENNReal.toReal_ofReal hh.le,realUpperSum]
  · intro n
    rw [upperCell_ofReal hz hh n]
    exact ENNReal.ofReal_ne_top

theorem realLowerSum_eq_toReal {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (hn : ∀t : ℝ,0≤t → 0≤z t) {h : ℝ} (hh : 0<h) :
    realLowerSum z h=(lowerSum (fun t => ENNReal.ofReal (z t)) h).toReal := by
  rw [lowerSum,ENNReal.toReal_mul,ENNReal.tsum_toReal_eq]
  · simp only [lowerCell_ofReal hz hh,ENNReal.toReal_ofReal (realLowerCell_nonnegative hz hn hh _),
      ENNReal.toReal_ofReal hh.le,realLowerSum]
  · intro n
    rw [lowerCell_ofReal hz hh n]
    exact ENNReal.ofReal_ne_top

/-- Literal full source `lem:sc-dri`, including actual ordinary supremum and
infimum sums, their summability at every positive mesh, and their common
limit equal to the actual Lebesgue integral. -/
theorem continuous_summable_unit_suprema_directly_riemann_integrable
    {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (hn : ∀t : ℝ,0≤t → 0≤z t)
    (hunit : Summable (fun n : ℕ => realUpperCell z 1 n)) :
    IntegrableOn z (Ici 0) volume ∧
    (∀h : ℝ,0<h → Summable (fun n => realUpperCell z h n) ∧
      Summable (fun n => realLowerCell z h n)) ∧
    Tendsto (realUpperSum z) (𝓝[>] (0:ℝ)) (𝓝 (∫ x in Ici 0,z x)) ∧
    Tendsto (realLowerSum z) (𝓝[>] (0:ℝ)) (𝓝 (∫ x in Ici 0,z x)) := by
  let Z := fun t : ℝ => ENNReal.ofReal (z t)
  have hsum : (∑' k,upperCell Z 1 k)≠∞ := by
    have heq : ∀k,upperCell Z 1 k=ENNReal.ofReal (realUpperCell z 1 k) :=
      upperCell_ofReal hz (by norm_num : (0:ℝ)<1)
    simpa only [heq] using hunit.tsum_ofReal_ne_top
  have hZ : ContinuousOn Z (Ici 0) := ENNReal.continuous_ofReal.comp_continuousOn hz
  have hdri := directlyRiemannIntegrable_of_continuous_unit_sums hZ hsum
  have hfinite : ∫⁻ x in Ici 0,Z x≠∞ := by
    apply ne_top_of_le_ne_top (upperSum_finite hsum (by norm_num : (0:ℝ)<1))
    change (∫⁻ x in Ici 0,Z x)≤ENNReal.ofReal 1*∑'n,upperCell Z 1 n
    rw [←lintegral_gridDensity _ (by norm_num : (0:ℝ)<1)]
    rw [←lintegral_indicator measurableSet_Ici]
    apply lintegral_mono
    intro x
    by_cases hx : 0≤x
    · rw [indicator_of_mem (show x∈Ici 0 from hx),gridDensity_at (by norm_num : (0:ℝ)<1) hx]
      exact le_upperCell ⟨(gridCell_floor (by norm_num : (0:ℝ)<1) hx).1,
        (gridCell_floor (by norm_num : (0:ℝ)<1) hx).2.le⟩
    · rw [indicator_of_notMem (show x∉Ici 0 from hx)]
      exact bot_le
  have hi : IntegrableOn z (Ici 0) volume := by
    refine ⟨hz.aestronglyMeasurable measurableSet_Ici,?_⟩
    change (∫⁻ x in Ici 0,‖z x‖ₑ)<∞
    apply lt_of_le_of_lt _ (lt_top_iff_ne_top.mpr hfinite)
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    rw [←ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hn x hx)]
  have htot : (∫⁻ x in Ici 0,Z x).toReal=∫ x in Ici 0,z x := by
    symm
    have hae : ∀ᵐ x : ℝ ∂volume.restrict (Ici 0),0≤x := self_mem_ae_restrict measurableSet_Ici
    exact integral_eq_lintegral_of_nonneg_ae (hae.mono fun x hx => hn x hx) hi.aestronglyMeasurable
  refine ⟨hi,?_,?_,?_⟩
  · intro h hh
    have hu := (ENNReal.lt_top_of_mul_ne_top_right (hdri.1 h hh).1
      (ENNReal.ofReal_ne_zero_iff.mpr hh)).ne
    have hl := (ENNReal.lt_top_of_mul_ne_top_right (hdri.1 h hh).2
      (ENNReal.ofReal_ne_zero_iff.mpr hh)).ne
    constructor
    · have hs := ENNReal.summable_toReal hu
      change Summable (fun n => (upperCell (fun t => ENNReal.ofReal (z t)) h n).toReal) at hs
      simpa only [upperCell_ofReal hz hh,ENNReal.toReal_ofReal (realUpperCell_nonnegative hz hn hh _)] using hs
    · have hs := ENNReal.summable_toReal hl
      change Summable (fun n => (lowerCell (fun t => ENNReal.ofReal (z t)) h n).toReal) at hs
      simpa only [lowerCell_ofReal hz hh,ENNReal.toReal_ofReal (realLowerCell_nonnegative hz hn hh _)] using hs
  · have hl := (ENNReal.tendsto_toReal hfinite).comp hdri.2.1
    rw [htot] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (realUpperSum_eq_toReal hz hn hh).symm
  · have hl := (ENNReal.tendsto_toReal hfinite).comp hdri.2.2
    rw [htot] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (realLowerSum_eq_toReal hz hn hh).symm

end
end SphericalAging.DirectRiemannReal
