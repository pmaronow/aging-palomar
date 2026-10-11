module

public import SphericalAging.DirectRiemannGrid
public import Mathlib.Topology.Order.Compact

public section

/-! The full direct Riemann integrability criterion: every mesh has finite
actual Darboux sums, and both sums tend to the actual integral as the mesh
approaches zero from the right. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.DirectRiemannCriterion
noncomputable section
set_option backward.isDefEq.respectTransparency false
open DirectRiemannGrid

/-- The literal definition in the source, with extended nonnegative sums. -/
@[expose] def DirectlyRiemannIntegrable (z : ℝ → ℝ≥0∞) : Prop :=
  (∀ h : ℝ,0<h → upperSum z h≠∞ ∧ lowerSum z h≠∞) ∧
  Tendsto (upperSum z) (𝓝[>] (0:ℝ)) (𝓝 (∫⁻ x in Ici 0,z x)) ∧
  Tendsto (lowerSum z) (𝓝[>] (0:ℝ)) (𝓝 (∫⁻ x in Ici 0,z x))

theorem closedCell_distance {h x t : ℝ} (hh : 0<h) (hx : 0≤x)
    (ht : t∈closedCell h ⌊x/h⌋₊) : |t-x|≤h := by
  have hg := gridCell_floor hh hx
  change (⌊x/h⌋₊:ℝ)*h≤x ∧ x<((⌊x/h⌋₊:ℝ)+1)*h at hg
  change (⌊x/h⌋₊:ℝ)*h≤t ∧ t≤((⌊x/h⌋₊:ℝ)+1)*h at ht
  rw [abs_le]
  constructor <;> nlinarith

theorem closedCell_nonnegative {h : ℝ} (hh : 0<h) {n : ℕ} {t : ℝ}
    (ht : t∈closedCell h n) : 0≤t :=
  (mul_nonneg n.cast_nonneg hh.le).trans ht.1

theorem upperDensity_tendsto {z : ℝ → ℝ≥0∞} {x : ℝ} (hx : 0<x)
    (hz : ContinuousAt z x) :
    Tendsto (fun h : ℝ => upperDensity z h x) (𝓝[>] (0:ℝ)) (𝓝 (z x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hxp : x∈closedCell h ⌊x/h⌋₊ :=
      ⟨(gridCell_floor hh hx.le).1,(gridCell_floor hh hx.le).2.le⟩
    rw [upperDensity,gridDensity_at hh hx.le]
    exact hb.trans_le (le_upperCell hxp)
  · intro b hb
    obtain ⟨c,hzc,hcb⟩ := exists_between hb
    have hnear : ∀ᶠ t in 𝓝 x,z t<c := hz.tendsto.eventually (Iio_mem_nhds hzc)
    obtain ⟨δ,hδ,hδz⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),h<δ :=
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hsmall] with h hh hs
    have hbound : upperCell z h ⌊x/h⌋₊≤c := by
      apply iSup₂_le
      intro t ht
      have hd := closedCell_distance hh hx.le ht
      exact (hδz (by simpa only [Real.dist_eq] using hd.trans_lt hs)).le
    rw [upperDensity,gridDensity_at hh hx.le]
    exact hbound.trans_lt hcb

theorem lowerDensity_tendsto {z : ℝ → ℝ≥0∞} {x : ℝ} (hx : 0<x)
    (hz : ContinuousAt z x) :
    Tendsto (fun h : ℝ => lowerDensity z h x) (𝓝[>] (0:ℝ)) (𝓝 (z x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨c,hbc,hcz⟩ := exists_between hb
    have hnear : ∀ᶠ t in 𝓝 x,c<z t := hz.tendsto.eventually (Ioi_mem_nhds hcz)
    obtain ⟨δ,hδ,hδz⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),h<δ :=
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hsmall] with h hh hs
    have hbound : c≤lowerCell z h ⌊x/h⌋₊ := by
      apply le_iInf
      intro t
      have hd := closedCell_distance hh hx.le t.property
      exact (hδz (by simpa only [Real.dist_eq] using hd.trans_lt hs)).le
    rw [lowerDensity,gridDensity_at hh hx.le]
    exact hbc.trans_le hbound
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hxp : x∈closedCell h ⌊x/h⌋₊ :=
      ⟨(gridCell_floor hh hx.le).1,(gridCell_floor hh hx.le).2.le⟩
    rw [lowerDensity,gridDensity_at hh hx.le]
    exact (lowerCell_le hxp).trans_lt hb

theorem lowerDensity_le_upperDensity {z : ℝ → ℝ≥0∞} {h : ℝ} (hh : 0<h) (x : ℝ) :
    lowerDensity z h x≤upperDensity z h x := by
  by_cases hx : 0≤x
  · rw [lowerDensity,upperDensity,gridDensity_at hh hx,gridDensity_at hh hx]
    exact lowerCell_le_upperCell hh _
  · rw [lowerDensity,upperDensity,gridDensity_negative hh (lt_of_not_ge hx),
      gridDensity_negative hh (lt_of_not_ge hx)]

theorem directlyRiemannIntegrable_of_continuous_unit_sums
    {z : ℝ → ℝ≥0∞} (hz : ContinuousOn z (Ici 0))
    (hunit : (∑' k : ℕ,upperCell z 1 k)≠∞) : DirectlyRiemannIntegrable z := by
  have hbound : ∫⁻ x,broadMajorant z 1 x≠∞ := by
    rw [lintegral_broadMajorant z (by norm_num : (0:ℝ)≤1)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit
  have hevent : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),0<h ∧ h≤1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with h hh h1
    exact ⟨hh,h1.le⟩
  have hlim (which : Bool) :
      Tendsto (fun h : ℝ => ∫⁻ x,(if which then upperDensity z h x else lowerDensity z h x))
        (𝓝[>] (0:ℝ)) (𝓝 (∫⁻ x,(Ici 0).indicator z x)) := by
    apply tendsto_lintegral_filter_of_dominated_convergence (broadMajorant z 1)
    · exact .of_forall fun h => by cases which <;> exact gridDensity_measurable _ h
    · filter_upwards [hevent] with h hh
      apply Filter.Eventually.of_forall
      intro x
      cases which
      · exact (lowerDensity_le_upperDensity hh.1 x).trans (upperDensity_le_broadMajorant hh.1 hh.2 x)
      · exact upperDensity_le_broadMajorant hh.1 hh.2 x
    · exact hbound
    · filter_upwards [ae_iff.mpr (by simp : volume ({x : ℝ | ¬ x≠0})=0)] with x hx0
      rcases lt_or_gt_of_ne hx0 with hx|hx
      · have heq : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
            (if which then upperDensity z h x else lowerDensity z h x)=0 := by
          filter_upwards [self_mem_nhdsWithin] with h hh
          cases which <;> exact gridDensity_negative hh hx _
        have hval : (Ici 0).indicator z x=0 := indicator_of_notMem hx.not_ge _
        rw [hval]
        exact tendsto_const_nhds.congr' (heq.mono fun h hh => hh.symm)
      · have hcx : ContinuousAt z x := (hz x hx.le).continuousAt (Ici_mem_nhds hx)
        rw [indicator_of_mem (show x∈Ici 0 from hx.le)]
        cases which
        · exact lowerDensity_tendsto hx hcx
        · exact upperDensity_tendsto hx hcx
  refine ⟨fun h hh => ⟨upperSum_finite hunit hh,lowerSum_finite hunit hh⟩,?_,?_⟩
  · have hl := hlim true
    simp only [if_pos rfl,lintegral_indicator measurableSet_Ici] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact lintegral_gridDensity _ hh
  · have hl := hlim false
    simp only [Bool.false_eq_true,ite_false,lintegral_indicator measurableSet_Ici] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact lintegral_gridDensity _ hh

end
end SphericalAging.DirectRiemannCriterion
