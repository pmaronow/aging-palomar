module

public import SphericalAging.DirectRiemannReal
public import SphericalAging.RenewalFirstMoment

public section

/-! Actual local finiteness and renewal-series summability for positive
increment laws, without a second moment or translated-lattice premise. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalSeries
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AbsorptionCutoff.Renewal DirectRiemannGrid DirectRiemannReal

/-- The exact source renewal summand, including the original [0,x] cutoff. -/
@[expose] def renewalTerm (μ : Measure ℝ) (z : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∫ y in Icc 0 x,z (x-y) ∂convPow μ n

theorem positive_renewal_locally_finite {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (a b : ℝ) : renewalMeasure μ (Icc a b)≠∞ := by
  exact (renewalMeasure_Icc_lt_top (by norm_num : (0:ℝ)<1)
    (KeyRenewal.expTransform_lt_one_of_positive_support (by norm_num : (0:ℝ)<1) hp) a b).ne

theorem unit_suprema_global_bound {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (hn : ∀t : ℝ,0≤t → 0≤z t) (hu : Summable (fun k => realUpperCell z 1 k)) :
    ∃ B : ℝ,0≤B ∧ ∀t : ℝ,0≤t → z t≤B := by
  let B : ℝ := ∑' k,realUpperCell z 1 k
  refine ⟨B,tsum_nonneg (fun k => realUpperCell_nonnegative hz hn (by norm_num) k),?_⟩
  intro t ht
  have hm : t∈closedCell 1 ⌊t⌋₊ := by
    change (⌊t⌋₊:ℝ)*1≤t ∧ t≤((⌊t⌋₊:ℝ)+1)*1
    simpa using And.intro (Nat.floor_le ht) (Nat.lt_floor_add_one t).le
  obtain ⟨s,hs,heq,hmax⟩ := realUpperCell_attained hz (by norm_num : (0:ℝ)<1) ⌊t⌋₊
  calc
    z t≤realUpperCell z 1 ⌊t⌋₊ := by rw [heq];exact hmax t hm
    _≤B := hu.le_tsum ⌊t⌋₊ (fun k hk => realUpperCell_nonnegative hz hn (by norm_num) k)

theorem renewalTerm_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    {B : ℝ} (hn : ∀t : ℝ,0≤t → 0≤z t) (hb : ∀t : ℝ,0≤t → z t≤B)
    (x : ℝ) (n : ℕ) : IntegrableOn (fun y => z (x-y)) (Icc 0 x) (convPow μ n) := by
  have hc : ContinuousOn (fun y : ℝ => z (x-y)) (Icc 0 x) := by
    apply hz.comp (continuous_const.sub continuous_id).continuousOn
    intro y hy
    exact sub_nonneg.mpr hy.2
  apply Integrable.of_bound (hc.aestronglyMeasurable measurableSet_Icc) B
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (hn _ (sub_nonneg.mpr hy.2))]
  exact hb _ (sub_nonneg.mpr hy.2)

theorem renewalTerm_nonnegative {μ : Measure ℝ} {z : ℝ → ℝ}
    (hn : ∀t : ℝ,0≤t → 0≤z t) (x : ℝ) (n : ℕ) : 0≤renewalTerm μ z x n := by
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy
  exact hn _ (sub_nonneg.mpr hy.2)

theorem ofReal_renewalTerm {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    {B : ℝ} (hn : ∀t : ℝ,0≤t → 0≤z t) (hb : ∀t : ℝ,0≤t → z t≤B)
    (x : ℝ) (n : ℕ) :
    ENNReal.ofReal (renewalTerm μ z x n)=
      ∫⁻ y,(Icc 0 x).indicator (fun y => ENNReal.ofReal (z (x-y))) y ∂convPow μ n := by
  rw [lintegral_indicator measurableSet_Icc]
  apply ofReal_integral_eq_lintegral_ofReal (renewalTerm_integrable hz hn hb x n)
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy
  exact hn _ (sub_nonneg.mpr hy.2)

/-- Source positive support alone supplies local finiteness and summability
of the actual renewal series for every continuous unit-supremum-summable
nonnegative test. No renewal limit is used or assumed. -/
theorem actual_positive_renewal_series_summable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (hn : ∀t : ℝ,0≤t → 0≤z t) (hu : Summable (fun k => realUpperCell z 1 k))
    (x : ℝ) : Summable (renewalTerm μ z x) := by
  obtain ⟨B,hB,hb⟩ := unit_suprema_global_bound hz hn hu
  have hEq : (∑' n,ENNReal.ofReal (renewalTerm μ z x n))=
      ∫⁻ y,(Icc 0 x).indicator (fun y => ENNReal.ofReal (z (x-y))) y ∂renewalMeasure μ := by
    simp_rw [ofReal_renewalTerm hz hn hb x]
    rw [lintegral_renewalMeasure]
  have hbound : (∑' n,ENNReal.ofReal (renewalTerm μ z x n))≤
      ENNReal.ofReal B*renewalMeasure μ (Icc 0 x) := by
    rw [hEq,←setLIntegral_const]
    rw [←lintegral_indicator measurableSet_Icc]
    apply lintegral_mono
    intro y
    by_cases hy : y∈Icc 0 x
    · rw [indicator_of_mem hy,indicator_of_mem hy]
      exact ENNReal.ofReal_le_ofReal (hb _ (sub_nonneg.mpr hy.2))
    · rw [indicator_of_notMem hy,indicator_of_notMem hy]
  have hfinite := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (positive_renewal_locally_finite hp 0 x)) hbound
  have hs := ENNReal.summable_toReal hfinite
  simpa only [ENNReal.toReal_ofReal (renewalTerm_nonnegative hn x _)] using hs

end
end SphericalAging.PositiveRenewalSeries
