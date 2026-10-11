module

public import SphericalAging.PositiveRenewalFirstEntry
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

public section

/-! A true uniform interval bound for every positive renewal law, obtained
from actual first-entry events and independent future increments. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalCellBound
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalWalk PositiveRenewalFirstEntry PositiveRenewalSeries AbsorptionCutoff.Renewal

/-- Extended nonnegative Cauchy product; no finite moment or summability
assumption on either factor is needed. -/
theorem ennreal_cauchy_product (a b : ℕ → ℝ≥0∞) :
    (∑' k,a k)*(∑' j,b j)=∑' n,∑k∈Finset.range (n+1),a k*b (n-k) := by
  conv_rhs =>
    congr
    ext n
    rw [←Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k j => a k*b j),
      ←Finset.sum_finset_coe,←tsum_fintype (L:=SummationFilter.unconditional _)]
  rw [←ENNReal.tsum_sigma]
  simp only [Finset.coe_sort_coe]
  have heq := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd :
      (Σn : ℕ,Finset.antidiagonal n)≃ℕ×ℕ).tsum_eq (fun p : ℕ×ℕ => a p.1*b p.2)
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply] at heq
  rw [heq]
  rw [ENNReal.tsum_prod' (f:=fun p : ℕ×ℕ => a p.1*b p.2)]
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

theorem convolution_visit_mass_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (t L : ℝ) (n : ℕ) :
    convPow μ n (Icc t (t+L))≤∑k∈Finset.range (n+1),
      walkLaw μ (entrySet t k)*convPow μ (n-k) (Icc 0 L) := by
  have hmap : walkLaw μ (partialSum n ⁻¹' Icc t (t+L))=convPow μ n (Icc t (t+L)) := by
    rw [←partialSum_map_law μ n,Measure.map_apply (partialSum_measurable n) measurableSet_Icc]
  let A : ℕ → Set WalkSpace := fun k => entrySet t k∩futureSum k (n-k) ⁻¹' Icc 0 L
  have hsub : ∀ᵐ ω ∂walkLaw μ,ω∈partialSum n ⁻¹' Icc t (t+L) →
      ω∈⋃k∈Finset.range (n+1),A k := by
    filter_upwards [positive_increments_ae hp] with ω hω hvisit
    obtain ⟨k,hkn,hentry,hfuture⟩ := visit_first_entry_cover hω hvisit
    exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hkn),hentry,hfuture⟩⟩
  calc
    _=walkLaw μ (partialSum n ⁻¹' Icc t (t+L)) := hmap.symm
    _≤walkLaw μ (⋃k∈Finset.range (n+1),A k) := measure_mono_ae hsub
    _≤∑k∈Finset.range (n+1),walkLaw μ (A k) := measure_biUnion_finset_le _ _
    _=∑k∈Finset.range (n+1),walkLaw μ (entrySet t k)*convPow μ (n-k) (Icc 0 L) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact first_entry_future_measure μ t L k (n-k)

/-- Genuine uniform renewal-cell bound with the actual near-origin renewal
mass as constant. No mean, second moment, nonarithmetic or density condition
is needed; positive support alone suffices. -/
theorem positive_renewal_interval_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (t L : ℝ) :
    renewalMeasure μ (Icc t (t+L))≤renewalMeasure μ (Icc 0 L) := by
  rw [renewalMeasure_apply μ measurableSet_Icc,renewalMeasure_apply μ measurableSet_Icc]
  calc
    _≤∑' n,∑k∈Finset.range (n+1),walkLaw μ (entrySet t k)*convPow μ (n-k) (Icc 0 L) :=
      ENNReal.tsum_le_tsum (convolution_visit_mass_bound hp t L)
    _=(∑' k,walkLaw μ (entrySet t k))*(∑' j,convPow μ j (Icc 0 L)) :=
      (ennreal_cauchy_product (fun k : ℕ => walkLaw μ (entrySet t k))
        (fun j : ℕ => convPow μ j (Icc 0 L))).symm
    _≤1*(∑' j,convPow μ j (Icc 0 L)) :=
      mul_le_mul (entrySet_total_mass_le_one μ t) le_rfl bot_le bot_le
    _=∑' j,convPow μ j (Icc 0 L) := one_mul _

/-- The uniform interval constant is actually finite by the proved positive
exponential-transform estimate. -/
theorem positive_renewal_uniform_finite_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (L : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀t : ℝ,renewalMeasure μ (Icc t (t+L))≤ENNReal.ofReal C := by
  refine ⟨(renewalMeasure μ (Icc 0 L)).toReal,ENNReal.toReal_nonneg,?_⟩
  intro t
  rw [ENNReal.ofReal_toReal (positive_renewal_locally_finite hp 0 L)]
  exact positive_renewal_interval_bound hp t L

end
end SphericalAging.PositiveRenewalCellBound
