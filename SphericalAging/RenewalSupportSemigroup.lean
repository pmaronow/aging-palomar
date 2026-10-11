module

public import SphericalAging.SemigroupTailDensity
public import SphericalAging.RenewalFirstMoment
public import Mathlib.MeasureTheory.Measure.Support

public section

/-! The actual positive support of a source nonarithmetic law generates an
additive semigroup which is eventually uniformly dense on the positive ray. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.RenewalSupportSemigroup
noncomputable section
set_option backward.isDefEq.respectTransparency false
open SemigroupTailDensity RenewalFirstMoment

@[expose] def supportSemigroup (μ : Measure ℝ) : AddSubmonoid ℝ := AddSubmonoid.closure μ.support

theorem support_nonnegative {μ : Measure ℝ} (hp : ∀ᵐ x ∂μ,0<x) :
    μ.support⊆Ici 0 := Measure.support_subset_of_isClosed isClosed_Ici (hp.mono fun x hx => hx.le)

theorem supportSemigroup_nonnegative {μ : Measure ℝ} (hp : ∀ᵐ x ∂μ,0<x) :
    ∀x∈supportSemigroup μ,0≤x := by
  intro x hx
  exact AddSubmonoid.closure_induction
    (fun x hx => support_nonnegative hp hx) (by norm_num)
    (fun x y hx hy hnx hny => add_nonneg hnx hny) hx

/-- An actual probability supported on an untranslated integer lattice is
arithmetic in the source's positive-natural-multiple definition. -/
theorem arithmetic_of_positive_ae_integer_lattice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ x ∂μ,0<x) {r : ℝ} (hr : r≠0)
    (hl : ∀ᵐ x ∂μ,∃k : ℤ,x=(k:ℝ)*r) : Arithmetic μ := by
  let h : ℝ := |r|
  have hh : 0<h := abs_pos.mpr hr
  have hs : ∀ᵐ x ∂μ,∃n : ℕ,0<n ∧ x=(n:ℝ)*h := by
    filter_upwards [hp,hl] with x hx hlx
    obtain ⟨k,hk⟩ := hlx
    have hj : ∃j : ℤ,x=(j:ℝ)*h := by
      rcases lt_or_gt_of_ne hr with hrneg|hrpos
      · refine ⟨-k,?_⟩
        simpa [h,abs_of_neg hrneg] using hk
      · exact ⟨k,by simpa only [h,abs_of_pos hrpos] using hk⟩
    obtain ⟨j,hj⟩ := hj
    have hj0 : 0<(j:ℝ) := by nlinarith
    have hjint : 0<j := by exact_mod_cast hj0
    have hjnat : ((j.toNat:ℕ):ℝ)=(j:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hjint.le
    refine ⟨j.toNat,?_,?_⟩
    · have hnat : (0:ℝ)<(j.toNat:ℝ) := by rw [hjnat];exact hj0
      exact_mod_cast hnat
    · rw [hjnat]
      exact hj
  have hc : {x : ℝ | ∃n : ℕ,0<n ∧ x=(n:ℝ)*h}.Countable := by
    apply (countable_range (fun n : ℕ => (n:ℝ)*h)).mono
    rintro x ⟨n,hn,hx⟩
    exact ⟨n,hx.symm⟩
  exact ⟨h,hh,(prob_compl_eq_zero_iff hc.measurableSet).mp (ae_iff.mp hs)⟩

theorem source_nonarithmetic_differenceGroup_dense {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ x ∂μ,0<x) (hna : ¬Arithmetic μ) :
    Dense (differenceGroup (supportSemigroup μ) : Set ℝ) := by
  let S := supportSemigroup μ
  rcases (differenceGroup S).dense_or_cyclic with hd|⟨r,hr⟩
  · exact hd
  · have hl : ∀ᵐ x ∂μ,∃k : ℤ,x=(k:ℝ)*r := by
      filter_upwards [Measure.support_mem_ae (μ:=μ)] with x hx
      have hxS : x∈S := AddSubmonoid.subset_closure hx
      have hxG : x∈differenceGroup S := submonoid_subset_differenceGroup S hxS
      rw [hr,AddSubgroup.mem_closure_singleton] at hxG
      obtain ⟨k,hk⟩ := hxG
      exact ⟨k,by simpa only [zsmul_eq_mul] using hk.symm⟩
    by_cases hr0 : r=0
    · have hf : ∀ᵐ x ∂μ,False := by
        filter_upwards [hp,hl] with x hx hlx
        obtain ⟨k,hk⟩ := hlx
        simp only [hr0,mul_zero] at hk
        linarith
      have hb : (1:ℝ≥0∞)=0 := by simpa using ae_iff.mp hf
      exact False.elim (one_ne_zero hb)
    · exact False.elim (hna (arithmetic_of_positive_ae_integer_lattice hp hr0 hl))

/-- A genuine source nonarithmetic positive law supplies eventual uniform
semigroup density, without any moment, regularity or density assumption on
its increment law. -/
theorem source_positive_support_eventually_dense {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ x ∂μ,0<x) (hna : ¬Arithmetic μ) {ε : ℝ} (hε : 0<ε) :
    ∃T : ℝ,∀t : ℝ,T≤t → ∃y∈supportSemigroup μ,y≤t ∧ t-y<ε :=
  eventually_left_approximation (supportSemigroup μ) (supportSemigroup_nonnegative hp)
    (source_nonarithmetic_differenceGroup_dense hp hna) hε

end
end SphericalAging.RenewalSupportSemigroup
