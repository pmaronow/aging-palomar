module

public import SphericalAging.PositiveRenewalWalk
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

public section

/-! Actual first-entry events and their independence from the future iid
renewal increments. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalFirstEntry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalWalk AbsorptionCutoff.Renewal

/-- First entry of the actual partial-sum walk into [t,infinity). -/
@[expose] def entrySet (t : ℝ) (k : ℕ) : Set WalkSpace :=
  {ω | t≤partialSum k ω ∧ ∀j : ℕ,j<k → partialSum j ω<t}

@[expose] def prefixVector (k : ℕ) (ω : WalkSpace) : (Finset.range k) → ℝ := fun i => ω i
@[expose] def prefixExtension (k : ℕ) (v : (Finset.range k) → ℝ) : WalkSpace :=
  fun j => if hj : j<k then v ⟨j,Finset.mem_range.mpr hj⟩ else 0

@[expose] def prefixEntrySet (t : ℝ) (k : ℕ) : Set ((Finset.range k) → ℝ) :=
  prefixExtension k ⁻¹' entrySet t k

theorem prefixExtension_measurable (k : ℕ) : Measurable (prefixExtension k) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j<k
  · simpa only [prefixExtension,dif_pos hj] using (measurable_pi_apply (⟨j,Finset.mem_range.mpr hj⟩ : Finset.range k))
  · simpa only [prefixExtension,dif_neg hj] using (measurable_const : Measurable (fun _ : (Finset.range k) → ℝ => (0:ℝ)))

theorem entrySet_measurable (t : ℝ) (k : ℕ) : MeasurableSet (entrySet t k) := by
  apply (measurableSet_le measurable_const (partialSum_measurable k)).inter
  have heq : {ω : WalkSpace | ∀j : ℕ,j<k → partialSum j ω<t}=
      ⋂ j : ℕ,{ω : WalkSpace | j<k → partialSum j ω<t} := by ext; simp
  change MeasurableSet {ω : WalkSpace | ∀j : ℕ,j<k → partialSum j ω<t}
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j<k
  · simpa only [hj,true_implies] using measurableSet_lt (partialSum_measurable j) measurable_const
  · simp only [hj,false_implies,setOf_true]
    exact MeasurableSet.univ

theorem prefixEntrySet_measurable (t : ℝ) (k : ℕ) : MeasurableSet (prefixEntrySet t k) :=
  (entrySet_measurable t k).preimage (prefixExtension_measurable k)

theorem partialSum_prefixExtension (k n : ℕ) (hn : n≤k) (ω : WalkSpace) :
    partialSum n (prefixExtension k (prefixVector k ω))=partialSum n ω := by
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i<k := (Finset.mem_range.mp hi).trans_le hn
  simp only [prefixExtension,prefixVector,dif_pos hik]

theorem entrySet_eq_prefix_preimage (t : ℝ) (k : ℕ) :
    entrySet t k=prefixVector k ⁻¹' prefixEntrySet t k := by
  ext ω
  change (t≤partialSum k ω ∧ ∀j : ℕ,j<k → partialSum j ω<t)↔
    (t≤partialSum k (prefixExtension k (prefixVector k ω)) ∧
      ∀j : ℕ,j<k → partialSum j (prefixExtension k (prefixVector k ω))<t)
  rw [partialSum_prefixExtension k k le_rfl]
  constructor
  · rintro ⟨h,hj⟩
    refine ⟨h,fun j hjk => ?_⟩
    rw [partialSum_prefixExtension k j hjk.le]
    exact hj j hjk
  · rintro ⟨h,hj⟩
    refine ⟨h,fun j hjk => ?_⟩
    rw [←partialSum_prefixExtension k j hjk.le]
    exact hj j hjk

theorem prefixVector_independent_future (μ : Measure ℝ) [IsProbabilityMeasure μ] (k n : ℕ) :
    IndepFun (prefixVector k) (futureSum k n) (walkLaw μ) := by
  have hd : Disjoint (Finset.range k) (Finset.Ico k (k+n)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_range.mp hi).not_ge (Finset.mem_Ico.mp hj).1
  have hv := (increments_independent μ).indepFun_finset (Finset.range k)
    (Finset.Ico k (k+n)) hd (fun i : ℕ => measurable_pi_apply i)
  have hs : Measurable (fun v : (Finset.Ico k (k+n)) → ℝ => ∑i,v i) := by fun_prop
  have hh := hv.comp measurable_id hs
  have heq : (fun ω : WalkSpace => ∑i : (Finset.Ico k (k+n)),ω i)=futureSum k n := by
    funext ω
    rw [futureSum_eq_Ico]
    exact Finset.sum_coe_sort _ _
  change IndepFun (prefixVector k) (fun ω : WalkSpace => ∑i : (Finset.Ico k (k+n)),ω i) (walkLaw μ) at hh
  rw [heq] at hh
  exact hh

/-- Actual first-entry/future factorization, including the literal future
convolution-power interval probability. -/
theorem first_entry_future_measure (μ : Measure ℝ) [IsProbabilityMeasure μ] (t L : ℝ) (k n : ℕ) :
    walkLaw μ (entrySet t k ∩ futureSum k n ⁻¹' Icc 0 L)=
      walkLaw μ (entrySet t k)*convPow μ n (Icc 0 L) := by
  have hi := (prefixVector_independent_future μ k n).measure_inter_preimage_eq_mul
    (prefixEntrySet t k) (Icc 0 L) (prefixEntrySet_measurable t k) measurableSet_Icc
  rw [←entrySet_eq_prefix_preimage] at hi
  have hm : walkLaw μ (futureSum k n ⁻¹' Icc 0 L)=convPow μ n (Icc 0 L) := by
    rw [←futureSum_map_law μ k n,Measure.map_apply (show Measurable (futureSum k n) by
      exact (partialSum_measurable n).comp (measurable_pi_iff.mpr fun i => measurable_pi_apply (k+i))) measurableSet_Icc]
  rw [hm] at hi
  exact hi

theorem entrySet_pairwise_disjoint (t : ℝ) : Pairwise (fun k n : ℕ => Disjoint (entrySet t k) (entrySet t n)) := by
  intro k n hkn
  have key : ∀k n : ℕ,k<n → Disjoint (entrySet t k) (entrySet t n) := by
    intro k n hkn
    apply disjoint_left.mpr
    intro ω hk hn
    exact (hn.2 k hkn).not_ge hk.1
  rcases lt_or_gt_of_ne hkn with h|h
  · exact key k n h
  · exact (key n k h).symm

theorem entrySet_total_mass_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (∑' k : ℕ,walkLaw μ (entrySet t k))≤1 := by
  rw [←measure_iUnion (entrySet_pairwise_disjoint t) (fun k => entrySet_measurable t k)]
  exact prob_le_one

/-- On the true common positive-increment event, a visit to [t,t+L] has a
unique earlier first entry, followed by a positive partial sum at most L. -/
theorem visit_first_entry_cover {ω : WalkSpace} (hp : ∀j : ℕ,0<ω j)
    {t L : ℝ} {n : ℕ} (hn : partialSum n ω∈Icc t (t+L)) :
    ∃k : ℕ,k≤n ∧ ω∈entrySet t k ∧ futureSum k (n-k) ω∈Icc 0 L := by
  have hex : ∃k : ℕ,t≤partialSum k ω := ⟨n,hn.1⟩
  let k := Nat.find hex
  have hk : t≤partialSum k ω := Nat.find_spec hex
  have hkn : k≤n := Nat.find_min' hex hn.1
  have hearlier : ∀j : ℕ,j<k → partialSum j ω<t := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min hex hj)
  have hsum : partialSum n ω=partialSum k ω+futureSum k (n-k) ω := by
    simpa only [Nat.add_sub_of_le hkn] using partialSum_add k (n-k) ω
  have hfutureNN : 0≤futureSum k (n-k) ω :=
    partialSum_nonnegative (fun j => hp (k+j)) (n-k)
  refine ⟨k,hkn,⟨hk,hearlier⟩,hfutureNN,?_⟩
  linarith [hn.2]

end
end SphericalAging.PositiveRenewalFirstEntry
