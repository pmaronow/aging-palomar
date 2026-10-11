module

public import SphericalAging.BackwardStrongL2

public section

/-! Source Theorem 11.5 with literal fixed-wait suprema and actual half-line
L2 norms. Its inputs are precisely the preceding CK physical bounds,
fixed-wait correlation forgetting, Fisher domination and response localization.
No backward-derivative convergence conclusion is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.BackwardStrongTheorem
open CKSpecification EarlierCovariance GreenCovariance StrongBackwardDefect
  EarlierSmoothing EarlierDerivativeForgetting BackwardRowL2 BackwardStrongL2

@[expose] def fixedWaitSup (f : ℝ→ℝ→ℝ) (S t : ℝ) : ℝ :=
  sSup ((fun s => |f t s|) '' Icc 0 S)

/-- Uniform convergence on the literal compact earlier interval implies
convergence of its literal supremum. -/
theorem fixedWaitSup_tendsto {f : ℝ→ℝ→ℝ} {S : ℝ} (hS : 0≤S)
    (hf : TendstoUniformlyOn f (fun _ => 0) atTop (Icc 0 S)) :
    Tendsto (fixedWaitSup f S) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu := Metric.tendstoUniformlyOn_iff.mp hf (ε/2) (by positivity)
  filter_upwards [hu] with t ht
  have hbound : ∀ x ∈ (fun s => |f t s|) '' Icc 0 S, x≤ε/2 := by
    rintro x ⟨s,hs,rfl⟩
    exact (show |f t s| < ε/2 from by
      simpa only [Real.dist_eq,zero_sub,abs_neg] using ht s hs).le
  have hb : BddAbove ((fun s => |f t s|) '' Icc 0 S) := ⟨ε/2,hbound⟩
  have hmem : |f t 0| ∈ (fun s => |f t s|) '' Icc 0 S :=
    ⟨0,⟨le_rfl,hS⟩,rfl⟩
  have hn : 0≤fixedWaitSup f S t :=
    (abs_nonneg _).trans (le_csSup hb hmem)
  have he : fixedWaitSup f S t≤ε/2 := csSup_le ⟨_,hmem⟩ hbound
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hn]
  linarith

/-- The exact indicator row in the manuscript, with the actual earlier slope. -/
@[expose] def sourceEarlierRow (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ→ℝ :=
  (Icc 0 t).indicator (fun v => earlierSlope p β d t (t-v))

theorem sourceEarlierRow_ae {p : ℕ} {β : ℝ} {d : CKData} {t : ℝ} (ht : 0≤t) :
    sourceEarlierRow p β d t=ᵐ[rayMeasure] earlierRow p β d t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  by_cases hvt : v≤t
  · have hcc : v∈Icc 0 t := ⟨hv.le,hvt⟩
    have hoc : v∈Ioc 0 t := ⟨hv,hvt⟩
    simp only [sourceEarlierRow,earlierRow,indicator_of_mem hcc,indicator_of_mem hoc]
    exact (clampedEarlierSlope_eq (sub_nonneg.mpr hvt) (sub_le_self t hv.le)).symm
  · simp only [sourceEarlierRow,earlierRow,
      indicator_of_notMem (show v∉Icc 0 t from fun hh => hvt hh.2),
      indicator_of_notMem (show v∉Ioc 0 t from fun hh => hvt hh.2)]

theorem sourceEarlierRow_memLp_two {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0≤t) :
    MemLp (sourceEarlierRow p β d t) 2 rayMeasure :=
  (memLp_congr_ae (sourceEarlierRow_ae ht)).mpr (earlierRow_memLp_two h t)

/-- Full local source Theorem 11.5. The L2 norm is the actual eLpNorm on
Lebesgue measure restricted to (0,∞), not a placeholder energy functional. -/
theorem strong_backward_fdt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ→ℝ} (ha : FisherMajorant p β d a) {r : ℝ→ℝ}
    (hr : ContinuousOn r (Ici 0)) (hpos : ∀ v,0≤v→0≤r v)
    (hmono : AntitoneOn r (Ici 0)) (hr0 : r 0≤1) (hi : IntegrableOn r (Ici 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (𝓝 0)) :
    (∀S : ℝ,0≤S→Tendsto (fixedWaitSup (earlierSlope p β d) S) atTop (𝓝 0)) ∧
    Tendsto (fun t => ∫ s in (0:ℝ)..t,|backwardDefect p β d t s|^2) atTop (𝓝 0) ∧
    Tendsto (fun t => (eLpNorm (fun v => sourceEarlierRow p β d t v-r v) 2 rayMeasure).toReal)
      atTop (𝓝 0) := by
  have hi2 : IntegrableOn (fun v => (r v)^2) (Ioi 0) :=
    (MonotoneResponseTail.square_integrable_ray hr hpos hmono hr0 hi).mono_set Ioi_subset_Ici_self
  refine ⟨fun S hS => fixedWaitSup_tendsto hS
    (earlierSlope_fixed_wait_uniform h hb hforget hS),?_,?_⟩
  · simpa only [sq_abs] using squared_backward_defect_tendsto h hb hforget ha
  · apply (backward_full_L2_tendsto h hb hforget ha hr hi2 hrow).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have he := eLpNorm_congr_ae ((sourceEarlierRow_ae (p:=p) (β:=β) (d:=d) ht).sub
      (Filter.EventuallyEq.rfl (f:=r))) (p:=2)
    exact (congrArg ENNReal.toReal he).symm

end SphericalAging.BackwardStrongTheorem
