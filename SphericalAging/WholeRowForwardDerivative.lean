module

public import SphericalAging.RemoteForwardDerivative
public import SphericalAging.RecentForwardDerivative
public import SphericalAging.NonnegativeLaplaceDecay
public import SphericalAging.SpectralSharpSecond

public section

/-! The entire causal-row forward FDT estimate, including the diagonal,
for every p>=3. All derivative limits are obtained from genuine CK dynamics,
reflected Gram convergence and a finite nonnegative-frequency spectral law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.WholeRowForwardDerivative
open CKSpecification PrefixRectangleStability PrefixReflection
open RemoteForwardDerivative RecentForwardDerivative
open SpectralLaplace (laplaceMoment)
open NonnegativeSpectralLaplace NonnegativeLaplaceDecay

theorem whole_row_profile {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {c r : ℝ→ℝ}
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0))
    (hd : ∀t : ℝ,0<t→HasDerivAt c (-r t) t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ᵐ x : ℝ ∂ν,0≤x)
    (hrep : ∀t : ℝ,0<t→c t=∫ x : ℝ,Real.exp (-x*t) ∂ν)
    (hC : ∀ A,0≤A→TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hQ : ∀ A,0≤A→TendstoUniformlyOn
      (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square A)) :
    ∀ε : ℝ,0<ε→∀ᶠ t : ℝ in atTop,∀s : ℝ,0≤s→s≤t→
      |correlationSlope p β d t s+r (t-s)|≤ε := by
  have hsmooth : ContDiffOn ℝ 2 c (Ioi 0) :=
    (spectralProfile_contDiffOn ν hν c hrep).of_le (by simp)
  have hrrep : ∀t : ℝ,0<t→ r t=laplaceMoment ν 1 t := by
    intro t ht
    have he := (spectralProfile_hasDerivAt ν hν c hrep t ht).unique (hd t ht)
    linarith
  have hrzero : Tendsto r atTop (𝓝 0) := momentProfile_tendsto_zero ν hν (by norm_num) hrrep
  have h2zero : Tendsto (fun L : ℝ => Real.sqrt (iteratedDeriv 2 c (2*L))) atTop (𝓝 0) := by
    have ht : Tendsto (fun L : ℝ => 2*L) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
    have hl := ((laplaceMoment_tendsto_zero ν hν (n:=2) (by norm_num)).comp ht).sqrt
    simp only [Real.sqrt_zero] at hl
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    rw [spectralProfile_iteratedDeriv ν hν c hrep 2 (2*L) (by positivity)]
    norm_num
  intro ε hε
  have hsum : Tendsto (fun L : ℝ => Real.sqrt (iteratedDeriv 2 c (2*L))+r L) atTop (𝓝 0) := by
    simpa only [zero_add] using h2zero.add hrzero
  have hsmall := hsum.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))
  obtain ⟨L,hL,hsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and hsmall).exists
  have ht0 : ∀ᶠ T : ℝ in atTop,0≤T := eventually_ge_atTop 0
  have hremote := remote_forward_derivative h hb ht0 hsmooth hQ hL (by positivity : 0<ε/4)
  have hrecent := translated_correlationSlope_uniform h hb ht0 hc hr.neg hd hL.le
    (hC (L+1) (by positivity))
  have hnear := Metric.tendstoUniformlyOn_iff.mp hrecent (ε/2) (by positivity)
  have hshift : Tendsto (fun t : ℝ => t-L) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-L) tendsto_id
  have hmono : AntitoneOn r (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact hr.mono Ioi_subset_Ici_self
    · intro t ht
      have ht : 0<t := by simpa only [isOpen_Ioi.interior_eq,mem_Ioi] using ht
      have hlocal : r =ᶠ[𝓝 t] laplaceMoment ν 1 := by
        filter_upwards [Ioi_mem_nhds ht] with u hu
        exact hrrep u hu
      exact ((laplaceMoment_hasDerivAt ν hν 1 t ht).congr_of_eventuallyEq hlocal).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht : 0<t := by simpa only [isOpen_Ioi.interior_eq,mem_Ioi] using ht
      have hlocal : r =ᶠ[𝓝 t] laplaceMoment ν 1 := by
        filter_upwards [Ioi_mem_nhds ht] with u hu
        exact hrrep u hu
      rw [hlocal.deriv_eq,(laplaceMoment_hasDerivAt ν hν 1 t ht).deriv]
      exact neg_nonpos.mpr (laplaceMoment_nonneg ν hν 2 t)
  have hrnonneg : ∀t : ℝ,0<t→0≤r t := by
    intro t ht
    rw [hrrep t ht]
    exact laplaceMoment_nonneg ν hν 1 t
  filter_upwards [hshift.eventually hremote,hshift.eventually hnear,eventually_ge_atTop L]
    with t hremote hnear ht
  intro s hs hst
  by_cases hsr : s≤t-L
  · have ha := hremote s hs hsr
    rw [sub_add_cancel] at ha
    have hv : 0<t-s := by linarith
    have hrv : r (t-s)≤r L := hmono hL hv (by linarith)
    have he := abs_add_le (correlationSlope p β d t s) (r (t-s))
    rw [abs_of_nonneg (hrnonneg _ hv)] at he
    linarith
  · have hz : (L,s-(t-L))∈triangle L := by
      exact ⟨⟨hL.le,le_rfl⟩,⟨by linarith,by linarith⟩⟩
    have hh := hnear (L,s-(t-L)) hz
    have he1 : t-L+L=t := by ring
    have he2 : t-L+(s-(t-L))=s := by ring
    have he3 : L-(s-(t-L))=t-s := by ring
    simp only [Real.dist_eq,he1,he2,he3] at hh
    have hid : (-r) (t-s)-correlationSlope p β d t s=
        -(correlationSlope p β d t s+r (t-s)) := by
      simp only [Pi.neg_apply]
      ring
    rw [hid,abs_neg] at hh
    linarith

end SphericalAging.WholeRowForwardDerivative
