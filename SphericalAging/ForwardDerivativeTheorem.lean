module

public import SphericalAging.WholeRowForwardDerivative
public import SphericalAging.CausalRowSup
public import SphericalAging.HankelLaplaceLaw
public import SphericalAging.CKPhysicalConsequences

public section

/-! Complete actual CK forward derivative theorem for all p>=3. The reflected
stationary law is constructed, the sharp envelope is proved, and both literal
whole-row suprema tend to zero. Inputs are precisely preceding stationary
selection/reflection and uniform response localization statements. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ForwardDerivativeTheorem
open CKSpecification CKPhysicalConsequences PrefixRectangleStability PrefixReflection
open HankelReflection HankelLaplaceLaw NonnegativeSpectralLaplace SpectralSharpSecond
open RemoteForwardDerivative WholeRowForwardDerivative CausalRowSup

structure Inputs {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (c r : ℝ→ℝ) (q : ℝ) : Prop where
  correlation_continuous : ContinuousOn c (Ici 0)
  response_continuous : ContinuousOn r (Ici 0)
  correlation_initial : c 0=1
  response_initial : r 0=1
  correlation_bound : ∀t : ℝ,0≤t→|c t|≤1
  plateau_limit : Tendsto c atTop (𝓝 q)
  fdt : ∀t : ℝ,0≤t→HasDerivWithinAt c (-r t) (Ici 0) t
  translated_correlation : ∀ A,0≤A→TendstoUniformlyOn
    (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2))
    (fun z => c |z.1-z.2|) atTop (square A)
  reflected_prefix : ∀ A,0≤A→TendstoUniformlyOn
    (fun T => Function.uncurry (futureKernel h T))
    (fun z => c (z.1+z.2)) atTop (square A)
  response_row : ∀ε : ℝ,0<ε→∀ᶠ t : ℝ in atTop,∀s : ℝ,0≤s→s≤t→|d.R t s-r (t-s)|≤ε

theorem profile_hankel {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) : HankelPositive c := by
  apply hankel_positive_of_prefix_limit (T:=fun n : ℕ => (n:ℝ)) h
  intro a b
  let A : ℝ := max (a:ℝ) (b:ℝ)
  have hA : 0≤A := a.coe_nonneg.trans (le_max_left _ _)
  have ha : (a:ℝ)∈Icc 0 A := ⟨a.coe_nonneg,le_max_left _ _⟩
  have hb : (b:ℝ)∈Icc 0 A := ⟨b.coe_nonneg,le_max_right _ _⟩
  have he := (H.reflected_prefix A hA).tendsto_at (x:=((a:ℝ),(b:ℝ))) ⟨ha,hb⟩
  simpa only [Function.comp_def,Function.uncurry_def] using he.comp tendsto_natCast_atTop_atTop

/-- Full source Theorem11.4, with actual causal one-sided derivative convention
at the diagonal. Every p>=3 is permitted by CKEquations.spin_ge_three. -/
theorem forward_derivative_theorem {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) :
    (∀L : ℝ,0<L→
      limsup (rowSup (correlationSlope p β d) L) atTop≤Real.sqrt (iteratedDeriv 2 c (2*L)) ∧
      Real.sqrt (iteratedDeriv 2 c (2*L))≤Real.sqrt (1-q)/(Real.exp 1*L)) ∧
    Tendsto (rowSup (fun t s => correlationSlope p β d t s+r (t-s)) 0) atTop (𝓝 0) ∧
    Tendsto (rowSup (fun t s => correlationSlope p β d t s+d.R t s) 0) atTop (𝓝 0) ∧
    (∀t : ℝ,0≤t→correlationSlope p β d t t= -1) ∧
    HasDerivWithinAt c (-1) (Ici 0) 0 := by
  have hH := profile_hankel H
  let ν := laplaceLaw c hH H.correlation_bound
  letI : IsProbabilityMeasure ν := laplaceLaw_probability hH H.correlation_bound H.correlation_initial
  have hν : ∀ᵐ x : ℝ ∂ν,0≤x := laplaceLaw_ae_nonnegative hH H.correlation_bound H.correlation_initial
  have hrep : ∀t : ℝ,0<t→c t=∫ x : ℝ,Real.exp (-x*t) ∂ν :=
    fun t ht => (integral_laplaceLaw hH H.correlation_bound H.correlation_initial H.correlation_continuous ht.le).symm
  have hderiv : ∀t : ℝ,0<t→HasDerivAt c (-r t) t :=
    fun t ht => (H.fdt t ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hb := physical_bounds_of_equations h
  have hsmooth : ContDiffOn ℝ 2 c (Ioi 0) := (spectralProfile_contDiffOn ν hν c hrep).of_le (by simp)
  have hwhole := whole_row_profile h hb H.correlation_continuous H.response_continuous hderiv
    ν hν hrep H.translated_correlation H.reflected_prefix
  refine ⟨?_,?_,?_,fun t ht => CKDiagonal.correlation_diagonal_slope h ht,?_⟩
  · intro L hL
    have hremote (ε : ℝ) (hε : 0<ε) := remote_forward_derivative h hb
      (eventually_ge_atTop (0:ℝ)) hsmooth H.reflected_prefix hL (ε:=ε) hε
    have hshift : Tendsto (fun t : ℝ => t-L) atTop atTop := by
      simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-L) tendsto_id
    constructor
    · apply rowSup_limsup_le (Real.sqrt_nonneg _)
      intro ε hε
      filter_upwards [hshift.eventually (hremote ε hε)] with t ht
      intro s hs hst
      simpa only [sub_add_cancel] using ht s hs hst
    · have hatom : ν.real {0}=q := laplaceLaw_zero_atom hH H.correlation_bound
        H.correlation_initial H.correlation_continuous H.plateau_limit
      have he := sqrt_second_bound ν hν hatom hL
      rw [spectralProfile_iteratedDeriv ν hν c hrep 2 (2*L) (by positivity)]
      norm_num at ⊢
      exact he
  · apply rowSup_tendsto_zero
    intro ε hε
    simpa only [sub_zero] using hwhole ε hε
  · apply rowSup_tendsto_zero
    intro ε hε
    filter_upwards [hwhole (ε/2) (by positivity),H.response_row (ε/2) (by positivity)] with t ht hR
    intro s hs hst
    have hst' : s≤t := by simpa only [sub_zero] using hst
    have he := abs_add_le (correlationSlope p β d t s+r (t-s)) (d.R t s-r (t-s))
    have hid : correlationSlope p β d t s+r (t-s)+(d.R t s-r (t-s))=
        correlationSlope p β d t s+d.R t s := by ring
    rw [hid] at he
    linarith [ht s hs hst',hR s hs hst']
  · simpa only [H.response_initial] using H.fdt 0 le_rfl

/-- The source formulas with exactly the ordinary causal-row suprema. -/
theorem forward_derivative_theorem_literal {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) :
    (∀L : ℝ,0<L→
      limsup (literalRowSup (correlationSlope p β d) L) atTop≤Real.sqrt (iteratedDeriv 2 c (2*L)) ∧
      Real.sqrt (iteratedDeriv 2 c (2*L))≤Real.sqrt (1-q)/(Real.exp 1*L)) ∧
    Tendsto (literalRowSup (fun t s => correlationSlope p β d t s+r (t-s)) 0) atTop (𝓝 0) ∧
    Tendsto (literalRowSup (fun t s => correlationSlope p β d t s+d.R t s) 0) atTop (𝓝 0) ∧
    (∀t : ℝ,0≤t→correlationSlope p β d t t= -1) ∧
    HasDerivWithinAt c (-1) (Ici 0) 0 := by
  obtain ⟨hremote,hprofile,hfdt,hdiag,hright⟩ := forward_derivative_theorem H
  refine ⟨?_,hprofile.congr' (rowSup_eventuallyEq_literal _ 0),
    hfdt.congr' (rowSup_eventuallyEq_literal _ 0),hdiag,hright⟩
  intro L hL
  have he := limsup_congr (rowSup_eventuallyEq_literal (correlationSlope p β d) L)
  rw [←he]
  exact hremote L hL

end SphericalAging.ForwardDerivativeTheorem
