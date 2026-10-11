module

public import SphericalAging.FiniteTriangleFrom
public import SphericalAging.BackwardResponse

public section

/-! Primitive identification of the causal response row. The triangular and
rectangular interchanges are proved from continuity and compact integrability;
zero primitives identify their continuous integrands including endpoints. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace SphericalAging.ResponsePrimitiveInterchange
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Zero prefixes determine a continuous integrand on a nondegenerate interval. -/
theorem eq_zero_of_prefix_integrals {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ}
    (ha : 0<a) (hzero : ∀ s ∈ Icc 0 a,(∫ v in (0 : ℝ)..s,f v)=0) :
    ∀ v ∈ Icc 0 a,f v=0 := by
  have hi : EqOn f (fun _ => 0) (Ioo 0 a) := by
    intro v hv
    have hd := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 v)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    have he : (fun s => (0 : ℝ)) =ᶠ[𝓝 v] (fun s => ∫ w in (0 : ℝ)..s,f w) := by
      filter_upwards [isOpen_Ioo.mem_nhds hv] with s hs
      exact (hzero s ⟨hs.1.le,hs.2.le⟩).symm
    exact (hd.congr_of_eventuallyEq he).unique (hasDerivAt_const v (0 : ℝ))
  have hh := hi.closure hf continuous_const
  rw [closure_Ioo ha.ne] at hh
  exact hh

/-- Rectangular Fubini follows from the continuous compact rectangle bound. -/
theorem rectangle_integral_swap {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (a b c d : ℝ) :
    (∫ u in a..b,∫ v in c..d,F u v)=∫ v in c..d,∫ u in a..b,F u v := by
  apply intervalIntegral_intervalIntegral_swap
  exact (hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

/-- The Brownian primitive is saturated at the state time. -/
@[expose] def responsePrimitive (R : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..min t s,R t v

@[expose] def gammaSlope (μ : ℝ → ℝ) (K R : ℝ → ℝ → ℝ) (u s : ℝ) : ℝ :=
  -μ u*responsePrimitive R u s+∫ r in (0 : ℝ)..u,K u r*responsePrimitive R r s

@[expose] def responseSlope (μ : ℝ → ℝ) (K R : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  -μ u*R u v+∫ r in v..u,K u r*R r v

lemma responseSlope_continuous {μ : ℝ → ℝ} {K R : ℝ → ℝ → ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R)) :
    Continuous (Function.uncurry (responseSlope μ K R)) := by
  have hF : Continuous (Function.uncurry (fun q : ℝ×ℝ => fun r => K q.1 r*R r q.2)) :=
    (hK.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hR.comp (continuous_snd.prodMk continuous_fst.snd))
  exact ((hμ.comp continuous_fst).neg.mul hR).add
    (BackwardResponse.continuous_integral_endpoints hF continuous_snd continuous_fst)

/-- The true triangular memory exchange, with the primitive truncated at min(r,s). -/
theorem responseSlope_prefix {μ : ℝ → ℝ} {K R : ℝ → ℝ → ℝ}
    (hK : Continuous (Function.uncurry K)) (hR : Continuous (Function.uncurry R))
    {u s : ℝ} (hs : 0≤s) (hsu : s≤u) :
    (∫ v in (0 : ℝ)..s,responseSlope μ K R u v)=gammaSlope μ K R u s := by
  have hmem := TriangleUniqueness.weighted_triangle_memory_swap hR hK
    (continuous_const (y := (1 : ℝ))) hs hsu
  simp only [one_mul,mul_one] at hmem
  have hrow : Continuous (fun v => ∫ r in v..u,K u r*R r v) := by
    apply BackwardResponse.continuous_integral_endpoints
    · exact (hK.comp (continuous_const.prodMk continuous_snd)).mul
        (hR.comp (continuous_snd.prodMk continuous_fst))
    · exact continuous_id
    · exact continuous_const
  have hRu : Continuous (fun v => R u v) := hR.comp (continuous_const.prodMk continuous_id)
  simp only [responseSlope]
  rw [intervalIntegral.integral_add
    ((hRu.const_mul (-μ u)).intervalIntegrable (μ := volume) 0 s)
    (hrow.intervalIntegrable 0 s),intervalIntegral.integral_const_mul,hmem]
  simp only [gammaSlope,responsePrimitive,min_eq_right hsu]

/-- Prefixes of the response defect are exactly defects of the Γ integral row. -/
theorem discrepancy_prefix {μ : ℝ → ℝ} {K R : ℝ → ℝ → ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R)) {a t s : ℝ}
    (hs : 0≤s) (hsa : s≤a) (hat : a≤t) :
    (∫ v in (0 : ℝ)..s,R t v-R a v-∫ u in a..t,responseSlope μ K R u v)=
      responsePrimitive R t s-responsePrimitive R a s-∫ u in a..t,gammaSlope μ K R u s := by
  have hS := responseSlope_continuous hμ hK hR
  have hInt : Continuous (fun v => ∫ u in a..t,responseSlope μ K R u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v u => responseSlope μ K R u v)
      (hS.comp continuous_swap) a t
  have hRt : Continuous (fun v => R t v) := hR.comp (continuous_const.prodMk continuous_id)
  have hRa : Continuous (fun v => R a v) := hR.comp (continuous_const.prodMk continuous_id)
  rw [intervalIntegral.integral_sub
    (f := fun v => R t v-R a v)
    (g := fun v => ∫ u in a..t,responseSlope μ K R u v)
    ((hRt.sub hRa).intervalIntegrable (μ := volume) 0 s)
    (hInt.intervalIntegrable 0 s),
    intervalIntegral.integral_sub (f := fun v => R t v) (g := fun v => R a v)
      (hRt.intervalIntegrable (μ := volume) 0 s)
      (hRa.intervalIntegrable (μ := volume) 0 s),
    rectangle_integral_swap (F := fun v u => responseSlope μ K R u v) (hS.comp continuous_swap) 0 s a t]
  simp only [responsePrimitive,min_eq_right hsa,min_eq_right (hsa.trans hat)]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hat] at hu
  exact responseSlope_prefix hK hR hs (hsa.trans hu.1)

/-- An exact Γ primitive row identifies the response row, including v=a.
The nondegenerate a>0 requirement is necessary for primitive uniqueness. -/
theorem response_row_of_gamma_row {μ : ℝ → ℝ} {K R Γ : ℝ → ℝ → ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R)) {a t : ℝ} (ha : 0<a) (hat : a≤t)
    (hprimitive : ∀ u s,Γ u s=responsePrimitive R u s)
    (hrow : ∀ s ∈ Icc 0 a,Γ t s-Γ a s=∫ u in a..t,
      -μ u*Γ u s+∫ r in (0 : ℝ)..u,K u r*Γ r s) :
    ∀ v ∈ Icc 0 a,R t v-R a v=∫ u in a..t,responseSlope μ K R u v := by
  have hS := responseSlope_continuous hμ hK hR
  have hF : Continuous (fun v => R t v-R a v-∫ u in a..t,responseSlope μ K R u v) :=
    ((hR.comp (continuous_const.prodMk continuous_id)).sub
      (hR.comp (continuous_const.prodMk continuous_id))).sub
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun v u => responseSlope μ K R u v)
        (hS.comp continuous_swap) a t)
  have hz : ∀ s ∈ Icc 0 a,
      (∫ v in (0 : ℝ)..s,R t v-R a v-∫ u in a..t,responseSlope μ K R u v)=0 := by
    intro s hs
    rw [discrepancy_prefix hμ hK hR hs.1 hs.2 hat]
    have hh := hrow s hs
    simp only [hprimitive] at hh
    exact sub_eq_zero.mpr hh
  intro v hv
  exact sub_eq_zero.mp (eq_zero_of_prefix_integrals hF ha hz v hv)

end SphericalAging.ResponsePrimitiveInterchange
