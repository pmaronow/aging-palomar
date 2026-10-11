module

public import SphericalAging.ThermalTail
public import SphericalAging.StationarySpectralRepresentation
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

/-! Source stationary thermal conclusions from the constructed Hankel law.
The integrated response and its exact mass are derived by the improper FTC.
No thermal property or spectral representation is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace SphericalAging.ThermalStationary
open SpectralLaplace (laplaceMoment)
open NonnegativeSpectralLaplace HankelReflection HankelLaplaceLaw
open ThermalSpectral ThermalTail BackwardRowL2

theorem response_mass_from_fdt (c r : ℝ → ℝ) (q : ℝ)
    (hc : ContinuousOn c (Ici 0)) (hc0 : c 0=1)
    (hderiv : ∀t, 0<t → HasDerivAt c (-r t) t)
    (hrnonneg : ∀t, 0<t → 0≤r t) (hlim : Tendsto c atTop (𝓝 q)) :
    Integrable r rayMeasure ∧ (∫v : ℝ, r v ∂rayMeasure)=1-q := by
  have hcont : ContinuousWithinAt (fun t => -c t) (Ici 0) 0 :=
    (hc 0 (by simp)).neg
  have hd : ∀t∈Ioi (0 : ℝ), HasDerivAt (fun s => -c s) (r t) t := by
    intro t ht
    convert (hderiv t ht).neg using 1 <;> simp
  have hl : Tendsto (fun t => -c t) atTop (𝓝 (-q)) := hlim.neg
  have hi := integrableOn_Ioi_deriv_of_nonneg hcont hd hrnonneg hl
  have hm := integral_Ioi_of_hasDerivAt_of_nonneg hcont hd hrnonneg hl
  refine ⟨hi, ?_⟩
  change (∫v in Ioi (0 : ℝ), r v)=1-q
  rw [hm,hc0]
  ring

/-- The actual physical response bound and its derived integrated response
give its half-line L2 class. -/
theorem response_memLp_two_of_bound (r : ℝ → ℝ) (hi : Integrable r rayMeasure)
    (hb : ∀v : ℝ,0<v → 0≤r v ∧ r v≤1) : MemLp r 2 rayMeasure := by
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  apply hi.mono'
  · exact hi.aestronglyMeasurable.pow 2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    obtain ⟨hv0,hv1⟩ := hb v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith

/-- All stationary thermal properties from actual reflected positivity and
FDT. The finite probability law is constructed inside this theorem. -/
theorem hankel_thermal_properties (c r : ℝ → ℝ) (q : ℝ)
    (hH : HankelPositive c) (hb : ∀t, 0≤t → |c t|≤1)
    (hc0 : c 0=1) (hc : ContinuousOn c (Ici 0))
    (hderiv : ∀t, 0<t → HasDerivAt c (-r t) t)
    (hlim : Tendsto c atTop (𝓝 q)) :
    Integrable r rayMeasure ∧ (∫v : ℝ, r v ∂rayMeasure)=1-q ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (thermalProfile r) (Ioi 0) ∧
    (∀n : ℕ, ∀t : ℝ, 0<t → 0≤(-1 : ℝ)^n * iteratedDeriv n (thermalProfile r) t) ∧
    Tendsto (thermalProfile r) atTop (𝓝 0) := by
  let ν := laplaceLaw c hH hb
  letI : IsProbabilityMeasure ν := laplaceLaw_probability hH hb hc0
  have hν : ∀ᵐ x : ℝ ∂ν,0≤x := laplaceLaw_ae_nonnegative hH hb hc0
  have hrep : ∀t : ℝ,0<t → c t=∫x : ℝ,Real.exp (-x*t) ∂ν :=
    fun t ht => (integral_laplaceLaw hH hb hc0 hc ht.le).symm
  have hrrep : ∀t : ℝ,0<t → r t=laplaceMoment ν 1 t := by
    intro t ht
    have he := (spectralProfile_hasDerivAt ν hν c hrep t ht).unique (hderiv t ht)
    linarith
  have hrnonneg : ∀t,0<t → 0≤r t := fun _ ht => response_nonneg ν hν r hrrep ht
  obtain ⟨hi,hm⟩ := response_mass_from_fdt c r q hc hc0 hderiv hrnonneg hlim
  exact ⟨hi,hm,thermalProfile_contDiffOn ν hν r hrrep hi,
    fun n t ht => thermalProfile_completeMonotonicity ν hν r hrrep hi n ht,
    thermalProfile_tendsto_zero ν hν r hrrep hi⟩

/-- The literal conditional thermal tail of Corollary 11.7. Antitonicity,
continuity, and the mass are derived from the actual constructed law and FDT. -/
theorem hankel_thermal_tail (c r : ℝ → ℝ) (a A q : ℝ)
    (hH : HankelPositive c) (hb : ∀t, 0≤t → |c t|≤1)
    (hc0 : c 0=1) (hc : ContinuousOn c (Ici 0))
    (hderiv : ∀t, 0<t → HasDerivAt c (-r t) t)
    (hlim : Tendsto c atTop (𝓝 q)) (hrpos : ∀t,0<t → 0<r t)
    (ha : 0<a) (hA : 0<A) (hq : q<1)
    (hpow : r ~[atTop] (fun t : ℝ => (a*A)*t^(-1-a))) :
    Tendsto (fun t => thermalProfile r t/r t) atTop (𝓝 (2*(1-q))) ∧
    (thermalProfile r ~[atTop] (fun t => (2*(1-q))*r t)) ∧
    (thermalProfile r ~[atTop] (fun t : ℝ => (2*(1-q)*a*A)*t^(-1-a))) := by
  let ν := laplaceLaw c hH hb
  letI : IsProbabilityMeasure ν := laplaceLaw_probability hH hb hc0
  have hν : ∀ᵐ x : ℝ ∂ν,0≤x := laplaceLaw_ae_nonnegative hH hb hc0
  have hrep : ∀t : ℝ,0<t → c t=∫x : ℝ,Real.exp (-x*t) ∂ν :=
    fun t ht => (integral_laplaceLaw hH hb hc0 hc ht.le).symm
  have hrrep : ∀t : ℝ,0<t → r t=laplaceMoment ν 1 t := by
    intro t ht
    have he := (spectralProfile_hasDerivAt ν hν c hrep t ht).unique (hderiv t ht)
    linarith
  obtain ⟨hi,hm⟩ := response_mass_from_fdt c r q hc hc0 hderiv (fun _ ht => (hrpos _ ht).le) hlim
  have hranti : AntitoneOn r (Ioi 0) := by
    intro s hs t ht hst
    rw [hrrep s hs,hrrep t ht]
    exact laplaceMoment_antitoneOn ν hν 1 hs ht hst
  have hrcont : ContinuousOn r (Ioi 0) :=
    (momentProfile_contDiffOn ν hν r 1 hrrep).continuousOn
  exact ⟨thermalProfile_source_ratio r a A q ha hA hrpos hranti hrcont hi hm hpow,
    thermalProfile_source_equivalences r a A q ha hA hq hrpos hranti hrcont hi hm hpow⟩

end SphericalAging.ThermalStationary
