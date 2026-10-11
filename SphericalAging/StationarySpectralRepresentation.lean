module

public import SphericalAging.HankelLaplaceLaw
public import SphericalAging.NonnegativeSpectralLaplace
public import SphericalAging.StationaryReflectionFromTranslation

public section

/-! Spectral representation of an actual stationary cluster. The spectral law,
its plateau atom, smoothness and every complete-monotonicity sign are constructed
from the genuine reflected Gram limit. No spectral representation is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StationarySpectralRepresentation
open HankelReflection HankelLaplaceLaw
open NonnegativeSpectralLaplace

/-- The bounded normalized continuous Hankel kernel constructs a probability
Laplace law, its exact plateau atom, and complete monotonicity of both c and r. -/
theorem hankel_spectral_representation {c r : ℝ → ℝ} {q : ℝ}
    (hc : HankelPositive c) (hb : ∀t : ℝ,0≤t→|c t|≤1)
    (h0 : c 0=1) (hcont : ContinuousOn c (Ici 0))
    (hq : Tendsto c atTop (𝓝 q))
    (hderiv : ∀t : ℝ,0<t→HasDerivAt c (-r t) t) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Iio 0)=0 ∧
      ν {0}=ENNReal.ofReal q ∧
      (∀t : ℝ,0≤t→c t=∫ x : ℝ,Real.exp (-x*t) ∂ν) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) r (Ioi 0) ∧
      (∀n : ℕ,∀t : ℝ,0<t→0≤(-1:ℝ)^n*iteratedDeriv n c t) ∧
      (∀n : ℕ,∀t : ℝ,0<t→0≤(-1:ℝ)^n*iteratedDeriv n r t) := by
  let ν := laplaceLaw c hc hb
  letI : IsProbabilityMeasure ν := laplaceLaw_probability hc hb h0
  have hν : ∀ᵐ x : ℝ ∂ν,0≤x := laplaceLaw_ae_nonnegative hc hb h0
  have hrep : ∀t : ℝ,0≤t→c t=∫ x : ℝ,Real.exp (-x*t) ∂ν :=
    fun _ ht => (integral_laplaceLaw hc hb h0 hcont ht).symm
  have hrep' : ∀t : ℝ,0<t→c t=∫ x : ℝ,Real.exp (-x*t) ∂ν :=
    fun _ ht => hrep _ ht.le
  have hatom : ν {0}=ENNReal.ofReal q := by
    have he : ν.real {0}=q := laplaceLaw_zero_atom hc hb h0 hcont hq
    rw [←he,Measure.real]
    exact (ENNReal.ofReal_toReal (measure_ne_top ν {0})).symm
  have hrrep : ∀t : ℝ,0<t→ r t=SpectralLaplace.laplaceMoment ν 1 t := by
    intro t ht
    have he := (spectralProfile_hasDerivAt ν hν c hrep' t ht).unique (hderiv t ht)
    linarith
  exact ⟨ν,inferInstance,laplaceLaw_negative_mass hc hb h0,hatom,hrep,
    spectralProfile_contDiffOn ν hν c hrep',
    momentProfile_contDiffOn ν hν r 1 hrrep,
    spectralProfile_completeMonotonicity ν hν c hrep',
    momentProfile_completeMonotonicity ν hν r 1 hrrep⟩

open CKSpecification PrefixRectangleStability StationaryResponseLimit
open StationaryReflectionFromTranslation PrefixReflection

/-- Complete source stationary-cluster spectral theorem. The reflected Hankel
positivity and physical bound are derived from actual translated CK limits. -/
theorem stationary_cluster_spectral_representation {p : ℕ} {β ell q : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ} (h : CKEquations p β d)
    (hT : Tendsto T atTop atTop)
    (hC : ∀ A,0≤A→TendstoUniformlyOn
      (fun n (z : ℝ×ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : ∀ A,0≤A→TendstoUniformlyOn
      (fun n (z : ℝ×ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hLam : ∀ A,0≤A→TendstoUniformlyOn
      (fun n a => d.multiplier (T n+a)) (fun _ => ell) atTop (Icc 0 A))
    (hFDT : ∀t : ℝ,0≤t→HasDerivWithinAt c (-r t) (Ici 0) t)
    (hq : Tendsto c atTop (𝓝 q)) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Iio 0)=0 ∧
      ν {0}=ENNReal.ofReal q ∧
      (∀t : ℝ,0≤t→c t=∫ x : ℝ,Real.exp (-x*t) ∂ν) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) r (Ioi 0) ∧
      (∀n : ℕ,∀t : ℝ,0<t→0≤(-1:ℝ)^n*iteratedDeriv n c t) ∧
      (∀n : ℕ,∀t : ℝ,0<t→0≤(-1:ℝ)^n*iteratedDeriv n r t) := by
  have hS := stationary_response_of_uniform_translation h hT hC hR hLam
  have hQ := prefix_reflection_of_uniform_translation_and_fdt h hT hC hR hLam hFDT
  have hH : HankelPositive c := hankel_positive_of_prefix_limit h (fun a b => by
    let A : ℝ := max (a:ℝ) (b:ℝ)
    have hA : 0≤A := a.coe_nonneg.trans (le_max_left _ _)
    have ha : (a:ℝ)∈Icc 0 A := ⟨a.coe_nonneg,le_max_left _ _⟩
    have hb : (b:ℝ)∈Icc 0 A := ⟨b.coe_nonneg,le_max_right _ _⟩
    simpa only [Function.uncurry_def] using (hQ A hA).tendsto_at (x:=((a:ℝ),(b:ℝ))) ⟨ha,hb⟩)
  have hb : ∀t : ℝ,0≤t→|c t|≤1 := by
    intro t ht
    have hp := hS.physical t ht
    rw [abs_of_nonneg (hp.1.trans hp.2.1)]
    exact hp.2.2
  exact hankel_spectral_representation hH hb hS.initial_c hS.continuous_c hq
    (fun t ht => (hFDT t ht.le).hasDerivAt (Ici_mem_nhds ht))

end SphericalAging.StationarySpectralRepresentation
