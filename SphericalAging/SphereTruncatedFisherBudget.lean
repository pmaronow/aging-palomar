module

public import SphericalAging.SphereGoodEventFisherClock

public section

/-! Genuine Fubini and total Fisher budgets on every measurable disorder event.
In particular, the bad-event Fisher mass is bounded by the actual truncated
landscape first moment, as in Step 3 of the source Fisher-clock construction. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereTruncatedFisherBudget

open MeasureTheory Set FiniteModel SphereInitialLaw SphereGibbsEntropy
open SphereRotationGeometry SphereCanonicalEntropy SphereAnnealedFisherBudget
open SphereGoodEventFisherClock GaussianLandscape

@[expose] def restrictedFisher {N p : ℕ} (β : ℝ) (ρ : Disorder N p → ℝ → Vector N → ℝ)
    (E : Set (Disorder N p)) (t : ℝ) : ℝ :=
  ∫ J : Disorder N p,E.indicator (fun K => fisherInformation β K (ρ K t)/(N : ℝ)) J ∂disorderLaw N p

/-- Actual event-restricted all-time Fisher mass, with its proved Fubini identity
and true quenched landscape domination. Product integrability is derived from
the positive smooth forward density PDE and initial entropy, not assumed. -/
theorem restricted_fisher_time_budget {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {ρ ρdot : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 2 (Function.uncurry (ρ J)))
    (hdot : ∀ J,Continuous (Function.uncurry (ρdot J)))
    (hpos : ∀ J t x,0<ρ J t x)
    (hderiv : ∀ J t x,HasDerivAt (fun s => ρ J s x) (ρdot J t x) t)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,ρdot J t x=sphericalForwardDensitySlope β J (ρ J t) x)
    (hmeas : AEStronglyMeasurable
      (fun z : Disorder N p × ℝ => fisherInformation β z.1 (ρ z.1 z.2))
      ((disorderLaw N p).prod (volume.restrict (Ioi 0))))
    (E : Set (Disorder N p)) (hE : MeasurableSet E) :
    IntegrableOn (restrictedFisher β ρ E) (Ioi 0) ∧
      (∫ t in Ioi 0,restrictedFisher β ρ E t) =
        (∫ J : Disorder N p,E.indicator (fun K => (∫ t in Ioi 0,fisherInformation β K (ρ K t))/(N : ℝ)) J
          ∂disorderLaw N p) ∧
      (∫ t in Ioi 0,restrictedFisher β ρ E t) ≤ β^2/2 ∧
      (∫ t in Ioi 0,restrictedFisher β ρ E t) ≤
        2*β*(∫ J : Disorder N p,E.indicator (landscapeNorm N p) J ∂disorderLaw N p) := by
  let μ := disorderLaw N p
  let ν := volume.restrict (Ioi (0 : ℝ))
  let F (z : Disorder N p × ℝ) := fisherInformation β z.1 (ρ z.1 z.2)/(N : ℝ)
  let FE (z : Disorder N p × ℝ) := E.indicator (fun J => fisherInformation β J (ρ J z.2)/(N : ℝ)) z.1
  have hprod : Integrable F (μ.prod ν) :=
    (fisher_product_integrable hN hp hβ hρ hdot hpos hderiv hinit hPDE hmeas).div_const _
  have hset : MeasurableSet {z : Disorder N p × ℝ | z.1∈E} := hE.preimage measurable_fst
  have hFE : FE = ({z : Disorder N p × ℝ | z.1∈E}).indicator F := by
    funext z
    by_cases h : z.1∈E <;> simp [FE,F,h]
  have hiFE : Integrable FE (μ.prod ν) := by
    rw [hFE]
    exact hprod.indicator hset
  have hi : IntegrableOn (restrictedFisher β ρ E) (Ioi 0) := hiFE.integral_prod_right
  have heq : (∫ t in Ioi 0,restrictedFisher β ρ E t) =
      (∫ J : Disorder N p,E.indicator (fun K => (∫ t in Ioi 0,fisherInformation β K (ρ K t))/(N : ℝ)) J
        ∂disorderLaw N p) := by
    unfold restrictedFisher
    change (∫ t,∫ J,FE (J,t) ∂μ ∂ν)=_
    rw [← integral_integral_swap hiFE]
    apply integral_congr_ae
    exact ae_of_all _ fun J => by
      by_cases h : J∈E
      · simp only [FE, indicator_of_mem h]
        rw [integral_div]
      · simp only [FE, indicator_of_notMem h, integral_zero]
  let B (J : Disorder N p) := (∫ t in Ioi 0,fisherInformation β J (ρ J t))/(N : ℝ)
  have hiBbase : Integrable B μ := by
    simpa only [F, B, ν, integral_div] using hprod.integral_prod_left
  have hiB : Integrable (E.indicator B) μ := hiBbase.indicator hE
  have hiD : Integrable (fun J : Disorder N p => initialEntropy N p β J/(N : ℝ)) μ :=
    (initialEntropy_annealed_integrable hN hp hβ).div_const _
  have hiQ : Integrable (E.indicator (landscapeNorm N p)) μ := (landscapeNorm_integrable hN hp).indicator hE
  have hbudget J := spherical_fisher_budget hN hp hβ J (hρ J) (hdot J) (hpos J)
    (hderiv J) (hinit J) (hPDE J)
  have hDpoint J : E.indicator B J ≤ initialEntropy N p β J/(N : ℝ) := by
    by_cases h : J∈E
    · rw [indicator_of_mem h]
      exact div_le_div_of_nonneg_right (hbudget J).2 (Nat.cast_nonneg N)
    · rw [indicator_of_notMem h]
      exact (initialEntropy_normalized_quenched hN hp hβ J).1
  have hQpoint J : E.indicator B J ≤ 2*β*(E.indicator (landscapeNorm N p) J) := by
    by_cases h : J∈E
    · simp only [indicator_of_mem h]
      exact spherical_fisher_normalized_quenched hN hp hβ J (hρ J) (hdot J) (hpos J)
        (hderiv J) (hinit J) (hPDE J)
    · simp only [indicator_of_notMem h,mul_zero,le_refl]
  refine ⟨hi,heq,?_,?_⟩
  · rw [heq]
    exact (integral_mono hiB hiD hDpoint).trans (initialEntropy_normalized_annealed hN hp hβ)
  · rw [heq,← integral_const_mul]
    exact integral_mono hiB (hiQ.const_mul _) hQpoint

end SphericalAging.SphereTruncatedFisherBudget
