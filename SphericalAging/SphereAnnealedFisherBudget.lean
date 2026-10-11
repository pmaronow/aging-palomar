module

public import SphericalAging.SphereIntegratedFDT
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! The actual annealed Fisher time budget, with genuine product integrability
and Fubini. Measurability concerns the constructed Fisher integrand only; no
Fisher budget, total-mass measurability, or Fubini equality is assumed. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.SphereAnnealedFisherBudget

open MeasureTheory Set FiniteModel SphereInitialLaw SphereGibbsEntropy
open SphereRotationGeometry SphereCanonicalEntropy

@[expose] def annealedFisher {N p : ℕ} (β : ℝ) (ρ : Disorder N p → ℝ → Vector N → ℝ) (t : ℝ) : ℝ :=
  (∫ J : Disorder N p,fisherInformation β J (ρ J t) ∂disorderLaw N p)/(N : ℝ)

theorem fisher_product_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {ρ ρdot : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 2 (Function.uncurry (ρ J)))
    (hdot : ∀ J,Continuous (Function.uncurry (ρdot J)))
    (hpos : ∀ J t x,0<ρ J t x)
    (hderiv : ∀ J t x,HasDerivAt (fun s => ρ J s x) (ρdot J t x) t)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,ρdot J t x=sphericalForwardDensitySlope β J (ρ J t) x)
    (hmeas : AEStronglyMeasurable
      (fun z : Disorder N p × ℝ => fisherInformation β z.1 (ρ z.1 z.2))
      ((disorderLaw N p).prod (volume.restrict (Ioi 0)))) :
    Integrable (fun z : Disorder N p × ℝ => fisherInformation β z.1 (ρ z.1 z.2))
      ((disorderLaw N p).prod (volume.restrict (Ioi 0))) := by
  have hbudget J := spherical_fisher_budget hN hp hβ J (hρ J) (hdot J) (hpos J)
    (hderiv J) (hinit J) (hPDE J)
  have hnon J t : 0≤fisherInformation β J (ρ J t) := by
    unfold fisherInformation
    exact integral_nonneg fun x => mul_nonneg (hpos J t x).le (sq_nonneg _)
  have hnorm J : (∫ t in Ioi 0,‖fisherInformation β J (ρ J t)‖)=
      (∫ t in Ioi 0,fisherInformation β J (ρ J t)) := by
    apply integral_congr_ae
    exact ae_of_all _ fun t => Real.norm_of_nonneg (hnon J t)
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨ae_of_all _ fun J => (hbudget J).1,?_⟩
  apply (initialEntropy_annealed_integrable hN hp hβ).mono'
    hmeas.norm.integral_prod_right'
  exact ae_of_all _ fun J => by
    rw [hnorm J,Real.norm_of_nonneg (integral_nonneg (hnon J))]
    exact (hbudget J).2

/-- Actual normalized annealed time Fisher mass is integrable and at most β²/2.
The equality with the true disorder average of total Fisher is proved by Fubini. -/
theorem annealed_fisher_time_budget {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {ρ ρdot : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 2 (Function.uncurry (ρ J)))
    (hdot : ∀ J,Continuous (Function.uncurry (ρdot J)))
    (hpos : ∀ J t x,0<ρ J t x)
    (hderiv : ∀ J t x,HasDerivAt (fun s => ρ J s x) (ρdot J t x) t)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,ρdot J t x=sphericalForwardDensitySlope β J (ρ J t) x)
    (hmeas : AEStronglyMeasurable
      (fun z : Disorder N p × ℝ => fisherInformation β z.1 (ρ z.1 z.2))
      ((disorderLaw N p).prod (volume.restrict (Ioi 0)))) :
    IntegrableOn (annealedFisher β ρ) (Ioi 0) ∧
      (∫ t in Ioi 0,annealedFisher β ρ t)=
        (∫ J : Disorder N p,(∫ t in Ioi 0,fisherInformation β J (ρ J t))/(N : ℝ) ∂disorderLaw N p) ∧
      (∫ t in Ioi 0,annealedFisher β ρ t) ≤ β^2/2 := by
  have hprod := fisher_product_integrable hN hp hβ hρ hdot hpos hderiv hinit hPDE hmeas
  have hi : IntegrableOn (annealedFisher β ρ) (Ioi 0) := hprod.integral_prod_right.div_const _
  have heq : (∫ t in Ioi 0,annealedFisher β ρ t)=
      (∫ J : Disorder N p,(∫ t in Ioi 0,fisherInformation β J (ρ J t))/(N : ℝ) ∂disorderLaw N p) := by
    unfold annealedFisher
    rw [integral_div,← integral_integral_swap hprod,integral_div]
  refine ⟨hi,heq,?_⟩
  rw [heq]
  exact spherical_fisher_normalized_annealed hN hp hβ hρ hdot hpos hderiv hinit hPDE
    hmeas.integral_prod_right'

end SphericalAging.SphereAnnealedFisherBudget
