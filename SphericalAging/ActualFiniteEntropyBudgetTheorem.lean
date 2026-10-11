module

public import SphericalAging.ActualSphereForwardZeroEndpoint
public import SphericalAging.ActualSphereAnnealedFisherBudget
public import SphericalAging.SphereOnlyFisherBudget

public section

/-! Every printed finite source5.1 clause for the literal actual diffusion.
At the time-zero boundary derivatives are right derivatives. All forward
flux identities are required only on the physical sphere. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SphericalAging.ActualFiniteEntropyBudgetTheorem
open FiniteModel HardSphereDynamics SphereInitialLaw SphericalIntegrationByParts
open SphereRotationGeometry SphereCanonicalEntropy SphereEntropyDissipation SphereGibbsEntropy
open SphereOnlySpatialLocalization SmoothPositiveSpatialReplacement SphereLogDensityEquation
open ActualSphereGibbsDensity ActualSphereForwardDensityRegularity ActualSphereForwardZeroEndpoint
open ActualSphereAnnealedFisherBudget SphereAnnealedFisherBudget SphereOnlyFisherBudget
variable {N p : ℕ}

theorem forwardDensitySlope_eq_score_divergence_onSphere (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    (J : Disorder N p) (t : ℝ) {x : Vector N} (hx : OnSphere x) :
    sphericalForwardDensitySlope β J (forwardDensity β R hR J t) x =
      (1 / (2 * (N : ℝ))) * ∑ ij : Fin N × Fin N,
        lieDerivative (coordinateRotation ij.1 ij.2)
          (fun y => forwardDensity β R hR J t y *
            lieDerivative (coordinateRotation ij.1 ij.2)
              (relativeLog β J (forwardDensity β R hR J t)) y) x := by
  let ρ := forwardDensity β R hR J t
  obtain ⟨g, hg, hgpos, hnear⟩ := exists_positive_near_sphere
    (forwardDensity_spatial_contDiff hN hp β R hR J t)
    (forwardDensity_positive_onSphere hN hp β R hR hNR J t)
  have hlocal : g =ᶠ[𝓝 x] ρ := hnear x hx
  unfold sphericalForwardDensitySlope SphereEntropyDissipation.forwardDensitySlope
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  let A := coordinateRotation ij.1 ij.2
  have hscore : (fun y => g y * lieDerivative A (relativeLog β J g) y) =ᶠ[𝓝 x]
      (fun y => ρ y * lieDerivative A (relativeLog β J ρ) y) :=
    hlocal.mul (lieDerivative_eventuallyEq A (relativeLog_eventuallyEq β J hlocal))
  calc
    lieDerivative A (SphereEntropyDissipation.rotationFlux β J A ρ) x =
        lieDerivative A (SphereEntropyDissipation.rotationFlux β J A g) x :=
      (lieDerivative_eventuallyEq A (rotationFlux_eventuallyEq β J A hlocal)).eq_of_nhds.symm
    _ = lieDerivative A (fun y => g y * lieDerivative A (relativeLog β J g) y) x := by
      rw [rotationFlux_eq_density_score β J A (hg.of_le (by norm_num)) hgpos]
    _ = lieDerivative A (fun y => ρ y * lieDerivative A (relativeLog β J ρ) y) x :=
      (lieDerivative_eventuallyEq A hscore).eq_of_nhds

theorem actual_source5_1 (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2) :
    (∀ J : Disorder N p, ∀ t : ℝ, 0 ≤ t → ∀ x : Vector N, OnSphere x →
      HasDerivWithinAt (fun s => forwardDensity β R hR J s x)
        ((1 / (2 * (N : ℝ))) * ∑ ij : Fin N × Fin N,
          lieDerivative (coordinateRotation ij.1 ij.2)
            (fun y => forwardDensity β R hR J t y *
              lieDerivative (coordinateRotation ij.1 ij.2)
                (relativeLog β J (forwardDensity β R hR J t)) y) x) (Ici 0) t) ∧
    (∀ J : Disorder N p, ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (fun s => relativeEntropy β J (forwardDensity β R hR J s))
        (-fisherInformation β J (forwardDensity β R hR J t)) (Ici 0) t) ∧
    (∀ J : Disorder N p,
      IntegrableOn (fun t => fisherInformation β J (forwardDensity β R hR J t)) (Ioi 0) ∧
      (∫ t in Ioi 0, fisherInformation β J (forwardDensity β R hR J t)) ≤ initialEntropy N p β J) ∧
    (IntegrableOn (annealedFisher (N := N) (p := p) β (forwardDensity β R hR)) (Ioi 0) ∧
      (∫ t in Ioi 0, annealedFisher (N := N) (p := p) β (forwardDensity β R hR) t) ≤ (β : ℝ) ^ 2 / 2) ∧
    (∀ J : Disorder N p, initialEntropy N p β J / (N : ℝ) ≤
      2 * (β : ℝ) * GaussianLandscape.landscapeNorm N p J) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro J t ht x hx
    rw [← forwardDensitySlope_eq_score_divergence_onSphere hN hp β R hR hNR J t hx]
    exact actual_forwardDensity_hasDerivWithinAt_forwardPDE hN hp β R hR hNR J ht hx
  · intro J t ht
    exact actual_forwardDensity_entropy_hasDerivWithinAt hN hp β R hR hNR J ht
  · exact fun J => actual_forwardDensity_fisher_budget hN hp β R hR hNR J
  · have hb := actual_annealed_fisher_time_budget hN hp β R hR hNR
    exact ⟨hb.1, hb.2.2⟩
  · exact fun J => (initialEntropy_normalized_quenched hN hp β.coe_nonneg J).2

end SphericalAging.ActualFiniteEntropyBudgetTheorem
