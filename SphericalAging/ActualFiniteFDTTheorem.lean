module

public import SphericalAging.ActualSphereFDTZeroEndpoint
public import SphericalAging.ActualSphereAnnealedPointwiseFDT
public import SphericalAging.ActualSphereIntegratedFDT

public section

/-! The complete finite nonequilibrium FDT for the constructed sphere law.
The initial-time derivative is taken within the physical half-line. The
literal annealed integrated defect follows from the continuous annealed row
and its interior derivative, including both endpoints of the time window. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology NNReal InnerProductSpace
namespace SphericalAging.ActualFiniteFDTTheorem
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry
open SphereQuenchedFDT SphereFisherCurrent SphereIntegratedFDT SphereAnnealedFisherBudget
open ActualSphereGibbsDensity ActualSphereMeanSpatialInterface ActualSphereCurrent
open ActualSphereOnlyFDT ActualSphereFDTZeroEndpoint ActualSphereIntegratedFDT
open ActualSphereAnnealedCurrentMoment ActualSphereAnnealedPointwiseFDT
variable {N p : ℕ}

theorem actual_annealed_correlation_hasDerivWithinAt (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (annealedCorrelation (N := N) (p := p) β R hR t)
      (annealedResponse (N := N) (p := p) β R hR t s -
        annealedCurrent (N := N) (p := p) β R hR t s) (Ici 0) s := by
  rcases hs.eq_or_lt with hzero | hpos
  · subst s
    have hc := annealed_rows_continuousOn hN hp β R hR hNR t
    exact right_derivative_on_interval_of_continuousOn hst hc.1 (hc.2.1.sub hc.2.2)
      (fun u hu => actual_annealed_correlation_hasDerivAt hN hp β R hR hNR hu.1 hu.2)
  · exact (actual_annealed_correlation_hasDerivAt hN hp β R hR hNR hpos hst).hasDerivWithinAt

theorem actual_annealed_pointwise_fdt_within_square_bound (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (annealedResponse (N := N) (p := p) β R hR t s -
      derivWithin (annealedCorrelation (N := N) (p := p) β R hR t) (Ici 0) s) ^ 2 ≤
      annealedFisher (N := N) (p := p) β (forwardDensity β R hR) s := by
  rw [(actual_annealed_correlation_hasDerivWithinAt hN hp β R hR hNR hs hst).derivWithin
    (uniqueDiffOn_Ici (0 : ℝ) s hs), sub_sub_cancel]
  exact actual_annealed_current_square_le_fisher hN hp β R hR hNR hs

theorem actual_annealedCorrelation_diagonal (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    annealedCorrelation (N := N) (p := p) β R hR t t = 1 := by
  unfold annealedCorrelation
  simp_rw [actual_quenchedCorrelation_diagonal hN hp β R hR hNR _ ht]
  simp

theorem actual_literal_annealed_integratedDefect_current (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    1 - annealedCorrelation (N := N) (p := p) β R hR t s -
      (∫ u in s..t, annealedResponse (N := N) (p := p) β R hR t u) =
      -(∫ u in s..t, annealedCurrent (N := N) (p := p) β R hR t u) := by
  have hc := annealed_rows_continuousOn hN hp β R hR hNR t
  have hsub : Icc s t ⊆ Icc 0 t := fun u hu => ⟨hs.trans hu.1, hu.2⟩
  have hRint := (hc.2.1.mono hsub).intervalIntegrable_of_Icc (μ := volume) hst
  have hcurint := (hc.2.2.mono hsub).intervalIntegrable_of_Icc (μ := volume) hst
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (hc.1.mono hsub)
    (fun u hu => actual_annealed_correlation_hasDerivAt hN hp β R hR hNR
      (hs.trans_lt hu.1) hu.2) (hRint.sub hcurint)
  rw [intervalIntegral.integral_sub hRint hcurint,
    actual_annealedCorrelation_diagonal hN (by omega) β R hR hNR (hs.trans hst)] at hFTC
  linarith

theorem actual_literal_annealed_integrated_fdt_square_bound (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 - annealedCorrelation (N := N) (p := p) β R hR t s -
      (∫ u in s..t, annealedResponse (N := N) (p := p) β R hR t u)) ^ 2 ≤
      (t - s) * (∫ u in s..t, annealedFisher (N := N) (p := p) β
        (forwardDensity β R hR) u) := by
  rw [actual_literal_annealed_integratedDefect_current hN hp β R hR hNR hs hst]
  have hb := actual_annealed_integratedDefect_fisher_bound (p := p) hN (by omega) β R hR hNR hs hst
  rw [(actual_annealed_integratedDefect_current (p := p) hN (by omega) β R hR hNR hs hst).2] at hb
  exact hb

theorem actual_source5_2 (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2) :
    (∀ t s : ℝ, 0 ≤ s → s < t → ∀ J : Disorder N p,
      HasDerivWithinAt
        (fun u => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t u)
        (quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s -
          current β R hR J t s) (Ici 0) s ∧
      quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s -
        derivWithin (fun u => quenchedCorrelation (forwardDensity β R hR J)
          (realMean β R hR J) t u) (Ici 0) s =
        (∫ x : Vector N, forwardDensity β R hR J s x *
          inner ℝ (realMean β R hR J (t - s) x)
            (tangentScore β J (forwardDensity β R hR J s) x) ∂sphereLaw N) / (N : ℝ)) ∧
    (∀ t s : ℝ, 0 ≤ s → s < t →
      HasDerivWithinAt (annealedCorrelation (N := N) (p := p) β R hR t)
        (annealedResponse (N := N) (p := p) β R hR t s -
          annealedCurrent (N := N) (p := p) β R hR t s) (Ici 0) s ∧
      (annealedResponse (N := N) (p := p) β R hR t s -
        derivWithin (annealedCorrelation (N := N) (p := p) β R hR t) (Ici 0) s) ^ 2 ≤
        annealedFisher (N := N) (p := p) β (forwardDensity β R hR) s) ∧
    (∀ t s : ℝ, 0 ≤ s → s ≤ t →
      (1 - annealedCorrelation (N := N) (p := p) β R hR t s -
        (∫ u in s..t, annealedResponse (N := N) (p := p) β R hR t u)) ^ 2 ≤
        (t - s) * (∫ u in s..t, annealedFisher (N := N) (p := p) β
          (forwardDensity β R hR) u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t s hs hst J
    exact ⟨actual_quenched_fdt_hasDerivWithinAt hN (by omega) β R hR hNR J hs hst,
      actual_quenched_fdt_current hN (by omega) β R hR hNR J hs hst⟩
  · intro t s hs hst
    exact ⟨actual_annealed_correlation_hasDerivWithinAt hN hp β R hR hNR hs hst,
      actual_annealed_pointwise_fdt_within_square_bound hN hp β R hR hNR hs hst⟩
  · intro t s hs hst
    exact actual_literal_annealed_integrated_fdt_square_bound hN hp β R hR hNR hs hst

end SphericalAging.ActualFiniteFDTTheorem
