module

public import SphericalAging.ActualSphereCurrentMoment
public import SphericalAging.ActualSphereFisherClock
public import SphericalAging.SphereAnnealedIntegratedFDT

public section

/-! Per-time annealed current moments from the constructed Fisher clock.
No disorder-current integrability or current majorant is supplied as input. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace SphericalAging.ActualSphereAnnealedCurrentMoment
open FiniteModel SphereInitialLaw SphereRotationGeometry ActualSphereGibbsDensity
open ActualSphereCurrent ActualSphereCurrentMoment ActualSphereFisherClock
open SphereAnnealedFisherBudget SphereAnnealedIntegratedFDT
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem actual_current_disorder_integrable_and_square (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {t s : ℝ} (hs : 0≤s) :
    Integrable (fun J : Disorder N p => current β R hR J t s) (disorderLaw N p) ∧
      Integrable (fun J : Disorder N p => (current β R hR J t s)^2) (disorderLaw N p) := by
  have hmcomp : StronglyMeasurable ((fun z : Disorder N p×ℝ => current β R hR z.1 t z.2)∘
      (fun J : Disorder N p => (J,s))) :=
    (actual_current_row_joint_stronglyMeasurable hN (by omega) β R hR hNR t).comp_measurable
      (measurable_id.prodMk measurable_const)
  have hm : StronglyMeasurable (fun J : Disorder N p => current β R hR J t s) := by
    simpa only [Function.comp_def] using hmcomp
  exact integrable_and_integrable_sq_of_square_bound (disorderLaw N p) hm.aestronglyMeasurable
    (actual_forwardDensity_fisher_disorder_integrable hN hp β R hR hNR hs)
    (fun J => actual_current_square_le_fisher hN (by omega) β R hR hNR J hs)

theorem actual_annealed_current_secondMoment_le_fisher (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {t s : ℝ} (hs : 0≤s) :
    (∫J : Disorder N p,(current β R hR J t s)^2 ∂disorderLaw N p)≤
      annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) s := by
  have hi := (actual_current_disorder_integrable_and_square hN hp β R hR hNR (t:=t) hs).2
  have hFI := actual_forwardDensity_fisher_disorder_integrable hN hp β R hR hNR hs
  have hh := integral_mono hi hFI (fun J =>
    actual_current_square_le_fisher hN (by omega) β R hR hNR J hs)
  simpa only [integral_div,annealedFisher] using hh

theorem actual_annealed_current_square_le_fisher (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {t s : ℝ} (hs : 0≤s) :
    (∫J : Disorder N p,current β R hR J t s ∂disorderLaw N p)^2≤
      annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) s := by
  have hi := actual_current_disorder_integrable_and_square hN hp β R hR hNR (t:=t) hs
  exact (probability_integral_square_le (disorderLaw N p) hi.1 hi.2).trans
    (actual_annealed_current_secondMoment_le_fisher hN hp β R hR hNR hs)

theorem actual_annealed_current_abs_le_sqrt_fisher (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {t s : ℝ} (hs : 0≤s) :
    |∫J : Disorder N p,current β R hR J t s ∂disorderLaw N p|≤
      Real.sqrt (annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) s) := by
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt
    (actual_annealed_current_square_le_fisher hN hp β R hR hNR hs)

end SphericalAging.ActualSphereAnnealedCurrentMoment
