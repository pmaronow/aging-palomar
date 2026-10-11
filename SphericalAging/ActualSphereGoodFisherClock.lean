module

public import SphericalAging.ActualSphereFisherClock
public import SphericalAging.SphereOnlyGoodFisherClock

public section

/-! The literal actual disorder-truncated Fisher clock, with no analytic
or measurable-density assumptions added to the finite spherical model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.ActualSphereGoodFisherClock
open MeasureTheory Set FiniteModel SphereRotationGeometry SphereGoodEventFisherClock
open ActualSphereFisherClock ActualSphereGibbsDensity ActualForwardFisherMeasurability
open scoped NNReal Topology
variable {N p : ℕ}

theorem actual_goodFisher_clock_antitoneOn (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (A : ℝ) :
    AntitoneOn (fun t => Real.exp (-ceilingRate p β A*t)*goodFisher (N:=N) (p:=p) β A (forwardDensity β R hR) t) (Ici 0) := by
  have hm t : Measurable (fun J : Disorder N p => fisherInformation β J (forwardDensity β R hR J t)) :=
    actual_forwardDensity_fisher_section_measurable hN (by omega : 1≤p) β R hR hNR t
  exact SphereOnlyGoodFisherClock.goodFisher_clock_antitoneOn hN hp β.coe_nonneg A
    (fun J => actualForwardData hN (by omega) β R hR hNR J)
    (fun J => forwardDensity_initial_onSphere hN (by omega) β R hR hNR J)
    (fun t => (hm t).aestronglyMeasurable)

theorem actual_goodFisher_clock_uniform_bound (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (A : ℝ)
    {t : ℝ} (ht : 0≤t) :
    0≤Real.exp (-ceilingRate p β A*t)*goodFisher (N:=N) (p:=p) β A (forwardDensity β R hR) t ∧
      Real.exp (-ceilingRate p β A*t)*goodFisher (N:=N) (p:=p) β A (forwardDensity β R hR) t≤(β:ℝ)^2*(p:ℝ) := by
  have hm t : Measurable (fun J : Disorder N p => fisherInformation β J (forwardDensity β R hR J t)) :=
    actual_forwardDensity_fisher_section_measurable hN (by omega : 1≤p) β R hR hNR t
  exact SphereOnlyGoodFisherClock.goodFisher_clock_uniform_bound hN hp β.coe_nonneg A
    (fun J => actualForwardData hN (by omega) β R hR hNR J)
    (fun J => forwardDensity_initial_onSphere hN (by omega) β R hR hNR J)
    (fun t => (hm t).aestronglyMeasurable) ht

end SphericalAging.ActualSphereGoodFisherClock
