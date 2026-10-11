module

public import SphericalAging.SphereOnlyEnergyCurrent
public import SphericalAging.ActualSphereFisherClock
public import SphericalAging.ActualForwardEnergyMeasurability

public section

/-! Energy derivative, current Fisher bound and finite energy increments
for the literal actual spherical diffusion. No density or forward PDE
realization, current calculus or moment estimate is supplied as a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualSphereEnergyCurrent
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereRotationGeometry ActualSphereGibbsDensity ActualSphereFisherClock
open ActualForwardEnergyMeasurability
open scoped Topology InnerProductSpace NNReal
variable {N p : ℕ}

@[expose] def forwardEnergyCurrent (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ) : ℝ :=
  -(∫x : State N,forwardDensity β R hR J t x*⟪tangentScore β J (forwardDensity β R hR J t) x,
    projection x (gradient (Hamiltonian N p J) x)⟫_ℝ ∂sphereLaw N)/(N:ℝ)

theorem actual_energy_hasDerivAt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {t : ℝ} (ht : 0<t) :
    HasDerivAt (forwardEnergy β R hR J) (forwardEnergyCurrent β R hR J t) t :=
  SphereOnlyEnergyCurrent.energy_hasDerivAt hN (actualForwardData hN hp β R hR hNR J) ht

theorem actual_energy_current_square_le_fisher (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {t : ℝ} (ht : 0≤t) :
    (forwardEnergyCurrent β R hR J t)^2≤(p:ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*
      (fisherInformation β J (forwardDensity β R hR J t)/(N:ℝ)) :=
  SphereOnlyEnergyCurrent.current_square_le_fisher hN (actualForwardData hN hp β R hR hNR J) t
    (forwardDensity_mass_one hN hp β R hR hNR J ⟨t,ht⟩)

theorem actual_energy_current_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) :
    Continuous (forwardEnergyCurrent β R hR J) :=
  SphereOnlyEnergyCurrent.current_continuous hN (actualForwardData hN hp β R hR hNR J)

theorem actual_energy_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) :
    Continuous (forwardEnergy β R hR J) :=
  SphereOnlyEnergyCurrent.energy_continuous hN (actualForwardData hN hp β R hR hNR J)

theorem actual_energy_increment_current (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    forwardEnergy β R hR J v-forwardEnergy β R hR J u=∫t in u..v,forwardEnergyCurrent β R hR J t :=
  SphereOnlyEnergyCurrent.energy_increment_current hN (actualForwardData hN hp β R hR hNR J) hu huv

theorem actual_energy_increment_square_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    (forwardEnergy β R hR J v-forwardEnergy β R hR J u)^2≤
      (p:ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*(v-u)*
        (∫t in u..v,fisherInformation β J (forwardDensity β R hR J t)/(N:ℝ)) :=
  SphereOnlyEnergyCurrent.energy_increment_square_bound hN (actualForwardData hN hp β R hR hNR J) hu huv
    (fun t ht => forwardDensity_mass_one hN hp β R hR hNR J ⟨t,hu.trans ht.1⟩)

theorem actual_energy_abs_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {t : ℝ} (ht : 0≤t) :
    |forwardEnergy β R hR J t|≤GaussianLandscape.landscapeNorm N p J :=
  SphereOnlyEnergyCurrent.energy_abs_bound hN hp (actualForwardData hN hp β R hR hNR J) t
    (forwardDensity_mass_one hN hp β R hR hNR J ⟨t,ht⟩)

end SphericalAging.ActualSphereEnergyCurrent
