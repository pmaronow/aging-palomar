module

public import SphericalAging.SphereFisherHelly
public import SphericalAging.SphereWaitingCurrent

public section

/-! Genuine normalized Hamiltonian energy current of the positive spherical
forward density, with the actual landscape/Fisher square estimate. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereEnergyCurrent
open MeasureTheory Set FiniteModel SphereInitialLaw HardSphereDynamics
open SphereRotationGeometry SphereFisherHelly SphereMixedDerivatives
open SphereEntropyDissipation SphereEntropyBudget SphereForwardAdjoint SphereCanonicalEntropy
open SphereGeneratorIntegrationByParts SphereCoordinateScore SphereFisherCurrent
open SphereWaitingCurrent SphericalIntegrationByParts SphereInitialFisher SphereQuenchedFDT SphereCarreDuChamp
open scoped InnerProductSpace Topology

@[expose] def energy {N p : ℕ} {β : ℝ} (E : FisherDensity N p β) (J : Disorder N p) (t : ℝ) : ℝ :=
  (∫ x : Vector N,E.ρ J t x*Hamiltonian N p J x ∂sphereLaw N)/(N : ℝ)

@[expose] def current {N p : ℕ} {β : ℝ} (E : FisherDensity N p β) (J : Disorder N p) (t : ℝ) : ℝ :=
  -(∫ x : Vector N,E.ρ J t x*⟪tangentScore β J (E.ρ J t) x,
    projection x (gradient (Hamiltonian N p J) x)⟫_ℝ ∂sphereLaw N)/(N : ℝ)

theorem energy_hasDerivAt {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (J : Disorder N p) {t : ℝ} (ht : 0≤t) :
    HasDerivAt (energy E J) (current E J t) t := by
  have hρ₂ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hH : ContDiff ℝ 2 (Hamiltonian N p J) := (Hamiltonian_contDiff J).of_le (by simp)
  have hF : Continuous (Function.uncurry (fun u x => E.ρ J u x*Hamiltonian N p J x)) :=
    hρ₂.continuous.mul (hH.continuous.comp continuous_snd)
  have hF' : Continuous (Function.uncurry (fun u x => timeSlope (E.ρ J) u x*Hamiltonian N p J x)) :=
    (timeSlope_contDiff_one hρ₂).continuous.mul (hH.continuous.comp continuous_snd)
  have hd := (hasDerivAt_sphere_parameter_integral hN hF hF'
    (fun u x => (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num)) u x).mul_const _) t).div_const (N : ℝ)
  apply hd.congr_deriv
  have hsp : ContDiff ℝ 2 (E.ρ J t) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ₂.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (t,x)))
  have hpair := forward_density_current_pairing hN (1/(2*(N : ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hsp (E.positive J t) (hH.of_le (by norm_num))
  have he : (∫ x : Vector N,timeSlope (E.ρ J) t x*Hamiltonian N p J x ∂sphereLaw N)=
      (∫ x : Vector N,Hamiltonian N p J x*
        SphereEntropyDissipation.forwardDensitySlope (1/(2*(N : ℝ))) β J (canonicalRotations N) (E.ρ J t) x
          ∂sphereLaw N) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [E.forward J t ht x]
      change SphereEntropyDissipation.forwardDensitySlope (1/(2*(N : ℝ))) β J
        (canonicalRotations N) (E.ρ J t) x * _ = _ *
        SphereEntropyDissipation.forwardDensitySlope (1/(2*(N : ℝ))) β J
          (canonicalRotations N) (E.ρ J t) x
      ring
  rw [he,hpair]
  unfold current
  congr 2
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hxs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  rw [canonical_rotationGamma hN _ _ x hxs]
  rfl

theorem current_square_le_fisher {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (J : Disorder N p) {t : ℝ} (ht : 0≤t) :
    (current E J t)^2≤(p : ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*
      (fisherInformation β J (E.ρ J t)/(N : ℝ)) := by
  have hρ₂ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hsp : ContDiff ℝ 2 (E.ρ J t) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ₂.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (t,x)))
  have hmass := density_mass_one hN (1/(2*(N : ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ₂ (timeSlope_contDiff_one hρ₂).continuous
    (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num))) (E.initial J) ht
    (fun u hu => E.forward J u hu.1)
  have hg : Continuous (gradient (Hamiltonian N p J)) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (((Hamiltonian_contDiff J).of_le (by simp) : ContDiff ℝ 1 (Hamiltonian N p J)).continuous_fderiv (by norm_num))
  have hF : Continuous (fun x : Vector N => projection x (gradient (Hamiltonian N p J) x)) := by
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N : ℝ)).smul continuous_id)
  have hb := score_pairing_square_le hN β J hsp (E.positive J t) hmass hF
    (fun x hx => Hamiltonian_tangent_gradient_sq_bound hN J x hx)
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  unfold current
  rw [div_pow,neg_sq]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).mpr
  convert hb using 1
  field_simp

theorem energy_deriv_square_le_fisher {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (J : Disorder N p) {t : ℝ} (ht : 0≤t) :
    (deriv (energy E J) t)^2≤(p : ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*
      (fisherInformation β J (E.ρ J t)/(N : ℝ)) := by
  rw [(energy_hasDerivAt hN E J ht).deriv]
  exact current_square_le_fisher hN E J ht

end SphericalAging.SphereEnergyCurrent
