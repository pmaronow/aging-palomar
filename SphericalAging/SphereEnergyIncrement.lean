module

public import SphericalAging.SphereEnergyCurrent

public section

/-! Actual finite normalized energy increments from density/current FTC.
The endpoint energy bound is sufficient to discard the bad disorder event
when passing to a fixed-time dimension limit. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereEnergyIncrement
open Set Filter MeasureTheory FiniteModel SphereInitialLaw HardSphereDynamics
open SphereEnergyCurrent SphereFisherHelly SphereQuenchedFDT SphereIntegratedFDT
open SphereEntropyBudget SphereEntropyDissipation SphereMixedDerivatives
open SphericalIntegrationByParts SphereRotationGeometry SphereCanonicalEntropy
open SphereGibbsEntropy GaussianLandscape SphereCoordinateScore SphereFisherCurrent
open scoped Topology InnerProductSpace

theorem density_mass {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (J : Disorder N p) {t : ℝ} (ht : 0≤t) : (∫ x : Vector N,E.ρ J t x ∂sphereLaw N)=1 := by
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  exact density_mass_one hN (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ (timeSlope_contDiff_one hρ).continuous
    (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num))) (E.initial J) ht
    (fun v hv => E.forward J v hv.1)

theorem current_continuous {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (J : Disorder N p) : Continuous (current E J) := by
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hg : Continuous (gradient (Hamiltonian N p J)) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (((Hamiltonian_contDiff J).of_le (by simp) : ContDiff ℝ 1 (Hamiltonian N p J)).continuous_fderiv (by norm_num))
  have hF : Continuous (fun x : Vector N => projection x (gradient (Hamiltonian N p J) x)) := by
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N:ℝ)).smul continuous_id)
  unfold current
  apply Continuous.div_const
  apply Continuous.neg
  apply continuous_sphere_parameter_integral hN
  exact hρ.continuous.mul ((joint_tangentScore_continuous β J hρ (E.positive J)).inner
    (hF.comp continuous_snd))

theorem energy_increment_current {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (J : Disorder N p) {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    energy E J v-energy E J u=∫ t in u..v,current E J t := by
  have hc : Continuous (energy E J) := by
    unfold energy
    apply Continuous.div_const
    apply continuous_sphere_parameter_integral hN
    exact (E.smooth J).continuous.mul ((Hamiltonian_contDiff J).continuous.comp continuous_snd)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hc.continuousOn
    (fun t ht => energy_hasDerivAt hN E J (hu.trans ht.1.le))
    ((current_continuous hN E J).intervalIntegrable u v)).symm

theorem energy_increment_square_bound {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (J : Disorder N p) {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    (energy E J v-energy E J u)^2≤(p:ℝ)^2*(landscapeNorm N p J)^2*(v-u)*
      (∫ t in u..v,fisherInformation β J (E.ρ J t)/(N:ℝ)) := by
  rcases huv.eq_or_lt with he | hlt
  · subst v
    simp
  rw [energy_increment_current hN E J hu huv]
  have hc := current_continuous hN E J
  have hFI := (SphereFisherClock.spherical_fisher_continuous hN β J
    ((E.smooth J).of_le (by norm_num)) (E.positive J)).div_const (N:ℝ)
  have hm := intervalIntegral.integral_mono_on (μ := volume) huv
    ((hc.pow 2).intervalIntegrable u v)
    ((hFI.const_mul ((p:ℝ)^2*(landscapeNorm N p J)^2)).intervalIntegrable u v)
      (fun t ht => current_square_le_fisher hN E J (hu.trans ht.1))
  rw [intervalIntegral.integral_const_mul] at hm
  have hh := (ResponseTransport.interval_square_bound hlt (hc.intervalIntegrable u v)
    ((hc.pow 2).intervalIntegrable u v)).trans
      (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr huv))
  convert hh using 1 <;> ring

theorem energy_abs_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (E : FisherDensity N p β) (J : Disorder N p) {t : ℝ} (ht : 0≤t) :
    |energy E J t|≤landscapeNorm N p J := by
  have hρ : Continuous (E.ρ J t) := (E.smooth J).continuous.comp (continuous_const.prodMk continuous_id)
  have hH := (Hamiltonian_contDiff J).continuous
  have hi₁ := continuous_sphere_integrable hN ((hρ.mul hH).norm)
  have hi₂ : Integrable (fun x : Vector N => E.ρ J t x*((N:ℝ)*landscapeNorm N p J))
      (sphereLaw N) := continuous_sphere_integrable hN (hρ.mul continuous_const)
  have hm := integral_mono_ae hi₁ hi₂ (by
    filter_upwards [sphere_Hamiltonian_bound hN hp J] with x hx
    change ‖E.ρ J t x * Hamiltonian N p J x‖ ≤ E.ρ J t x * ((N:ℝ)*landscapeNorm N p J)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (E.positive J t x)]
    exact mul_le_mul_of_nonneg_left hx (E.positive J t x).le)
  rw [integral_mul_const,density_mass hN E J ht,one_mul] at hm
  have hh := (norm_integral_le_integral_norm
    (f := fun x : Vector N => E.ρ J t x*Hamiltonian N p J x)).trans hm
  unfold energy
  rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_pos (Nat.cast_pos.mpr hN)]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr (by
    simpa only [Real.norm_eq_abs,mul_comm] using hh)

end SphericalAging.SphereEnergyIncrement
