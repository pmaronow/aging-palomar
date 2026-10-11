module

public import SphericalAging.SphereOnlyForwardCalculus
public import SphericalAging.SphereOnlyLocalParameterIntegral
public import SphericalAging.SphereOnlyGeneratorLocalization
public import SphericalAging.SphereEnergyCurrent
public import SphericalAging.SphereOnlyFisherCurrentContinuity
public import SphericalAging.SphereEnergyIncrement

public section

/-! Actual Hamiltonian energy calculus with positivity and evolution only
on the physical sphere. Positive spatial representatives transfer IBP
and Fisher Cauchy estimates, and are not given an evolution equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereOnlyEnergyCurrent
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereRotationGeometry
open SphereEntropyDissipation SphereForwardAdjoint SphereCarreDuChamp SphereWaitingCurrent
open SphereGeneratorIntegrationByParts SphereFisherDissipation SphereFisherClock SphereCanonicalEntropy
open SphereOnlyForwardCalculus SphereOnlyLocalParameterIntegral SmoothPositiveSpatialReplacement
open SphereOnlySpatialLocalization SphereOnlyGeneratorLocalization SphereInitialFisher
open scoped Topology InnerProductSpace
variable {N p : ℕ}

theorem forward_density_current_pairing_onSphere {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {ρ f : Vector N→ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x) (hf : ContDiff ℝ 1 f) :
    (∫x,f x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N)=
      -(∫x,ρ x*rotationGamma κ A (relativeLog β J ρ) f x ∂sphereLaw N) := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := forward_density_current_pairing hN κ β J A hA hg hgpos hf
  have hleft : (∫x,f x*forwardDensitySlope κ β J A g x ∂sphereLaw N)=
      ∫x,f x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(forwardDensitySlope_eventuallyEq κ β J A (hnear x hx)).eq_of_nhds]
  have hright : (∫x,g x*rotationGamma κ A (relativeLog β J g) f x ∂sphereLaw N)=
      ∫x,ρ x*rotationGamma κ A (relativeLog β J ρ) f x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,
      (rotationGamma_eventuallyEq κ A (relativeLog_eventuallyEq β J (hnear x hx))
        (Filter.EventuallyEq.rfl)).eq_of_nhds]
  rwa [hleft,hright] at hh

theorem score_pairing_square_le_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x)
    (hmass : (∫x,ρ x ∂sphereLaw N)=1) {F : Vector N→Vector N}
    (hF : Continuous F) {M : ℝ} (hbound : ∀x,OnSphere x→‖F x‖^2≤M) :
    (∫x,ρ x*⟪tangentScore β J ρ x,F x⟫_ℝ ∂sphereLaw N)^2≤M*fisherInformation β J ρ := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hgmass : (∫x,g x ∂sphereLaw N)=1 := by
    rw [←hmass]
    apply integral_congr_ae
    exact (physicalSphere_ae hN).mono fun x hx => (hnear x hx).eq_of_nhds
  have hh := score_pairing_square_le hN β J hg hgpos hgmass hF hbound
  have heq : (∫x,g x*⟪tangentScore β J g x,F x⟫_ℝ ∂sphereLaw N)=
      ∫x,ρ x*⟪tangentScore β J ρ x,F x⟫_ℝ ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,(tangentScore_eventuallyEq β J (hnear x hx)).eq_of_nhds]
  rwa [heq,fisherInformation_eq_of_near hN β J hnear] at hh

@[expose] def energy {β : ℝ} {J : Disorder N p} (D : SphereForwardData N p β J) (t : ℝ) : ℝ :=
  (∫x,D.ρ t x*Hamiltonian N p J x ∂sphereLaw N)/(N:ℝ)

@[expose] def current {β : ℝ} {J : Disorder N p} (D : SphereForwardData N p β J) (t : ℝ) : ℝ :=
  -(∫x,D.ρ t x*⟪tangentScore β J (D.ρ t) x,
    projection x (gradient (Hamiltonian N p J) x)⟫_ℝ ∂sphereLaw N)/(N:ℝ)

theorem energy_hasDerivAt (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {t : ℝ} (ht : 0<t) :
    HasDerivAt (energy D) (current D t) t := by
  have hH : ContDiff ℝ 1 (Hamiltonian N p J) := (Hamiltonian_contDiff J).of_le (by simp)
  have hF : Continuous (Function.uncurry (fun u x => D.ρ u x*Hamiltonian N p J x)) :=
    D.joint.mul (hH.continuous.comp continuous_snd)
  have hF' : Continuous (Function.uncurry (fun u x => D.ρdot u x*Hamiltonian N p J x)) :=
    D.jointDot.mul (hH.continuous.comp continuous_snd)
  have hd := (hasDerivAt_integral_of_sphere_derivative hN hF hF'
    (a:=t/2) (b:=t+1) (t₀:=t) (by linarith) (by linarith)
    (fun u hu x hx => (D.timeDerivative u (by linarith [hu.1]) x hx).mul_const
      (Hamiltonian N p J x))).div_const (N:ℝ)
  apply hd.congr_deriv
  have hpair := forward_density_current_pairing_onSphere hN (1/(2*(N:ℝ))) β J
    (SphereCasimirGamma2.rotations N) (fun ij => coordinateRotation_skew ij.1 ij.2)
    ((D.spatial t).of_le (by norm_num)) (D.positive t) hH
  have he : (∫x,D.ρdot t x*Hamiltonian N p J x ∂sphereLaw N)=
      ∫x,Hamiltonian N p J x*forwardDensitySlope (1/(2*(N:ℝ))) β J
        (SphereCasimirGamma2.rotations N) (D.ρ t) x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [D.spherePDE t ht x hx]
    exact mul_comm _ _
  rw [he,hpair]
  unfold current
  congr 2
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [canonical_rotationGamma hN _ _ x hx]
  rfl

theorem current_square_le_fisher (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) (t : ℝ) (hmass : (∫x,D.ρ t x ∂sphereLaw N)=1) :
    (current D t)^2≤(p:ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*
      (fisherInformation β J (D.ρ t)/(N:ℝ)) := by
  have hg : Continuous (gradient (Hamiltonian N p J)) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (((Hamiltonian_contDiff J).of_le (by simp) : ContDiff ℝ 1 (Hamiltonian N p J)).continuous_fderiv (by norm_num))
  have hF : Continuous (fun x : Vector N => projection x (gradient (Hamiltonian N p J) x)) := by
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N:ℝ)).smul continuous_id)
  have hb := score_pairing_square_le_onSphere hN β J ((D.spatial t).of_le (by norm_num))
    (D.positive t) hmass hF (fun x hx => Hamiltonian_tangent_gradient_sq_bound hN J x hx)
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  unfold current
  rw [div_pow,neg_sq]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).mpr
  convert hb using 1
  field_simp


theorem current_continuous (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) : Continuous (current D) := by
  have hg : Continuous (gradient (Hamiltonian N p J)) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (((Hamiltonian_contDiff J).of_le (by simp) : ContDiff ℝ 1 (Hamiltonian N p J)).continuous_fderiv (by norm_num))
  have hF : Continuous (fun x : Vector N => projection x (gradient (Hamiltonian N p J) x)) := by
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N:ℝ)).smul continuous_id)
  have hscore := SphereOnlyFisherCurrentContinuity.joint_tangentScore_continuousOn_all β J D.joint
    D.jointFirst (fun t => (D.spatial t).of_le (by norm_num)) D.positive
  unfold current
  apply Continuous.div_const
  apply Continuous.neg
  apply SphereOnlyAllTimeContinuity.supported_integral_continuous hN
  · apply (D.joint.continuousOn.mul (hscore.inner (hF.comp continuous_snd).continuousOn)).congr
    intro z _
    rfl
  · intro t
    exact (D.spatial t).continuous.aestronglyMeasurable.mul
      ((SphereOnlyFisherContinuity.tangentScore_aestronglyMeasurable hN β J
        ((D.spatial t).of_le (by norm_num)) (D.positive t)).inner hF.aestronglyMeasurable)

theorem energy_continuous (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) : Continuous (energy D) := by
  unfold energy
  apply Continuous.div_const
  apply SphereEntropyBudget.continuous_sphere_parameter_integral hN
  exact D.joint.mul ((Hamiltonian_contDiff J).continuous.comp continuous_snd)

theorem energy_increment_current (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    energy D v-energy D u=∫t in u..v,current D t :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv (energy_continuous hN D).continuousOn
    (fun t ht => energy_hasDerivAt hN D (hu.trans_lt ht.1))
    ((current_continuous hN D).intervalIntegrable u v)).symm

theorem energy_increment_square_bound (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {u v : ℝ} (hu : 0≤u) (huv : u≤v)
    (hmass : ∀t,t∈Icc u v→(∫x,D.ρ t x ∂sphereLaw N)=1) :
    (energy D v-energy D u)^2≤(p:ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2*(v-u)*
      (∫t in u..v,fisherInformation β J (D.ρ t)/(N:ℝ)) := by
  rcases huv.eq_or_lt with he | hlt
  · subst v
    simp
  rw [energy_increment_current hN D hu huv]
  have hc := current_continuous hN D
  have hFI := (D.fisher_continuous hN).div_const (N:ℝ)
  have hm := intervalIntegral.integral_mono_on (μ:=volume) huv
    ((hc.pow 2).intervalIntegrable u v)
    ((hFI.const_mul ((p:ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2)).intervalIntegrable u v)
    (fun t ht => current_square_le_fisher hN D t (hmass t ht))
  rw [intervalIntegral.integral_const_mul] at hm
  have hh := (ResponseTransport.interval_square_bound hlt (hc.intervalIntegrable u v)
    ((hc.pow 2).intervalIntegrable u v)).trans
      (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr huv))
  convert hh using 1 <;> ring

theorem energy_abs_bound (hN : 0<N) (hp : 1≤p) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) (t : ℝ) (hmass : (∫x,D.ρ t x ∂sphereLaw N)=1) :
    |energy D t|≤GaussianLandscape.landscapeNorm N p J := by
  have hρ := (D.spatial t).continuous
  have hH := (Hamiltonian_contDiff J).continuous
  have hi₁ := continuous_sphere_integrable hN ((hρ.mul hH).norm)
  have hi₂ : Integrable (fun x : Vector N => D.ρ t x*((N:ℝ)*GaussianLandscape.landscapeNorm N p J))
      (sphereLaw N) := continuous_sphere_integrable hN (hρ.mul continuous_const)
  have hm := integral_mono_ae hi₁ hi₂ (by
    filter_upwards [SphereGibbsEntropy.sphere_Hamiltonian_bound hN hp J,physicalSphere_ae hN] with x hx hxs
    change ‖D.ρ t x*Hamiltonian N p J x‖≤D.ρ t x*((N:ℝ)*GaussianLandscape.landscapeNorm N p J)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (D.positive t x hxs)]
    exact mul_le_mul_of_nonneg_left hx (D.positive t x hxs).le)
  rw [integral_mul_const,hmass,one_mul] at hm
  have hh := (norm_integral_le_integral_norm
    (f:=fun x : Vector N => D.ρ t x*Hamiltonian N p J x)).trans hm
  unfold energy
  rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_pos (Nat.cast_pos.mpr hN)]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr (by
    simpa only [Real.norm_eq_abs,mul_comm] using hh)

end SphericalAging.SphereOnlyEnergyCurrent
