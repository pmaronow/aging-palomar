module

public import SphericalAging.SphereOnlyEnergyCurrent

public section

/-! Supported forward-density expectations and currents for any smooth
observable, including the fixed-lag waiting observable. Evolution is
required only on the sphere and at strictly positive times. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereOnlyObservableCurrent
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereRotationGeometry
open SphereEntropyDissipation SphereGeneratorIntegrationByParts SphereCarreDuChamp
open SphereOnlyForwardCalculus SphereOnlyLocalParameterIntegral SphereOnlyEnergyCurrent
open SphereOnlyAllTimeContinuity SphereOnlyFisherCurrentContinuity SphereOnlyFisherContinuity
open scoped Topology InnerProductSpace
variable {N p : ℕ}

@[expose] def expectation {β : ℝ} {J : Disorder N p} (D : SphereForwardData N p β J)
    (f : Vector N→ℝ) (t : ℝ) : ℝ := ∫x,D.ρ t x*f x ∂sphereLaw N

@[expose] def current {β : ℝ} {J : Disorder N p} (D : SphereForwardData N p β J)
    (f : Vector N→ℝ) (t : ℝ) : ℝ :=
  -(∫x,D.ρ t x*⟪tangentScore β J (D.ρ t) x,projection x (gradient f x)⟫_ℝ ∂sphereLaw N)

theorem expectation_hasDerivAt (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {f : Vector N→ℝ} (hf : ContDiff ℝ 1 f)
    {t : ℝ} (ht : 0<t) : HasDerivAt (expectation D f) (current D f t) t := by
  have hF : Continuous (Function.uncurry (fun u x => D.ρ u x*f x)) :=
    D.joint.mul (hf.continuous.comp continuous_snd)
  have hF' : Continuous (Function.uncurry (fun u x => D.ρdot u x*f x)) :=
    D.jointDot.mul (hf.continuous.comp continuous_snd)
  have hd := hasDerivAt_integral_of_sphere_derivative hN hF hF'
    (a:=t/2) (b:=t+1) (t₀:=t) (by linarith) (by linarith)
    (fun u hu x hx => (D.timeDerivative u (by linarith [hu.1]) x hx).mul_const (f x))
  apply hd.congr_deriv
  have hpair := forward_density_current_pairing_onSphere hN (1/(2*(N:ℝ))) β J
    (SphereCasimirGamma2.rotations N) (fun ij => coordinateRotation_skew ij.1 ij.2)
    ((D.spatial t).of_le (by norm_num)) (D.positive t) hf
  have he : (∫x,D.ρdot t x*f x ∂sphereLaw N)=
      ∫x,f x*forwardDensitySlope (1/(2*(N:ℝ))) β J
        (SphereCasimirGamma2.rotations N) (D.ρ t) x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [D.spherePDE t ht x hx]
    exact mul_comm _ _
  rw [he,hpair]
  unfold current
  congr 1
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [canonical_rotationGamma hN _ _ x hx]
  rfl

theorem projected_gradient_continuous {f : Vector N→ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fun x : Vector N => projection x (gradient f x)) := by
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num))
  unfold projection
  exact hg.sub (((continuous_id.inner hg).div_const (N:ℝ)).smul continuous_id)

theorem current_continuous (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {f : Vector N→ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (current D f) := by
  have hF := projected_gradient_continuous hf
  have hscore := joint_tangentScore_continuousOn_all β J D.joint D.jointFirst
    (fun t => (D.spatial t).of_le (by norm_num)) D.positive
  unfold current
  apply Continuous.neg
  apply supported_integral_continuous hN
  · apply (D.joint.continuousOn.mul (hscore.inner (hF.comp continuous_snd).continuousOn)).congr
    intro z _
    rfl
  · intro t
    exact (D.spatial t).continuous.aestronglyMeasurable.mul
      ((tangentScore_aestronglyMeasurable hN β J ((D.spatial t).of_le (by norm_num))
        (D.positive t)).inner hF.aestronglyMeasurable)

theorem expectation_continuous (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {f : Vector N→ℝ} (hf : Continuous f) :
    Continuous (expectation D f) := by
  unfold expectation
  apply SphereEntropyBudget.continuous_sphere_parameter_integral hN
  exact D.joint.mul (hf.comp continuous_snd)

theorem expectation_increment_current (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {f : Vector N→ℝ} (hf : ContDiff ℝ 2 f)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    expectation D f v-expectation D f u=∫t in u..v,current D f t :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (expectation_continuous hN D hf.continuous).continuousOn
    (fun t ht => expectation_hasDerivAt hN D (hf.of_le (by norm_num)) (hu.trans_lt ht.1))
    ((current_continuous hN D hf).intervalIntegrable u v)).symm

theorem current_square_le_fisher (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {f : Vector N→ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ)
    (hmass : (∫x,D.ρ t x ∂sphereLaw N)=1) {M : ℝ}
    (hbound : ∀x,OnSphere x→‖projection x (gradient f x)‖^2≤M) :
    (current D f t)^2≤M*fisherInformation β J (D.ρ t) := by
  unfold current
  rw [neg_sq]
  exact score_pairing_square_le_onSphere hN β J ((D.spatial t).of_le (by norm_num))
    (D.positive t) hmass (projected_gradient_continuous hf) hbound

theorem expectation_increment_square_bound (hN : 0<N) {β : ℝ} {J : Disorder N p}
    (D : SphereForwardData N p β J) {f : Vector N→ℝ} (hf : ContDiff ℝ 2 f)
    {u v M : ℝ} (hu : 0≤u) (huv : u≤v)
    (hmass : ∀t,t∈Icc u v→(∫x,D.ρ t x ∂sphereLaw N)=1)
    (hbound : ∀x,OnSphere x→‖projection x (gradient f x)‖^2≤M) :
    (expectation D f v-expectation D f u)^2≤M*(v-u)*(∫t in u..v,fisherInformation β J (D.ρ t)) := by
  rcases huv.eq_or_lt with he | hlt
  · subst v
    simp
  rw [expectation_increment_current hN D hf hu huv]
  have hc := current_continuous hN D hf
  have hFI := D.fisher_continuous hN
  have hm := intervalIntegral.integral_mono_on (μ:=volume) huv
    ((hc.pow 2).intervalIntegrable u v) ((hFI.const_mul M).intervalIntegrable u v)
    (fun t ht => current_square_le_fisher hN D hf t (hmass t ht) hbound)
  rw [intervalIntegral.integral_const_mul] at hm
  have hh := (ResponseTransport.interval_square_bound hlt (hc.intervalIntegrable u v)
    ((hc.pow 2).intervalIntegrable u v)).trans
      (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr huv))
  convert hh using 1 <;> ring

end SphericalAging.SphereOnlyObservableCurrent
