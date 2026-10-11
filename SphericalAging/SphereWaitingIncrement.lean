module

public import SphericalAging.SphereWaitingCurrent
public import SphericalAging.SphereEnergyIncrement
public import SphericalAging.SphereOnSphereCurrent

public section

/-! Actual fixed-lag waiting increments. The mean derivative premise is the
genuine tangent Frechet derivative, rather than a current or increment bound. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereWaitingIncrement
open Set MeasureTheory FiniteModel SphereInitialLaw HardSphereDynamics
open SphereFisherHelly SphereOnSphereCurrent SphereWaitingCurrent SphereQuenchedFDT
open SphereIntegratedFDT SphereEntropyBudget SphereMixedDerivatives SphereFisherCurrent
open SphereEntropyDissipation SphereRotationGeometry SphereCoordinateScore
open SphericalIntegrationByParts
open scoped Topology InnerProductSpace

@[expose] def waitingCurrent {N p : ℕ} {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (J : Disorder N p) (τ w : ℝ) : ℝ :=
  -(∫ x : Vector N,E.ρ J w x*⟪tangentScore β J (E.ρ J w) x,
    projection x (gradient (waitingObservable (M.m J τ)) x)⟫_ℝ ∂sphereLaw N)

theorem mean_row_contDiff {N p : ℕ} {β : ℝ} (M : SphereBackwardMean N p β)
    (J : Disorder N p) (τ : ℝ) : ContDiff ℝ 2 (M.m J τ) := by
  simpa only [Function.comp_def,Function.uncurry,id_eq] using
    (M.smooth J).comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (τ,x)))

theorem waitingCurrent_continuous {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (J : Disorder N p) (τ : ℝ) :
    Continuous (waitingCurrent E M J τ) := by
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hφ := waitingObservable_contDiff_two (mean_row_contDiff M J τ)
  have hg : Continuous (gradient (waitingObservable (M.m J τ))) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (hφ.continuous_fderiv (by norm_num))
  have hF : Continuous (fun x : Vector N => projection x (gradient (waitingObservable (M.m J τ)) x)) := by
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N:ℝ)).smul continuous_id)
  unfold waitingCurrent
  apply Continuous.neg
  apply continuous_sphere_parameter_integral hN
  exact hρ.continuous.mul ((joint_tangentScore_continuous β J hρ (E.positive J)).inner
    (hF.comp continuous_snd))

theorem waiting_hasDerivAt {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (J : Disorder N p) (τ : ℝ) {w : ℝ} (hw : 0≤w) :
    HasDerivAt (fun v => quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v)
      (waitingCurrent E M J τ w) w := by
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  exact waiting_clock_current_hasDerivAt hN β J hρ (timeSlope_contDiff_one hρ).continuous
    (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num))) (M.smooth J) w τ
    (E.positive J w) (E.forward J w hw)

theorem waiting_increment_current {N p : ℕ} (hN : 0<N) {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (J : Disorder N p) (τ : ℝ)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v-
      quenchedCorrelation (E.ρ J) (M.m J) (u+τ) u=
        ∫ w in u..v,waitingCurrent E M J τ w := by
  have hρ := (E.smooth J).continuous
  have hφ := (waitingObservable_contDiff_two (mean_row_contDiff M J τ)).continuous
  have hc : Continuous (fun v => quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v) := by
    have he : (fun v => quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v)=
        (fun v => ∫ x : Vector N,E.ρ J v x*waitingObservable (M.m J τ) x ∂sphereLaw N) := by
      funext v
      rw [quenchedCorrelation_eq_inner hN hρ (M.smooth J).continuous,← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp [waitingObservable];ring
    rw [he]
    exact continuous_sphere_parameter_integral hN (hρ.mul (hφ.comp continuous_snd))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hc.continuousOn
    (fun w hw => waiting_hasDerivAt hN E M J τ (hu.trans hw.1.le))
    ((waitingCurrent_continuous hN E M J τ).intervalIntegrable u v)).symm

theorem waiting_increment_square_bound {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β) (J : Disorder N p)
    {τ B u v : ℝ} (hτ : 0≤τ) (hB : 0≤B) (hu : 0≤u) (huv : u≤v)
    (hDm : ∀ x,OnSphere x → ∀ z,‖fderiv ℝ (M.m J τ) x (projection x z)‖≤B*‖z‖) :
    (quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v-
      quenchedCorrelation (E.ρ J) (M.m J) (u+τ) u)^2≤
        (1+B)^2*(v-u)*(∫ w in u..v,fisherInformation β J (E.ρ J w)/(N:ℝ)) := by
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hb w (hw : 0≤w) : (waitingCurrent E M J τ w)^2≤
      (1+B)^2*(fisherInformation β J (E.ρ J w)/(N:ℝ)) := by
    have hh := waiting_clock_fisher_bound hN β J hρ (timeSlope_contDiff_one hρ).continuous
      (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num))) (M.smooth J) w τ
      (E.positive J w) (E.forward J w hw) (SphereEnergyIncrement.density_mass hN E J hw) hB
      (fun x hx => by
        have hn := M.norm_bound J τ hτ x hx
        have hs := Real.sq_sqrt (Nat.cast_nonneg N)
        nlinarith [norm_nonneg (M.m J τ x),Real.sqrt_nonneg (N:ℝ)]) hDm
    rw [(waiting_hasDerivAt hN E M J τ hw).deriv] at hh
    convert hh using 1 <;> ring
  rcases huv.eq_or_lt with he | hlt
  · subst v;simp
  rw [waiting_increment_current hN E M J τ hu huv]
  have hc := waitingCurrent_continuous hN E M J τ
  have hFI := (SphereFisherClock.spherical_fisher_continuous hN β J
    ((E.smooth J).of_le (by norm_num)) (E.positive J)).div_const (N:ℝ)
  have hm := intervalIntegral.integral_mono_on (μ := volume) huv
    ((hc.pow 2).intervalIntegrable u v) ((hFI.const_mul ((1+B)^2)).intervalIntegrable u v)
      (fun w hw => hb w (hu.trans hw.1))
  rw [intervalIntegral.integral_const_mul] at hm
  have hh := (ResponseTransport.interval_square_bound hlt (hc.intervalIntegrable u v)
    ((hc.pow 2).intervalIntegrable u v)).trans
      (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr huv))
  convert hh using 1 <;> ring

end SphericalAging.SphereWaitingIncrement
