module

public import SphericalAging.ActualSphereOnlyTensorProductCurrent
public import SphericalAging.ActualForkMomentComparison
public import SphericalAging.ActualSphereForwardDensityLaw

public section

/-! Genuine sphere-initial fork/current endpoint identities, with the
waiting law and forward density realized by the actual diffusion. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereOnlyForkEndpoints
open MeasureTheory ProbabilityTheory Set Filter FiniteModel HardSphereDynamics
open ActualSphereForkMoment ActualSphereForkConditional ActualSphereForkEndpoints
open ActualSphereOnlyTensorProductCurrent ActualSphereTensorSemigroup
open ActualSphereForwardDensityLaw ActualSphereUniformInitialLaw ActualSphereGibbsDensity
open ActualForkOverlapLaw ActualForkMomentComparison SphereInitialLaw ActualModelOverlapVariance
open scoped NNReal ENNReal InnerProductSpace
variable {N p k : ℕ}

theorem initialWaiting_hasLaw_density (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s : ℝ≥0) :
    HasLaw (initialWaiting β R hR J s) (densityLaw β R hR J s) (initialLaw N) := by
  rw [←waitingLaw_eq_densityLaw hN hp β R hR hNR J s]
  exact ⟨(initialWaiting_measurable β R hR J s).aemeasurable,rfl⟩

theorem initialForkMoment_eq_actual_density (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s a b : ℝ≥0) :
    initialForkMoment (k:=k) β R hR J s a b=
      ∫x : State N,forwardDensity β R hR J s x*
        ⟪tensorMean (k:=k) β R hR J a x,tensorMean (k:=k) β R hR J b x⟫_ℝ ∂sphereLaw N := by
  rw [initialForkMoment,waitingForkMoment_eq_tensorMean
    (initialWaiting_measurable β R hR J s)
    (initialWaiting_onSphere hN β R hR hNR J s) hN β R hR hNR J a b]
  have hm : Continuous (fun x : State N =>
      ⟪tensorMean (k:=k) β R hR J a x,tensorMean (k:=k) β R hR J b x⟫_ℝ) :=
    (tensorMean_contDiff_two β R hR J a).continuous.inner
      (tensorMean_contDiff_two β R hR J b).continuous
  have he := (initialWaiting_hasLaw_density hN hp β R hR hNR J s).integral_comp
    hm.aestronglyMeasurable
  simp only [Function.comp_def] at he
  rw [he,densityLaw_test_integral hN hp β R hR hNR J s]

theorem pairing_zero_eq_fork (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (T a d : ℝ≥0) :
    actualTensorPairing (k:=k) β R hR J T a d 0=
      initialForkMoment (k:=k) β R hR J T a d := by
  simpa only [actualTensorPairing,add_zero,sub_zero,realTensorMean,Real.toNNReal_coe]
    using (initialForkMoment_eq_actual_density (k:=k) hN hp β R hR hNR J T a d).symm

theorem pairing_age_eq_same_path (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (T a d : ℝ≥0) :
    actualTensorPairing (k:=k) β R hR J T a d a=
      samePathMoment (k:=k) β R hR J (T+a) (a+d) := by
  have he := (initialForkMoment_eq_actual_density (k:=k) hN hp β R hR hNR J (T+a) 0 (a+d)).symm
  have hh : actualTensorPairing (k:=k) β R hR J T a d a=
      initialForkMoment (k:=k) β R hR J (T+a) 0 (a+d) := by
    simpa only [actualTensorPairing,sub_self,realTensorMean,←NNReal.coe_add,
      Real.toNNReal_coe,Real.toNNReal_zero,add_comm] using he
  exact hh.trans (initial_zero_branch_eq_same_path hN β R hR hNR J (T+a) (a+d))

theorem pairing_increment_measurable (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T a d : ℝ≥0) :
    Measurable (fun J : Disorder N p => actualTensorPairing (k:=k) β R hR J T a d a-
      actualTensorPairing (k:=k) β R hR J T a d 0) := by
  have he : (fun J : Disorder N p => actualTensorPairing (k:=k) β R hR J T a d a-
      actualTensorPairing (k:=k) β R hR J T a d 0)=
      (fun J => samePathMoment (k:=k) β R hR J (T+a) (a+d)-
        initialForkMoment (k:=k) β R hR J T a d) := by
    funext J
    rw [pairing_age_eq_same_path hN hp β R hR hNR,
      pairing_zero_eq_fork hN hp β R hR hNR]
  rw [he]
  exact (samePathMoment_measurable hN β R hR hNR (T+a) (a+d)).sub
    (initialForkMoment_measurable β R hR T a d)

theorem pairing_increment_integral_eq_moment_difference (hN : 2≤N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T a d : ℝ≥0) :
    (∫J,actualTensorPairing (k:=k) β R hR J T a d a-
      actualTensorPairing (k:=k) β R hR J T a d 0 ∂disorderLaw N p)=
    (∫z,(actualOverlap (p:=p) β R hR (T+a) ((T+a)+(a+d)) z)^k ∂AnnealedModelLaw.law N p)-
      ∫z,(forkOverlap (p:=p) β R hR T a d z)^k ∂forkLaw N p := by
  have hn : 0<N := by omega
  simp_rw [pairing_age_eq_same_path hn hp β R hR hNR,
    pairing_zero_eq_fork hn hp β R hR hNR]
  rw [integral_sub (samePathMoment_integrable hn β R hR hNR (T+a) (a+d))
    (initialForkMoment_integrable hn β R hR hNR T a d),
    samePathMoment_annealed_actual hn β R hR hNR (T+a) (a+d),
    forkOverlap_moment hn β R hR hNR T a d]

end SphericalAging.ActualSphereOnlyForkEndpoints
