module

public import SphericalAging.ActualForkOverlapLaw
public import SphericalAging.ActualTensorUniformComparison

public section

/-! The source10.3 finite moment comparison for literal actual fork
endpoints and the actual annealed same-path overlap. Measurability is
derived from the actual endpoint law, rather than assumed for the density. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkMomentComparison
open Set Filter MeasureTheory FiniteModel HardSphereDynamics GaussianLandscape
open ActualSphereForkMoment ActualSphereForkEndpoints ActualForkOverlapLaw
open ActualTensorUniformComparison ActualTensorAnnealedComparison ActualSphereTensorProductCurrent
open SphereFisherHelly ForkFisherWindowLimit ActualModelOverlapVariance SphereGoodEventFisherClock
open SphereBadEventFisherMass
open scoped Topology NNReal InnerProductSpace

theorem initialForkMoment_integrable {N p k : ℕ} (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T a d : ℝ≥0) :
    Integrable (fun J => initialForkMoment (k:=k) β R hR J T a d) (disorderLaw N p) :=
  Integrable.of_bound (initialForkMoment_measurable β R hR T a d).aestronglyMeasurable 1
    (ae_of_all _ (fun J => by
      rw [Real.norm_eq_abs]
      exact waitingForkMoment_abs_le_one (initialWaiting_measurable β R hR J T)
        (initialWaiting_onSphere hN β R hR hNR J T) hN β R hR hNR J a d))

theorem samePathMoment_integrable {N p k : ℕ} (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (s b : ℝ≥0) :
    Integrable (fun J => samePathMoment (k:=k) β R hR J s b) (disorderLaw N p) := by
  have he : (fun J : Disorder N p => samePathMoment (k:=k) β R hR J s b)=
      (fun J => initialForkMoment (k:=k) β R hR J s 0 b) :=
    funext (fun J => (initial_zero_branch_eq_same_path hN β R hR hNR J s b).symm)
  rw [he]
  exact initialForkMoment_integrable hN β R hR hNR s 0 b

theorem pairing_increment_integral_eq_moment_difference {N p k : ℕ} (hN : 2≤N)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (hLaw : WaitingDensityLaw β R hR E)
    (T a d : ℝ≥0) :
    (∫J,actualTensorPairing (k:=k) β R hR E J T a d a-
      actualTensorPairing (k:=k) β R hR E J T a d 0 ∂disorderLaw N p)=
    (∫z,(actualOverlap (p:=p) β R hR (T+a) ((T+a)+(a+d)) z)^k ∂AnnealedModelLaw.law N p)-
      ∫z,(forkOverlap (p:=p) β R hR T a d z)^k ∂forkLaw N p := by
  have hn : 0<N := by omega
  simp_rw [pairing_age_eq_same_path hn β R hR hNR E hLaw,
    pairing_zero_eq_fork hn β R hR hNR E hLaw]
  rw [integral_sub (samePathMoment_integrable hn β R hR hNR (T+a) (a+d))
    (initialForkMoment_integrable hn β R hR hNR T a d),
    samePathMoment_annealed_actual hn β R hR hNR (T+a) (a+d),
    forkOverlap_moment hn β R hR hNR T a d]

/-- Exact printed finite-N coefficient, with the proved bad-landscape
probability bound exp(-N). It holds for the two printed moments. -/
theorem actual_fork_moment_comparison {N p k : ℕ} (hN : 2≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (hLaw : WaitingDensityLaw β R hR E)
    (T a d : ℝ≥0) (hk : 1≤k) :
    |(∫z,(forkOverlap (p:=p) β R hR T a d z)^k ∂forkLaw N p)-
      ∫z,(actualOverlap (p:=p) β R hR (T+a) ((T+a)+(a+d)) z)^k ∂AnnealedModelLaw.law N p|≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*((a:ℝ)+d)))*
        Real.sqrt ((a:ℝ)*(∫w in (T:ℝ)..((T:ℝ)+a),E.full w))+2*Real.exp (-(N:ℝ)) := by
  have hn : 0<N := by omega
  have hh := actualTensorPairing_annealed_comparison (by omega : 2≤N) hp
    hk β R hR hNR E T.coe_nonneg a.coe_nonneg d.coe_nonneg
    (pairing_increment_measurable (k:=k) hn β R hR hNR E hLaw T a d).aestronglyMeasurable
  rw [pairing_increment_integral_eq_moment_difference hN β R hR hNR E hLaw T a d,
    abs_sub_comm] at hh
  exact hh

theorem actual_fork_moment_uniform_bound {N p k : ℕ} (hN : 2≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (hLaw : WaitingDensityLaw β R hR E)
    {T L a d : ℝ} (hT : 0≤T) (ha : a∈Icc 0 L) (hd : d∈Icc 0 L)
    (hk : 1≤k) :
    |(∫z,(forkOverlap (p:=p) β R hR T.toNNReal a.toNNReal d.toNNReal z)^k ∂forkLaw N p)-
      ∫z,(actualOverlap (p:=p) β R hR (T.toNNReal+a.toNNReal)
        ((T.toNNReal+a.toNNReal)+(a.toNNReal+d.toNNReal)) z)^k ∂AnnealedModelLaw.law N p|≤
      comparisonError (windowCoefficient p k β L) L E T := by
  have hn : 0<N := by omega
  have hm : AEStronglyMeasurable (fun J => actualTensorPairing (k:=k) β R hR E J
      T.toNNReal a.toNNReal d.toNNReal a.toNNReal-
      actualTensorPairing (k:=k) β R hR E J T.toNNReal a.toNNReal d.toNNReal 0)
      (disorderLaw N p) :=
    (pairing_increment_measurable (k:=k) hn β R hR hNR E hLaw
      T.toNNReal a.toNNReal d.toNNReal).aestronglyMeasurable
  simp only [Real.coe_toNNReal T hT,Real.coe_toNNReal a ha.1,Real.coe_toNNReal d hd.1] at hm
  have hh := actualTensorPairing_uniform_window_bound (by omega : 2≤N) hp
    hk β R hR hNR E hT ha hd hm
  have he := pairing_increment_integral_eq_moment_difference (k:=k) hN β R hR hNR E hLaw
    T.toNNReal a.toNNReal d.toNNReal
  simp only [Real.coe_toNNReal T hT,Real.coe_toNNReal a ha.1,Real.coe_toNNReal d hd.1] at he
  rw [he,abs_sub_comm] at hh
  exact hh

end SphericalAging.ActualForkMomentComparison
