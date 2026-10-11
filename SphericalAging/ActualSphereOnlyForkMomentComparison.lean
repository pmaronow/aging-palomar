module

public import SphericalAging.ActualSphereOnlyForkEndpoints
public import SphericalAging.ActualSphereOnlyTensorUniformComparison

public section

/-! The source10.3 finite moment comparison for literal actual fork
endpoints and the actual annealed same-path overlap. Measurability is
derived from the actual endpoint law, rather than assumed for the density. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereOnlyForkMomentComparison
open Set Filter MeasureTheory FiniteModel HardSphereDynamics GaussianLandscape
open ActualSphereForkMoment ActualSphereForkEndpoints ActualForkOverlapLaw
open ActualSphereOnlyTensorUniformComparison ActualSphereOnlyTensorAnnealedComparison ActualSphereOnlyTensorProductCurrent
open ActualSphereOnlyForkEndpoints ActualSphereRestrictedFisherBudget
open ActualForkFisherWindowLimit ActualModelOverlapVariance SphereGoodEventFisherClock
open SphereBadEventFisherMass
open scoped Topology NNReal InnerProductSpace

/-- Exact printed finite-N coefficient, with the proved bad-landscape
probability bound exp(-N). It holds for the two printed moments. -/
theorem actual_fork_moment_comparison {N p k : ℕ} (hN : 2≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (T a d : ℝ≥0) (hk : 1≤k) :
    |(∫z,(forkOverlap (p:=p) β R hR T a d z)^k ∂forkLaw N p)-
      ∫z,(actualOverlap (p:=p) β R hR (T+a) ((T+a)+(a+d)) z)^k ∂AnnealedModelLaw.law N p|≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*((a:ℝ)+d)))*
        Real.sqrt ((a:ℝ)*(∫w in (T:ℝ)..((T:ℝ)+a),full (N:=N) (p:=p) β R hR w))+2*Real.exp (-(N:ℝ)) := by
  have hn : 0<N := by omega
  have hh := actualTensorPairing_annealed_comparison (by omega : 2≤N) hp
    hk β R hR hNR T.coe_nonneg a.coe_nonneg d.coe_nonneg
    (pairing_increment_measurable (k:=k) hn (by omega) β R hR hNR T a d).aestronglyMeasurable
  rw [pairing_increment_integral_eq_moment_difference hN (by omega) β R hR hNR T a d,
    abs_sub_comm] at hh
  exact hh

theorem actual_fork_moment_uniform_bound {N p k : ℕ} (hN : 2≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {T L a d : ℝ} (hT : 0≤T) (ha : a∈Icc 0 L) (hd : d∈Icc 0 L)
    (hk : 1≤k) :
    |(∫z,(forkOverlap (p:=p) β R hR T.toNNReal a.toNNReal d.toNNReal z)^k ∂forkLaw N p)-
      ∫z,(actualOverlap (p:=p) β R hR (T.toNNReal+a.toNNReal)
        ((T.toNNReal+a.toNNReal)+(a.toNNReal+d.toNNReal)) z)^k ∂AnnealedModelLaw.law N p|≤
      comparisonError (N:=N) (p:=p) (windowCoefficient p k β L) L β R hR T := by
  have hn : 0<N := by omega
  have hm : AEStronglyMeasurable (fun J => actualTensorPairing (k:=k) β R hR J
      T.toNNReal a.toNNReal d.toNNReal a.toNNReal-
      actualTensorPairing (k:=k) β R hR J T.toNNReal a.toNNReal d.toNNReal 0)
      (disorderLaw N p) :=
    (pairing_increment_measurable (k:=k) hn (by omega) β R hR hNR
      T.toNNReal a.toNNReal d.toNNReal).aestronglyMeasurable
  simp only [Real.coe_toNNReal T hT,Real.coe_toNNReal a ha.1,Real.coe_toNNReal d hd.1] at hm
  have hh := actualTensorPairing_uniform_window_bound (by omega : 2≤N) hp
    hk β R hR hNR hT ha hd hm
  have he := pairing_increment_integral_eq_moment_difference (p:=p) (k:=k) hN (by omega) β R hR hNR
    T.toNNReal a.toNNReal d.toNNReal
  simp only [Real.coe_toNNReal T hT,Real.coe_toNNReal a ha.1,Real.coe_toNNReal d hd.1] at he
  rw [he,abs_sub_comm] at hh
  exact hh

end SphericalAging.ActualSphereOnlyForkMomentComparison
