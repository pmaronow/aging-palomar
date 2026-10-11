module

public import SphericalAging.ActualSphereMeanConditionalPairing
public import SphericalAging.ActualForkOverlapLaw
public import SphericalAging.ActualForkMeanBridge

public section

/-! The literal forward-density/backward-mean correlation equals the
full-model expected physical overlap. The waiting law, conditional mean
pairing and all finite Fubini inputs are derived from the actual SDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereDensityCorrelation
open FiniteModel HardSphereDynamics SphereInitialLaw SphericalIntegrationByParts SphereQuenchedFDT
open ActualSphereTransition ActualSphereMeanSpatialInterface ActualSphereGibbsDensity
open ActualSphereUniformInitialLaw ActualSphereForwardDensityLaw ActualSphereDensityResponse
open ActualSphereMeanConditionalPairing ActualSphereForkEndpoints ActualForkOverlapLaw
open ActualModelOverlapVariance ActualForkMeanBridge
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem densityCorrelation_eq_uniform_initial (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (H s : ℝ≥0) :
    quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) H s=
      (∫z : State N×VectorBrownian.Space N,
        ⟪initialWaiting β R hR J s z,realMean β R hR J ((H:ℝ)-(s:ℝ))
          (initialWaiting β R hR J s z)⟫_ℝ ∂initialLaw N)/(N:ℝ) := by
  have hc : Continuous (fun x : State N => ⟪x,realMean β R hR J ((H:ℝ)-(s:ℝ)) x⟫_ℝ) :=
    continuous_id.inner (realMean_spatial_contDiff β R hR J ((H:ℝ)-(s:ℝ))).continuous
  rw [quenchedCorrelation_eq_inner hN (forwardDensity_joint_continuous hN hp β R hR J)
      (realMean_joint_continuous β R hR J),
    ←densityLaw_test_integral hN hp β R hR hNR J s,
    ←waitingLaw_eq_densityLaw hN hp β R hR hNR J s,waitingLaw,
    integral_map (terminal_measurable _ β R hR J s).aemeasurable hc.aestronglyMeasurable]
  rfl

theorem uniform_samePath_pairing_integrable (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s t : ℝ≥0) :
    Integrable (fun z : State N×VectorBrownian.Space N =>
      ⟪initialWaiting β R hR J s z,initialWaiting β R hR J t z⟫_ℝ/(N:ℝ)) (initialLaw N) := by
  have hm := ((continuous_fst.inner continuous_snd).measurable.comp
    ((initialWaiting_measurable β R hR J s).prodMk (initialWaiting_measurable β R hR J t))).div_const (N:ℝ)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [initialWaiting_onSphere hN β R hR hNR J s,
    initialWaiting_onSphere hN β R hR hNR J t] with z hs ht
  exact FiniteCorrelationIto.overlap_abs_le_one hN hs ht

theorem densityCorrelation_eq_samePathMoment (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (H s : ℝ≥0) (hs : s≤H) :
    quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) H s=
      samePathMoment (k:=1) β R hR J s (H-s) := by
  have hrm : realMean β R hR J ((H-s:ℝ≥0):ℝ)=
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (H-s) := by
    funext y
    simp only [realMean,Real.toNNReal_coe]
  have hc : Continuous (fun x : State N => ⟪x,realMean β R hR J ((H:ℝ)-(s:ℝ)) x⟫_ℝ) :=
    continuous_id.inner (realMean_spatial_contDiff β R hR J ((H:ℝ)-(s:ℝ))).continuous
  rw [densityCorrelation_eq_uniform_initial hN hp β R hR hNR J H s]
  unfold initialLaw initialWaiting ActualSphereForkMoment.endpoint
  rw [integral_prod _ (uniformWaiting_continuous_test_integrable hN β R hR hNR J s hc),←integral_div]
  unfold samePathMoment
  simp only [pow_one]
  rw [show initialLaw N=(sphereLaw N).prod (VectorBrownian.law N) from rfl,
    integral_prod _ (uniform_samePath_pairing_integrable hN β R hR hNR J s (s+(H-s)))]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hxS := (onSphere_iff_norm_sq x).mpr hx
  rw [←NNReal.coe_sub hs,hrm]
  simp_rw [integral_div]
  exact congrArg (fun r : ℝ => r/(N:ℝ))
    (mean_waiting_inner_identity (Nat.ne_of_gt hN) β R hR hNR J x hxS s (H-s)).symm

theorem densityCorrelation_annealed_eq_actualMean (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H s : ℝ≥0) (hs : s≤H) :
    (∫J : Disorder N p,quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) H s
      ∂disorderLaw N p)=actualMean (N:=N) (p:=p) β R hR H s := by
  simp_rw [densityCorrelation_eq_samePathMoment hN hp β R hR hNR _ H s hs]
  rw [samePathMoment_annealed_actual (k:=1) hN β R hR hNR s (H-s),add_tsub_cancel_of_le hs]
  simp only [pow_one,actualMean,Real.toNNReal_coe]
  apply integral_congr_ae
  exact .of_forall (fun z => by unfold actualOverlap;rw [real_inner_comm])

theorem densityCorrelation_disorder_integrable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H s : ℝ≥0) (hs : s≤H) :
    Integrable (fun J : Disorder N p => quenchedCorrelation (forwardDensity β R hR J)
      (realMean β R hR J) H s) (disorderLaw N p) := by
  have hi : Integrable (fun z : Disorder N p×(State N×VectorBrownian.Space N) =>
      sameOverlap β R hR s H z) ((disorderLaw N p).prod (initialLaw N)) := by
    apply Integrable.of_bound (sameOverlap_measurable (N:=N) (p:=p) β R hR s H).aestronglyMeasurable 1
    simpa only [Real.norm_eq_abs] using sameOverlap_abs_le_one hN β R hR hNR s H
  have he : (fun J : Disorder N p => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) H s)=
      (fun J : Disorder N p => ∫z : State N×VectorBrownian.Space N,sameOverlap β R hR s H (J,z) ∂initialLaw N) := by
    funext J
    rw [densityCorrelation_eq_samePathMoment hN hp β R hR hNR J H s hs]
    simp only [samePathMoment,pow_one,add_tsub_cancel_of_le hs,sameOverlap,FiniteCorrelationIto.overlap]
  rw [he]
  exact hi.integral_prod_left

theorem densityCorrelation_abs_le_one (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (H s : ℝ≥0) (hs : s≤H) :
    |quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) H s|≤1 := by
  rw [densityCorrelation_eq_samePathMoment hN hp β R hR hNR J H s hs]
  unfold samePathMoment
  simp only [pow_one]
  have hh := norm_integral_le_of_norm_le_const (μ:=initialLaw N) (C:=1)
    (f:=fun z : State N×VectorBrownian.Space N =>
      ⟪initialWaiting β R hR J s z,initialWaiting β R hR J (s+(H-s)) z⟫_ℝ/(N:ℝ)) (by
    filter_upwards [initialWaiting_onSphere hN β R hR hNR J s,
      initialWaiting_onSphere hN β R hR hNR J (s+(H-s))] with z hs ht
    simpa only [Real.norm_eq_abs,FiniteCorrelationIto.overlap] using FiniteCorrelationIto.overlap_abs_le_one hN hs ht)
  simpa only [Real.norm_eq_abs,probReal_univ,one_mul] using hh

end SphericalAging.ActualSphereDensityCorrelation
