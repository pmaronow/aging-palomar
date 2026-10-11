module

public import SphericalAging.ActualResponsePositiveDimension
public import SphericalAging.ActualFiniteFDTTheorem

public section

/-! Native source 5.2 for the literal same-path correlation and actual
projected physical impulse response, including N=2 and the genuine
initial-time right derivative. All density/mean and response identities,
measurability and Fubini bounds are derived from the actual diffusion. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology NNReal InnerProductSpace
namespace SphericalAging.ActualLiteralFiniteFDTTheorem
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry
open ActualSphereGibbsDensity ActualSphereMeanSpatialInterface ActualSphereDensityCorrelation
open ActualSphereDensityResponse ActualSphereTransition ActualSphereForkEndpoints
open ActualSphereAnnealedPointwiseFDT ActualSphereAnnealedCurrentMoment
open ActualFiniteFDTTheorem SphereAnnealedFisherBudget
open TwoTimeResponseTimeParameter ActualExpectedTwoTimeResponse ActualResponseJointKernel
open ActualQuenchedBrownianPairing ActualPhysicalBrownianPairing
variable {N p : ℕ}

@[expose] def physicalWaiting (t s : ℝ) : WaitingTime t.toNNReal :=
  ⟨min s.toNNReal t.toNNReal, ⟨zero_le, min_le_right _ _⟩⟩

@[expose] def physicalCorrelation (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (t s : ℝ) : ℝ :=
  ActualForkMeanBridge.actualMean (N := N) (p := p) β R hR t s

@[expose] def physicalResponse (hN : 0 < N) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (t s : ℝ) : ℝ :=
  ActualResponseKernel.annealedResponse (p := p) (Nat.ne_of_gt hN) β R hR hNR
    t.toNNReal (physicalWaiting t s)

@[expose] def physicalQuenchedCorrelation (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (J : Disorder N p) (t s : ℝ) : ℝ :=
  ∫z : State N × VectorBrownian.Space N,
    ⟪initialWaiting β R hR J t.toNNReal z, initialWaiting β R hR J s.toNNReal z⟫_ℝ /
      (N : ℝ) ∂initialLaw N

@[expose] def physicalQuenchedResponse (hN : 0 < N) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (t s : ℝ) : ℝ :=
  ∫x : State N, ActualResponseKernel.quenchedResponse (Nat.ne_of_gt hN)
    β R hR hNR t.toNNReal (physicalWaiting t s) (J,x) ∂sphereLaw N

theorem physicalCorrelation_eq_density (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    physicalCorrelation (N := N) (p := p) β R hR t s =
      annealedCorrelation (N := N) (p := p) β R hR t s := by
  have ht := hs.trans hst
  have he := densityCorrelation_annealed_eq_actualMean hN hp β R hR hNR
    t.toNNReal s.toNNReal (Real.toNNReal_mono hst)
  simpa only [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht,
    physicalCorrelation, annealedCorrelation] using he.symm

theorem physicalResponse_eq_density (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    physicalResponse (p := p) hN β R hR hNR t s =
      annealedResponse (N := N) (p := p) β R hR t s := by
  have ht := hs.trans hst
  have he := ActualResponsePositiveDimension.densityResponse_annealed_eq_physicalResponse
    hN hp β R hR hNR t.toNNReal (physicalWaiting t s)
  simpa only [physicalResponse, physicalWaiting, min_eq_left (Real.toNNReal_mono hst),
    Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht, annealedResponse] using he.symm

theorem physicalQuenchedCorrelation_eq_density (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    physicalQuenchedCorrelation β R hR J t s =
      SphereQuenchedFDT.quenchedCorrelation (forwardDensity β R hR J)
        (realMean β R hR J) t s := by
  have ht := hs.trans hst
  have hstNN := Real.toNNReal_mono hst
  have he := densityCorrelation_eq_samePathMoment hN hp β R hR hNR J
    t.toNNReal s.toNNReal hstNN
  rw [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht] at he
  rw [he]
  unfold physicalQuenchedCorrelation samePathMoment
  simp only [pow_one, add_tsub_cancel_of_le hstNN]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by dsimp only; rw [real_inner_comm]

theorem physicalQuenchedResponse_eq_density (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    physicalQuenchedResponse hN β R hR hNR J t s =
      SphereQuenchedFDT.quenchedResponse (forwardDensity β R hR J)
        (realMean β R hR J) t s := by
  have ht := hs.trans hst
  have hstNN := Real.toNNReal_mono hst
  have hi := uniformWaiting_continuous_test_integrable hN β R hR hNR J s.toNNReal
    (tangentMeanTrace_continuous β R hR J (t-s))
  have hd := densityResponse_eq_uniform_initial hN hp β R hR hNR J t.toNNReal s.toNNReal
  rw [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht, integral_prod _ hi, ← integral_div] at hd
  rw [hd]
  unfold physicalQuenchedResponse
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hxS := (onSphere_iff_norm_sq x).mpr hx
  simp only [physicalWaiting, min_eq_left hstNN]
  rw [ActualResponseKernel.quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN)
    β R hR hNR t.toNNReal ⟨s.toNNReal, ⟨zero_le,hstNN⟩⟩ (J,x) hxS]
  rw [normalizedTrace_eq_joint_mean_derivative (Nat.ne_of_gt hN) β R hR hNR
    s.toNNReal (t.toNNReal+1) (t.toNNReal-s.toNNReal)
      ((tsub_le_self : t.toNNReal-s.toNNReal ≤ t.toNNReal).trans (le_add_right le_rfl))
      (by positivity) (J,x) hxS]
  rw [← integral_div]
  congr 1
  have hm : realMean β R hR J (t-s) =
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J
        (t.toNNReal-s.toNNReal) := by
    funext y
    rw [← Real.coe_toNNReal t ht, ← Real.coe_toNNReal s hs, ← NNReal.coe_sub hstNN]
    simp only [realMean, Real.toNNReal_coe]
  simp only [tangentMeanTrace, hm, integral_div]

theorem physical_response_parameter_integrable (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (H : ℝ≥0) (s : WaitingTime H) :
    Integrable (ActualResponseKernel.quenchedResponse (p := p) (Nat.ne_of_gt hN)
      β R hR hNR H s) (AnnealedModelLaw.parameterLaw N p) := by
  have hi := ActualResponsePositiveDimension.backwardTraceField_integrable
    hN hp β R hR hNR H s
  apply hi.integral_prod_left.congr
  filter_upwards [AnnealedModelLaw.parameter_initial_onSphere hN p] with q hq
  rw [quenchedResponse_eq_backwardMeanKernel (Nat.ne_of_gt hN) β R hR hNR H s q hq]
  unfold backwardMeanKernel
  rw [← integral_div]
  rfl

theorem physical_quenched_correlation_hasDerivWithinAt (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (physicalQuenchedCorrelation β R hR J t)
      (physicalQuenchedResponse hN β R hR hNR J t s -
        ActualSphereCurrent.current β R hR J t s) (Ici 0) s := by
  rw [physicalQuenchedResponse_eq_density hN hp β R hR hNR J hs hst.le]
  apply (ActualSphereFDTZeroEndpoint.actual_quenched_fdt_hasDerivWithinAt
    hN hp β R hR hNR J hs hst).congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hst)] with u hu hut
    exact physicalQuenchedCorrelation_eq_density hN hp β R hR hNR J hu hut.le
  · exact hs

theorem physical_quenched_fdt_current (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    physicalQuenchedResponse hN β R hR hNR J t s -
      derivWithin (physicalQuenchedCorrelation β R hR J t) (Ici 0) s =
      (∫x : State N, forwardDensity β R hR J s x *
        ⟪realMean β R hR J (t-s) x,
          tangentScore β J (forwardDensity β R hR J s) x⟫_ℝ ∂sphereLaw N)/(N : ℝ) := by
  rw [(physical_quenched_correlation_hasDerivWithinAt hN hp β R hR hNR J hs hst).derivWithin
    (uniqueDiffOn_Ici (0 : ℝ) s hs),sub_sub_cancel]
  rfl

theorem physical_quenched_correlation_hasDerivAt (hN : 0 < N) (hp : 1 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0 < s) (hst : s < t) :
    HasDerivAt (physicalQuenchedCorrelation β R hR J t)
      (physicalQuenchedResponse hN β R hR hNR J t s -
        ActualSphereCurrent.current β R hR J t s) s :=
  (physical_quenched_correlation_hasDerivWithinAt hN hp β R hR hNR J hs.le hst).hasDerivAt (Ici_mem_nhds hs)

theorem physical_correlation_hasDerivWithinAt (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (physicalCorrelation (N := N) (p := p) β R hR t)
      (physicalResponse (p := p) hN β R hR hNR t s -
        annealedCurrent (N := N) (p := p) β R hR t s) (Ici 0) s := by
  rw [physicalResponse_eq_density hN hp β R hR hNR hs hst.le]
  apply (actual_annealed_correlation_hasDerivWithinAt hN hp β R hR hNR hs hst).congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hst)] with u hu hut
    exact physicalCorrelation_eq_density hN (by omega) β R hR hNR hu hut.le
  · exact hs

theorem physical_correlation_hasDerivAt (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    {t s : ℝ} (hs : 0 < s) (hst : s < t) :
    HasDerivAt (physicalCorrelation (N := N) (p := p) β R hR t)
      (physicalResponse (p := p) hN β R hR hNR t s -
        annealedCurrent (N := N) (p := p) β R hR t s) s :=
  (physical_correlation_hasDerivWithinAt hN hp β R hR hNR hs.le hst).hasDerivAt (Ici_mem_nhds hs)

theorem physical_pointwise_fdt_square_bound (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (physicalResponse (p := p) hN β R hR hNR t s -
      derivWithin (physicalCorrelation (N := N) (p := p) β R hR t) (Ici 0) s)^2 ≤
      annealedFisher (N := N) (p := p) β (forwardDensity β R hR) s := by
  rw [(physical_correlation_hasDerivWithinAt hN hp β R hR hNR hs hst).derivWithin (uniqueDiffOn_Ici (0 : ℝ) s hs), sub_sub_cancel]
  exact actual_annealed_current_square_le_fisher hN hp β R hR hNR hs

theorem physical_integrated_fdt_square_bound (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 - physicalCorrelation (N := N) (p := p) β R hR t s -
      (∫u in s..t, physicalResponse (p := p) hN β R hR hNR t u))^2 ≤
      (t-s)*(∫u in s..t, annealedFisher (N := N) (p := p) β
        (forwardDensity β R hR) u) := by
  rw [physicalCorrelation_eq_density hN (by omega) β R hR hNR hs hst]
  have he : (∫u in s..t, physicalResponse (p := p) hN β R hR hNR t u) =
      ∫u in s..t, annealedResponse (N := N) (p := p) β R hR t u := by
    apply intervalIntegral.integral_congr_ae
    apply ae_of_all
    intro u hu
    rw [uIoc_of_le hst] at hu
    exact physicalResponse_eq_density hN hp β R hR hNR (hs.trans hu.1.le) hu.2
  rw [he]
  exact actual_literal_annealed_integrated_fdt_square_bound hN hp β R hR hNR hs hst

theorem physical_response_diagonal (hN : 0 < N) (β R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2) (t : ℝ) :
    physicalResponse (p := p) hN β R hR hNR t t = ((N : ℝ)-1)/(N : ℝ) := by
  simpa only [physicalResponse,physicalWaiting,min_self,HardSphereDynamics.kappa] using
    ActualResponseKernel.annealedResponse_diagonal (p := p) hN β R hR hNR t.toNNReal

theorem actual_source5_2_physical (hN : 2 ≤ N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2) :
    (∀t s : ℝ, 0 ≤ s → s < t → ∀J : Disorder N p,
      HasDerivWithinAt (physicalQuenchedCorrelation β R hR J t)
        (physicalQuenchedResponse (by omega : 0<N) β R hR hNR J t s -
          ActualSphereCurrent.current β R hR J t s) (Ici 0) s ∧
      physicalQuenchedResponse (by omega : 0<N) β R hR hNR J t s -
        derivWithin (physicalQuenchedCorrelation β R hR J t) (Ici 0) s =
        (∫x : State N, forwardDensity β R hR J s x *
          ⟪realMean β R hR J (t-s) x,
            tangentScore β J (forwardDensity β R hR J s) x⟫_ℝ ∂sphereLaw N)/(N : ℝ)) ∧
    (∀t s : ℝ, 0 ≤ s → s < t →
      HasDerivWithinAt (physicalCorrelation (N := N) (p := p) β R hR t)
        (physicalResponse (p := p) (by omega : 0<N) β R hR hNR t s -
          annealedCurrent (N := N) (p := p) β R hR t s) (Ici 0) s) ∧
    (∀t s : ℝ, 0 ≤ s → s < t →
      (physicalResponse (p := p) (by omega : 0<N) β R hR hNR t s -
        derivWithin (physicalCorrelation (N := N) (p := p) β R hR t) (Ici 0) s)^2 ≤
          annealedFisher (N := N) (p := p) β (forwardDensity β R hR) s) ∧
    (∀t s : ℝ, 0 ≤ s → s ≤ t →
      (1-physicalCorrelation (N := N) (p := p) β R hR t s-
        (∫u in s..t,physicalResponse (p := p) (by omega : 0<N) β R hR hNR t u))^2 ≤
        (t-s)*(∫u in s..t,annealedFisher (N := N) (p := p) β (forwardDensity β R hR) u)) ∧
    (∀t : ℝ, physicalResponse (p := p) (by omega : 0<N) β R hR hNR t t=
      ((N : ℝ)-1)/(N : ℝ)) := by
  have hN0 : 0<N := by omega
  exact ⟨fun _ _ hs hst J =>
      ⟨physical_quenched_correlation_hasDerivWithinAt hN0 (by omega) β R hR hNR J hs hst,
        physical_quenched_fdt_current hN0 (by omega) β R hR hNR J hs hst⟩,
    fun _ _ hs hst => physical_correlation_hasDerivWithinAt hN0 hp β R hR hNR hs hst,
    fun _ _ hs hst => physical_pointwise_fdt_square_bound hN0 hp β R hR hNR hs hst,
    fun _ _ hs hst => physical_integrated_fdt_square_bound hN0 hp β R hR hNR hs hst,
    physical_response_diagonal hN0 β R hR hNR⟩

end SphericalAging.ActualLiteralFiniteFDTTheorem
