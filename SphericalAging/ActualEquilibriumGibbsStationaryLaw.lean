module

public import SphericalAging.ActualEquilibriumGibbsInvariance
public import SphericalAging.SphereSmoothTestMeasureExt
public import SphericalAging.ActualSphereUniformInitialLaw

public section

/-! Full Gibbs-law invariance for the literal actual spherical diffusion.
The Gibbs probability measure and its actual Brownian terminal law are
constructed. Compact C² stationarity and the genuine smooth-test measure
characterisation identify the entire laws; no invariant-law input remains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualEquilibriumGibbsStationaryLaw
open FiniteModel HardSphereDynamics SphereInitialLaw SphereGibbsEntropy SphereGibbsGenerator
open ActualSphereTransition ActualSphereCompactSemigroup ActualEquilibriumGibbsInvariance
open SphereSmoothTestMeasureExt ActualSphereUniformInitialLaw SphericalIntegrationByParts
open ActualSphereKernelSupport
variable {N p : ℕ}

/-- The normalized Gibbs law of the genuine spherical Hamiltonian. -/
@[expose] def gibbsLaw (β : ℝ≥0) (J : Disorder N p) : Measure (State N) :=
  (sphereLaw N).withDensity (fun x => ENNReal.ofReal (gibbsDensity N p β J x))

theorem gibbsLaw_probability (hN : 0<N) (hp : 1≤p) (β : ℝ≥0) (J : Disorder N p) :
    IsProbabilityMeasure (gibbsLaw β J) := by
  constructor
  rw [gibbsLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal
      (continuous_sphere_integrable hN (gibbsDensity_contDiff β J).continuous)
      (.of_forall (fun x => (gibbsDensity_positive hN hp β.coe_nonneg J x).le)),
    gibbsDensity_normalized hN hp β.coe_nonneg J]
  simp

theorem gibbsLaw_sphere_support (hN : 0<N) (β : ℝ≥0) (J : Disorder N p) :
    ∀ᵐx∂gibbsLaw β J,OnSphere x := by
  apply (withDensity_absolutelyContinuous (sphereLaw N) _).ae_le
  exact (sphereLaw_support hN).mono (fun x hx => (onSphere_iff_norm_sq x).mpr hx)

theorem gibbsLaw_test_integral (hN : 0<N) (hp : 1≤p) (β : ℝ≥0)
    (J : Disorder N p) (f : State N→ℝ) :
    (∫x,f x ∂gibbsLaw β J)=∫x,gibbsDensity N p β J x*f x ∂sphereLaw N := by
  rw [gibbsLaw,integral_withDensity_eq_integral_toReal_smul
    ((gibbsDensity_contDiff β J).continuous.measurable.ennreal_ofReal)
    (.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact .of_forall (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (gibbsDensity_positive hN hp β.coe_nonneg J x).le,smul_eq_mul])

/-- The terminal law of the genuine SDE started from independent Gibbs
initial data and the actual Wiener driver. -/
@[expose] def gibbsWaitingLaw (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (t : ℝ≥0) : Measure (State N) :=
  ((gibbsLaw β J).prod (VectorBrownian.law N)).map
    (fun z : State N×VectorBrownian.Space N =>
      jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) t z.2)

theorem gibbsWaitingLaw_probability (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ≥0) :
    IsProbabilityMeasure (gibbsWaitingLaw β R hR J t) := by
  letI := gibbsLaw_probability hN hp β J
  unfold gibbsWaitingLaw
  infer_instance

theorem gibbsWaitingLaw_sphere_support (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) :
    ∀ᵐx∂gibbsWaitingLaw β R hR J t,OnSphere x := by
  rw [gibbsWaitingLaw]
  apply (ae_map_iff (terminal_measurable _ β R hR J t).aemeasurable
    measurableSet_onSphere).2
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_onSphere.preimage (terminal_measurable _ β R hR J t))).2
  filter_upwards [gibbsLaw_sphere_support hN β J] with x hx
  exact (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N)
    β R hR hNR J x hx).mono (fun ω hω => hω t)

theorem gibbsWaitingLaw_compact_test_integral (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f : State N→ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    (∫y,f y ∂gibbsWaitingLaw β R hR J t)=
      ∫x : State N,gibbsDensity N p β J x*realTransition β R hR J f t x ∂sphereLaw N := by
  letI := gibbsLaw_probability hN hp β J
  have hm := terminal_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t
  obtain ⟨C,hC⟩ := hfc.exists_bound_of_continuous hf
  have hi : Integrable (fun z : State N×VectorBrownian.Space N =>
      f (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) t z.2))
        ((gibbsLaw β J).prod (VectorBrownian.law N)) :=
    Integrable.of_bound (hf.stronglyMeasurable.comp_measurable hm).aestronglyMeasurable C
      (.of_forall (fun z => hC _))
  rw [gibbsWaitingLaw,integral_map hm.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
    integral_prod _ hi]
  rw [gibbsLaw_test_integral hN hp β J]
  simp only [realTransition,Real.toNNReal_coe,transition]

/-- Full equality of probability laws: the actual sphere SDE preserves
its genuine normalized Gibbs measure at every nonnegative time. -/
theorem actual_gibbs_law_stationary (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) :
    gibbsWaitingLaw β R hR J t=gibbsLaw β J := by
  letI := gibbsLaw_probability hN hp β J
  letI := gibbsWaitingLaw_probability hN hp β R hR J t
  apply measure_eq_of_compactC2_integrals
    (gibbsWaitingLaw_sphere_support hN β R hR hNR J t) (gibbsLaw_sphere_support hN β J)
  intro f hf hfc
  rw [gibbsWaitingLaw_compact_test_integral hN hp β R hR J hf.continuous hfc t,
    gibbsLaw_test_integral hN hp β J f]
  exact compact_gibbs_transition_stationary hN hp β R hR hNR J hf hfc t

/-- Stationarity against arbitrary scalar observables follows from the
literal equality of laws, with no extra smooth-test restriction. -/
theorem actual_gibbs_observable_stationary (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0)
    (f : State N→ℝ) :
    (∫x,f x ∂gibbsWaitingLaw β R hR J t)=∫x,f x ∂gibbsLaw β J := by
  rw [actual_gibbs_law_stationary hN hp β R hR hNR J t]

end SphericalAging.ActualEquilibriumGibbsStationaryLaw
