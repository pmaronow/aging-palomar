module

public import SphericalAging.ActualEquilibriumGibbsStationaryLaw
public import SphericalAging.ActualSphereMeanConditionalPairing

public section

/-! Literal two-time equilibrium stationarity for the actual sphere SDE.
The initial law is the proved normalized Gibbs measure. Its full-law
invariance and the genuine conditional Markov pairing reduce the actual
two-time Brownian correlation to the equilibrium lag correlation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace
namespace SphericalAging.ActualEquilibriumTwoTimeStationarity
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMeanSpatialInterface
open ActualEquilibriumGibbsStationaryLaw ActualSphereMeanConditionalPairing
open ActualEquilibriumFDT ActualEquilibriumResponseNormalization SphereGibbsGenerator SphereInitialLaw
variable {N p : ℕ}

/-- The actual two-time Brownian correlation, with independent Gibbs
initial state and genuine Wiener noise, in the manuscript's normalization. -/
@[expose] def equilibriumTwoTimeCorrelation (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (t s : ℝ≥0) : ℝ :=
  (∫x : State N,∫ω : VectorBrownian.Space N,
    ⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω,
      jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t ω⟫_ℝ
      ∂VectorBrownian.law N ∂gibbsLaw β J)/(N:ℝ)

/-- Every measurable Gibbs-integrable observable has the same expected
value after the literal SDE evolution. The iterated integral is justified
by its true product-law integrability. -/
theorem actual_gibbs_expected_observable_stationary (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (t : ℝ≥0) (f : State N→ℝ)
    (hf : StronglyMeasurable f) (hi : Integrable f (gibbsLaw β J)) :
    (∫x : State N,∫ω : VectorBrownian.Space N,
      f (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t ω)
        ∂VectorBrownian.law N ∂gibbsLaw β J)=∫x,f x ∂gibbsLaw β J := by
  letI := gibbsLaw_probability hN hp β J
  have hm := terminal_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t
  have hi' : Integrable f (gibbsWaitingLaw β R hR J t) := by
    rw [actual_gibbs_law_stationary hN hp β R hR hNR J t]
    exact hi
  have hip : Integrable (fun z : State N×VectorBrownian.Space N =>
      f (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) t z.2))
      ((gibbsLaw β J).prod (VectorBrownian.law N)) :=
    hi'.comp_measurable hm
  rw [←integral_prod _ hip,←integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact actual_gibbs_observable_stationary hN hp β R hR hNR J t f

theorem gibbs_mean_pairing_integrable (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (u : ℝ≥0) :
    Integrable (fun x : State N=>⟪x,realMean β R hR J (u:ℝ) x⟫_ℝ) (gibbsLaw β J) := by
  letI := gibbsLaw_probability hN hp β J
  have hf : Continuous (fun x : State N=>⟪x,realMean β R hR J (u:ℝ) x⟫_ℝ) :=
    continuous_id.inner (realMean_spatial_contDiff β R hR J (u:ℝ)).continuous
  apply Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable ((R:ℝ)^2)
  filter_upwards [gibbsLaw_sphere_support hN β J] with x hx
  have hxR := sphere_norm_le_radius R hNR hx
  have hsqr := mean_norm_sq_le (Nat.ne_of_gt hN) (VectorBrownian.driver N)
    β R hR hNR J u x hx
  have hmR : ‖realMean β R hR J (u:ℝ) x‖≤R := by
    simp only [realMean,Real.toNNReal_coe]
    nlinarith [norm_nonneg (mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J u x),R.coe_nonneg]
  exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans
    (by simpa only [pow_two] using mul_le_mul hxR hmR (norm_nonneg _) R.coe_nonneg)

/-- The literal actual two-time correlation depends only on elapsed time.
Both the Markov pairing and Gibbs stationarity are derived from the actual
SDE, rather than supplied as equilibrium assumptions. -/
theorem actual_equilibrium_two_time_lag (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s u : ℝ≥0) :
    equilibriumTwoTimeCorrelation β R hR J (s+u) s=equilibriumCorrelation β R hR J u := by
  rw [equilibriumTwoTimeCorrelation,equilibriumCorrelation_eq_inner hN β R hR J]
  congr 1
  let f : State N→ℝ := fun x=>⟪x,realMean β R hR J (u:ℝ) x⟫_ℝ
  have hf : Continuous f :=
    continuous_id.inner (realMean_spatial_contDiff β R hR J (u:ℝ)).continuous
  calc
    _=(∫x : State N,∫ω : VectorBrownian.Space N,
        f (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω)
          ∂VectorBrownian.law N ∂gibbsLaw β J) := by
      apply integral_congr_ae
      filter_upwards [gibbsLaw_sphere_support hN β J] with x hx
      simpa only [f,realMean,Real.toNNReal_coe] using
        mean_waiting_inner_identity (Nat.ne_of_gt hN) β R hR hNR J x hx s u
    _=(∫x,f x ∂gibbsLaw β J) :=
      actual_gibbs_expected_observable_stationary hN hp β R hR hNR J s f
        hf.stronglyMeasurable (gibbs_mean_pairing_integrable hN hp β R hR hNR J u)
    _=_ := gibbsLaw_test_integral hN hp β J f

theorem actual_equilibrium_two_time_stationary (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (t s : ℝ≥0) (hst : s≤t) :
    equilibriumTwoTimeCorrelation β R hR J t s=
      equilibriumCorrelation β R hR J (t-s) := by
  have hh := actual_equilibrium_two_time_lag hN hp β R hR hNR J s (t-s)
  simpa only [add_tsub_cancel_of_le hst,NNReal.coe_sub hst] using hh

theorem actual_equilibrium_two_time_diagonal (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s : ℝ≥0) :
    equilibriumTwoTimeCorrelation β R hR J s s=1 := by
  simpa only [add_zero,NNReal.coe_zero,equilibriumCorrelation_zero hN hp β R hR J] using
    actual_equilibrium_two_time_lag hN hp β R hR hNR J s 0

end SphericalAging.ActualEquilibriumTwoTimeStationarity
