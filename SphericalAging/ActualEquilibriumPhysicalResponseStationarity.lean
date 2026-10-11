module

public import SphericalAging.ActualEquilibriumTwoTimeStationarity
public import SphericalAging.ActualSphereDensityResponse

public section

/-! Literal equilibrium response stationarity and FDT. The response is
the normalized trace of the actual physical projected variational SDE,
averaged over the actual Gibbs initial law. Its expected restarted mean
trace, full Gibbs-law invariance, and the proved equilibrium FDT identify
the response and correlation at every waiting time, including lag zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace BigOperators
namespace SphericalAging.ActualEquilibriumPhysicalResponseStationarity
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMeanSpatialInterface
open ActualEquilibriumGibbsStationaryLaw ActualEquilibriumTwoTimeStationarity
open ActualEquilibriumFDT ActualEquilibriumResponseNormalization SphereInitialLaw
open ActualSphereDensityResponse ActualExpectedTwoTimeResponse TwoTimeResponseParameter
variable {N p : ℕ}

theorem gibbs_continuous_observable_integrable (hN : 0<N) (hp : 1≤p)
    (β : ℝ≥0) (J : Disorder N p) {f : State N→ℝ} (hf : Continuous f) :
    Integrable f (gibbsLaw β J) := by
  letI := gibbsLaw_probability hN hp β J
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:State N) (Real.sqrt N)).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable C
  filter_upwards [gibbsLaw_sphere_support hN β J] with x hx
  apply hC
  refine ⟨x,?_,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (((onSphere_iff_norm_sq _).mp hx).trans (Real.sq_sqrt (Nat.cast_nonneg N)).symm) |>.le

theorem equilibriumResponse_eq_gibbs_mean_trace (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (u : ℝ≥0) :
    equilibriumResponse β R hR J u=
      (∫x,tangentMeanTrace β R hR J u x ∂gibbsLaw β J)/(N:ℝ) := by
  classical
  have hi (i : Fin N) : Integrable (fun x : State N=>
      ⟪basisVector i,fderiv ℝ (realMean β R hR J u) x (projection x (basisVector i))⟫_ℝ)
      (gibbsLaw β J) := by
    apply gibbs_continuous_observable_integrable hN hp β J
    exact continuous_const.inner
      (((realMean_spatial_contDiff β R hR J u).continuous_fderiv (by norm_num)).clm_apply
        (by unfold projection;fun_prop))
  rw [equilibriumResponse_eq_projected_mean_trace hN β R hR J]
  simp only [tangentMeanTrace]
  rw [integral_finsetSum _ (fun i _=>hi i)]
  congr 1
  exact Finset.sum_congr rfl (fun i _=>(gibbsLaw_test_integral hN hp β J _).symm)

/-- Actual projected physical response after waiting time `s`, at elapsed
time `u`. The arbitrary extension away from the sphere has zero Gibbs law. -/
@[expose] def equilibriumTwoTimePhysicalResponse (hN : N≠0) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s u : ℝ≥0) : ℝ := by
  classical
  exact ∫x : State N,if hx : OnSphere x then
    TwoTimeResponseTrace.normalizedTrace (physicalMatrix hN (VectorBrownian.driver N)
      β R hR hNR s (u+1) u (J,x) hx) else 0 ∂gibbsLaw β J

/-- Gibbs averaging removes the waiting-time dependence of the genuine
physical projected response, by the actual restarted derivative identity. -/
theorem actual_equilibrium_physical_response_stationary (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (s u : ℝ≥0) :
    equilibriumTwoTimePhysicalResponse (Nat.ne_of_gt hN) β R hR hNR J s u=
      equilibriumResponse β R hR J u := by
  classical
  unfold equilibriumTwoTimePhysicalResponse
  calc
    _=(∫x : State N,(∫ω : VectorBrownian.Space N,
        tangentMeanTrace β R hR J u
          (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω)
            ∂VectorBrownian.law N)/(N:ℝ) ∂gibbsLaw β J) := by
      apply integral_congr_ae
      filter_upwards [gibbsLaw_sphere_support hN β J] with x hx
      rw [dif_pos hx,normalizedTrace_eq_joint_mean_derivative (Nat.ne_of_gt hN)
        β R hR hNR s (u+1) u (le_add_right le_rfl) (by positivity) (J,x) hx]
      have hm : realMean β R hR J (u:ℝ)=
          mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u := by
        funext y
        simp only [realMean,Real.toNNReal_coe]
      simp only [tangentMeanTrace,hm]
    _=(∫x : State N,∫ω : VectorBrownian.Space N,
        tangentMeanTrace β R hR J u
          (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω)
            ∂VectorBrownian.law N ∂gibbsLaw β J)/(N:ℝ) := integral_div _ _
    _=(∫x,tangentMeanTrace β R hR J u x ∂gibbsLaw β J)/(N:ℝ) := by
      rw [actual_gibbs_expected_observable_stationary hN hp β R hR hNR J s
        (tangentMeanTrace β R hR J u) (tangentMeanTrace_continuous β R hR J u).stronglyMeasurable
          (gibbs_continuous_observable_integrable hN hp β J
            (tangentMeanTrace_continuous β R hR J u))]
    _=equilibriumResponse β R hR J u := (equilibriumResponse_eq_gibbs_mean_trace hN hp β R hR J u).symm

theorem actual_equilibrium_physical_response_diagonal (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (s : ℝ≥0) :
    equilibriumTwoTimePhysicalResponse (Nat.ne_of_gt hN) β R hR hNR J s 0=((N:ℝ)-1)/(N:ℝ) := by
  rw [actual_equilibrium_physical_response_stationary hN hp β R hR hNR J s 0]
  exact equilibriumResponse_zero hN hp β R hR J

/-- The physical Gibbs two-time correlation obeys force-normalized FDT
at every waiting time, including the genuine one-sided lag-zero derivative. -/
theorem actual_equilibrium_two_time_fdt (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (s : ℝ≥0) {u : ℝ} (hu : 0≤u) :
    HasDerivWithinAt (fun v : ℝ=>equilibriumTwoTimeCorrelation β R hR J (s+v.toNNReal) s)
      (-equilibriumTwoTimePhysicalResponse (Nat.ne_of_gt hN) β R hR hNR J s u.toNNReal)
      (Ici 0) u := by
  rw [actual_equilibrium_physical_response_stationary hN hp β R hR hNR J,
    Real.coe_toNNReal _ hu]
  apply (equilibrium_fdt_hasDerivWithinAt hN hp β R hR hNR J hu).congr_of_mem
  · intro v hv
    rw [actual_equilibrium_two_time_lag hN hp β R hR hNR J,
      Real.coe_toNNReal _ hv]
  · exact hu

end SphericalAging.ActualEquilibriumPhysicalResponseStationarity
