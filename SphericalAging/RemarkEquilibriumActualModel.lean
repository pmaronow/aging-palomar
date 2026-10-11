module

public import SphericalAging.ActualEquilibriumPhysicalResponseStationarity

public section

/-! Complete actual-model mathematical content of Remark 3.1.
Full Gibbs-law invariance, literal two-time correlation and physical
response stationarity, finite-dimensional diagonal normalization, and
one-sided force-normalized FDT are collected with no equilibrium input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace
namespace SphericalAging.RemarkEquilibriumActualModel
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMeanSpatialInterface
open ActualEquilibriumGibbsStationaryLaw ActualEquilibriumTwoTimeStationarity
open ActualEquilibriumPhysicalResponseStationarity ActualEquilibriumFDT
open ActualSphereDensityResponse ActualExpectedTwoTimeResponse TwoTimeResponseParameter
variable {N p : ℕ}

@[expose] def physicalGibbsTrace (hN : N≠0) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s u : ℝ≥0) (x : State N) : ℝ := by
  classical
  exact if hx : OnSphere x then
    TwoTimeResponseTrace.normalizedTrace (physicalMatrix hN (VectorBrownian.driver N)
      β R hR hNR s (u+1) u (J,x) hx) else 0

/-- The actual physical response trace really is Gibbs-integrable. This
follows from the genuine restarted derivative identity and product-law
Fubini, rather than a separate response measurability or moment input. -/
theorem physicalGibbsTrace_integrable (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (s u : ℝ≥0) :
    Integrable (physicalGibbsTrace (Nat.ne_of_gt hN) β R hR hNR J s u) (gibbsLaw β J) := by
  classical
  letI := gibbsLaw_probability hN hp β J
  let f : State N→ℝ := tangentMeanTrace β R hR J u
  have hf : Continuous f := tangentMeanTrace_continuous β R hR J u
  have hi : Integrable f (gibbsWaitingLaw β R hR J s) := by
    rw [actual_gibbs_law_stationary hN hp β R hR hNR J s]
    exact gibbs_continuous_observable_integrable hN hp β J hf
  have hm := terminal_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s
  have hip : Integrable (fun z : State N×VectorBrownian.Space N=>
      f (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) s z.2))
      ((gibbsLaw β J).prod (VectorBrownian.law N)) := hi.comp_measurable hm
  apply (hip.integral_prod_left.div_const (N:ℝ)).congr
  filter_upwards [gibbsLaw_sphere_support hN β J] with x hx
  rw [physicalGibbsTrace,dif_pos hx]
  symm
  rw [normalizedTrace_eq_joint_mean_derivative (Nat.ne_of_gt hN)
    β R hR hNR s (u+1) u (le_add_right le_rfl) (by positivity) (J,x) hx]
  have he : realMean β R hR J (u:ℝ)=
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u := by
    funext y
    simp only [realMean,Real.toNNReal_coe]
  simp only [f,tangentMeanTrace,he]

structure Conclusions (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) : Prop where
  law_stationary : ∀t,gibbsWaitingLaw β R hR J t=gibbsLaw β J
  correlation_stationary : ∀s u,equilibriumTwoTimeCorrelation β R hR J (s+u) s=
    equilibriumCorrelation β R hR J u
  response_stationary : ∀s u,equilibriumTwoTimePhysicalResponse (Nat.ne_of_gt hN)
    β R hR hNR J s u=equilibriumResponse β R hR J u
  trace_integrable : ∀s u,Integrable (physicalGibbsTrace (Nat.ne_of_gt hN)
    β R hR hNR J s u) (gibbsLaw β J)
  correlation_diagonal : ∀s,equilibriumTwoTimeCorrelation β R hR J s s=1
  response_diagonal : ∀s,equilibriumTwoTimePhysicalResponse (Nat.ne_of_gt hN)
    β R hR hNR J s 0=((N:ℝ)-1)/(N:ℝ)
  fdt : ∀s,∀u : ℝ,0≤u→
    HasDerivWithinAt (fun v : ℝ=>equilibriumTwoTimeCorrelation β R hR J (s+v.toNNReal) s)
      (-equilibriumTwoTimePhysicalResponse (Nat.ne_of_gt hN) β R hR hNR J s u.toNNReal)
      (Ici 0) u

theorem actual_source3_1 (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) :
    Conclusions hN β R hR hNR J :=
  ⟨actual_gibbs_law_stationary hN hp β R hR hNR J,
    actual_equilibrium_two_time_lag hN hp β R hR hNR J,
    actual_equilibrium_physical_response_stationary hN hp β R hR hNR J,
    physicalGibbsTrace_integrable hN hp β R hR hNR J,
    actual_equilibrium_two_time_diagonal hN hp β R hR hNR J,
    actual_equilibrium_physical_response_diagonal hN hp β R hR hNR J,
    fun s u hu=>actual_equilibrium_two_time_fdt hN hp β R hR hNR J s hu⟩

end SphericalAging.RemarkEquilibriumActualModel
