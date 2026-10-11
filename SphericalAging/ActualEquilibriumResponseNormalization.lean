module

public import SphericalAging.ActualEquilibriumFDT
public import SphericalAging.ActualSphereIntegratedFDT
public import Mathlib.Analysis.Calculus.FDeriv.Extend

public section

/-! The actual Gibbs equilibrium force response is the mean projected
Jacobian trace, with exact finite-N diagonal (N−1)/N. This completes the
normalization and endpoint calculus of manuscript Remark 3.1. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualEquilibriumResponseNormalization
open FiniteModel HardSphereDynamics SphereInitialLaw SphereGibbsEntropy
  ActualEquilibriumFDT ActualSphereMeanSpatialInterface SphereGeneratorIntegrationByParts
  SphereCoordinateScore SphereQuenchedFDT SphereGibbsGenerator ActualSphereMeanDerivative
  ActualExpectedTwoTimeResponse LandscapeDerivatives HamiltonianTerminalDerivative
  SphereEntropyBudget SphericalIntegrationByParts
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

 theorem coordinate_mean_gamma_eq_projected_derivative (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ) (x : State N) (hx : OnSphere x) (i : Fin N) :
    rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N) (coordinateObservable i)
      (fun y => realMean β R hR J τ y i) x=
        ⟪basisVector i,fderiv ℝ (realMean β R hR J τ) x (projection x (basisVector i))⟫_ℝ := by
  rw [SphereCarreDuChamp.canonical_rotationGamma hN _ _ x hx,coordinateObservable_gradient,
    ←projection_self_adjoint x (projection x (basisVector i)),
    projection_idempotent (Nat.ne_of_gt hN) x (basisVector i) hx,inner_gradient_right]
  simp only [conj_trivial]
  have hd := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).hasFDerivAt.comp x
    ((realMean_spatial_contDiff β R hR J τ).differentiable (by norm_num) x).hasFDerivAt
  change HasFDerivAt (fun y => realMean β R hR J τ y i)
    ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).comp (fderiv ℝ (realMean β R hR J τ) x)) x at hd
  rw [hd.fderiv,real_inner_comm,basis_inner]
  rfl

 /-- The printed sphere-gradient response is exactly the projected mean trace. -/
 theorem equilibriumResponse_eq_projected_mean_trace (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ) :
    equilibriumResponse β R hR J τ=
      (∑i : Fin N,∫x : State N,gibbsDensity N p β J x*
        ⟪basisVector i,fderiv ℝ (realMean β R hR J τ) x (projection x (basisVector i))⟫_ℝ
          ∂sphereLaw N)/(N:ℝ) := by
  unfold equilibriumResponse SphereQuenchedFDT.quenchedResponse
  simp only [sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [SphereOnlyParameterIntegral.physicalSphere_ae hN] with x hx
  rw [coordinate_mean_gamma_eq_projected_derivative hN β R hR J τ x hx i]

@[expose]  def equilibriumPhysicalTrace (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ≥0) : ℝ :=
  ∫x : State N,gibbsDensity N p β J x*TwoTimeResponseTrace.normalizedTrace
    ((stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR x (τ+1) τ).comp
      (tangentProjection x)) ∂sphereLaw N

 /-- Genuine expectation/initial-state differentiation identifies this
response with the normalized trace of the actual projected Jacobian SDE. -/
 theorem equilibriumResponse_eq_expected_physical_trace (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ≥0) :
    equilibriumResponse β R hR J τ=equilibriumPhysicalTrace β R hR J τ := by
  rw [equilibriumResponse_eq_projected_mean_trace hN β R hR J]
  unfold equilibriumPhysicalTrace
  simp_rw [normalizedTrace_eq_sum_expected,ContinuousLinearMap.comp_apply,tangentProjection_apply]
  have he (x v : State N) :
      expectationOperator (stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR x (τ+1) τ v)=
        fderiv ℝ (realMean β R hR J τ) x v := by
    unfold realMean
    rw [Real.toNNReal_coe,expectationOperator_apply]
    exact (fderiv_mean_eq_expected_response (VectorBrownian.driver N) β J R hR x v (τ+1) τ
        (le_add_right le_rfl) (by positivity)).symm
  simp_rw [he]
  have hi (i : Fin N) : Integrable (fun x : State N => gibbsDensity N p β J x*
      ⟪basisVector i,fderiv ℝ (realMean β R hR J τ) x (projection x (basisVector i))⟫_ℝ) (sphereLaw N) := by
    apply continuous_sphere_integrable hN
    have hD : Continuous (fun x : State N => fderiv ℝ (realMean β R hR J τ) x) := by
      unfold realMean
      simp only [Real.toNNReal_coe]
      exact (ActualSphereMeanJointSpatialContinuity.mean_fderiv_joint_continuous
        (VectorBrownian.driver N) β J R hR).comp (continuous_const.prodMk continuous_id)
    have hP : Continuous (fun x : State N => projection x (basisVector i)) := by unfold projection;fun_prop
    exact (gibbsDensity_contDiff β J).continuous.mul
      (continuous_const.inner (hD.clm_apply hP))
  have hefun : (fun x : State N => gibbsDensity N p β J x*
      ((∑i : Fin N,⟪basisVector i,fderiv ℝ (realMean β R hR J τ) x (projection x (basisVector i))⟫_ℝ)/(N:ℝ)))=
        fun x => (∑i : Fin N,gibbsDensity N p β J x*
          ⟪basisVector i,fderiv ℝ (realMean β R hR J τ) x (projection x (basisVector i))⟫_ℝ)/(N:ℝ) := by
    funext x
    rw [←Finset.mul_sum]
    ring
  rw [hefun,integral_div,integral_finsetSum Finset.univ (fun i _ => hi i)]

 theorem equilibriumCorrelation_continuous (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) : Continuous (equilibriumCorrelation β R hR J) := by
  change Continuous (fun τ => equilibriumCorrelation β R hR J τ)
  simp_rw [equilibriumCorrelation_eq_inner hN β R hR J]
  apply Continuous.div_const
  apply continuous_sphere_parameter_integral hN
  exact ((gibbsDensity_contDiff β J).continuous.comp continuous_snd).mul
    (continuous_snd.inner (realMean_joint_continuous β R hR J))

 theorem equilibriumResponse_continuous (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) : Continuous (equilibriumResponse β R hR J) := by
  classical
  unfold equilibriumResponse SphereQuenchedFDT.quenchedResponse
  simp only [sub_zero]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply continuous_sphere_parameter_integral hN
  apply ((gibbsDensity_contDiff β J).continuous.comp continuous_snd).mul
  unfold rotationGamma
  apply continuous_const.mul
  apply continuous_finsetSum
  intro ij _
  exact ((lieDerivative_continuous (canonicalRotations N ij)
    ((coordinateObservable_contDiff i).of_le (by simp))).comp continuous_snd).mul
      (SphereSpatialGeneratorRegularity.joint_lieDerivative_continuous (canonicalRotations N ij)
        (m:=fun τ x => realMean β R hR J τ x i)
        (realMean_coordinate_first_joint_continuous β R hR J i))

 /-- Including lag zero, the actual correlation has the exact right FDT derivative. -/
 theorem equilibrium_fdt_hasDerivWithinAt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {τ : ℝ} (hτ : 0≤τ) :
    HasDerivWithinAt (equilibriumCorrelation β R hR J) (-equilibriumResponse β R hR J τ) (Ici 0) τ := by
  rcases hτ.eq_or_lt with he|ht
  · subst τ
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s:=Ioi (0:ℝ)) (fun x hx => (equilibrium_fdt_hasDerivAt hN hp β R hR hNR J hx).differentiableAt.differentiableWithinAt)
      (equilibriumCorrelation_continuous hN β R hR J).continuousWithinAt self_mem_nhdsWithin
    have hl : Tendsto (fun x : ℝ => -equilibriumResponse β R hR J x) (𝓝[>] (0:ℝ))
        (𝓝 (-equilibriumResponse β R hR J 0)) :=
      (equilibriumResponse_continuous hN β R hR J).neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (equilibrium_fdt_hasDerivAt hN hp β R hR hNR J hx).deriv.symm
  · exact (equilibrium_fdt_hasDerivAt hN hp β R hR hNR J ht).hasDerivWithinAt

 theorem equilibriumResponse_zero (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) : equilibriumResponse β R hR J 0=((N:ℝ)-1)/(N:ℝ) := by
  rw [equilibriumResponse_eq_projected_mean_trace hN β R hR J]
  have hm : realMean β R hR J 0=id := funext (ActualSphereIntegratedFDT.actual_realMean_zero β R hR J)
  rw [hm]
  simp only [fderiv_id,ContinuousLinearMap.id_apply]
  have hi (i : Fin N) : Integrable (fun x : State N => gibbsDensity N p β J x*
      ⟪basisVector i,projection x (basisVector i)⟫_ℝ) (sphereLaw N) := by
    apply continuous_sphere_integrable hN
    exact (gibbsDensity_contDiff β J).continuous.mul
      (continuous_const.inner (by unfold projection;fun_prop))
  rw [←integral_finsetSum Finset.univ (fun i _ => hi i)]
  have he : (fun x : State N => ∑i : Fin N,gibbsDensity N p β J x*⟪basisVector i,projection x (basisVector i)⟫_ℝ)=ᵐ[sphereLaw N]
      fun x => gibbsDensity N p β J x*((N:ℝ)-1) := by
    filter_upwards [SphereOnlyParameterIntegral.physicalSphere_ae hN] with x hx
    rw [←Finset.mul_sum,TwoTimeResponseTrace.projection_basis_trace_onSphere (Nat.ne_of_gt hN) x hx]
  rw [integral_congr_ae he,integral_mul_const,gibbsDensity_normalized hN hp β.coe_nonneg J,one_mul]

 theorem equilibriumCorrelation_zero (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) : equilibriumCorrelation β R hR J 0=1 := by
  apply SphereIntegratedFDT.quenchedCorrelation_diagonal (ρ:=fun _ : ℝ => gibbsDensity N p β J) hN
    ((gibbsDensity_contDiff β J).continuous.comp continuous_snd)
    (realMean_joint_continuous β R hR J)
    (ActualSphereIntegratedFDT.actual_realMean_zero β R hR J) 0
  exact gibbsDensity_normalized hN hp β.coe_nonneg J

 theorem equilibrium_integrated_fdt (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {τ : ℝ} (hτ : 0≤τ) :
    (∫u in (0:ℝ)..τ,equilibriumResponse β R hR J u)=1-equilibriumCorrelation β R hR J τ := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ
    (equilibriumCorrelation_continuous hN β R hR J).continuousOn
      (fun u hu => equilibrium_fdt_hasDerivAt hN hp β R hR hNR J hu.1)
        ((equilibriumResponse_continuous hN β R hR J).neg.intervalIntegrable 0 τ)
  rw [intervalIntegral.integral_neg,equilibriumCorrelation_zero hN hp β R hR J] at hh
  linarith

 /-- The actual derivative column is linear in the applied tangent force. -/
 theorem projected_response_beta_force (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (τ : ℝ≥0) (x v : State N) :
    stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR x (τ+1) τ
      (projection x ((β:ℝ)•v))=(β:ℝ)•
        stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR x (τ+1) τ
          (projection x v) := by
  rw [projection_smul,map_smul]

end SphericalAging.ActualEquilibriumResponseNormalization
