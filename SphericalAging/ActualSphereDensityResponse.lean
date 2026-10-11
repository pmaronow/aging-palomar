module

public import SphericalAging.ActualSphereOnlyFDT
public import SphericalAging.ActualSphereForwardDensityLaw
public import SphericalAging.ActualResponseJointEnvelope

public section

/-! The rotation-generator response of the constructed forward density is
the literal projected SDE response. The equality uses the actual waiting
law and expected restarted derivative, with genuine Fubini integrability. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereDensityResponse
open FiniteModel HardSphereDynamics SphereInitialLaw SphericalIntegrationByParts
open SphereRotationGeometry SphereGeneratorIntegrationByParts SphereCoordinateScore SphereQuenchedFDT
open ActualSphereTransition ActualSphereMeanSpatialInterface ActualSphereGibbsDensity
open ActualSphereUniformInitialLaw ActualSphereForwardDensityLaw ActualSphereOnlyFDT
open ActualResponseJointKernel ActualResponseJointEnvelope ActualAnnealedCorrelationIntegral
open ActualSphereKernelSupport AnnealedResponseMatrixContraction
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem canonicalGamma_coordinate_mean (hN : 0<N) {m : State N→State N}
    (hm : Differentiable ℝ m) (x : State N) (hx : OnSphere x) (i : Fin N) :
    rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N) (coordinateObservable i) (fun y => m y i) x=
      ⟪basisVector i,fderiv ℝ m x (projection x (basisVector i))⟫_ℝ := by
  rw [SphereCarreDuChamp.canonical_rotationGamma hN _ _ x hx,coordinateObservable_gradient,
    ←projection_self_adjoint,projection_idempotent (Nat.ne_of_gt hN) x _ hx,real_inner_comm,
    inner_gradient_left]
  have hd := ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).hasFDerivAt.comp x (hm x).hasFDerivAt).fderiv
  simp only [Function.comp_def,PiLp.proj_apply] at hd
  rw [hd]
  simpa only [ContinuousLinearMap.comp_apply,PiLp.proj_apply] using
    (show (fderiv ℝ m x (projection x (basisVector i))) i=
      ⟪basisVector i,fderiv ℝ m x (projection x (basisVector i))⟫_ℝ from by rw [real_inner_comm,basis_inner])

@[expose] def tangentMeanTrace (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (τ : ℝ) (x : State N) : ℝ :=
  ∑i : Fin N,⟪basisVector i,fderiv ℝ (realMean β R hR J τ) x (projection x (basisVector i))⟫_ℝ

theorem tangentMeanTrace_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (τ : ℝ) : Continuous (tangentMeanTrace β R hR J τ) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.inner
    (((realMean_spatial_contDiff β R hR J τ).continuous_fderiv (by norm_num)).clm_apply
      (by unfold projection;fun_prop))

theorem uniformWaiting_continuous_test_integrable (hN : 0<N)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (s : ℝ≥0) {f : State N→ℝ} (hf : Continuous f) :
    Integrable (fun z : State N×VectorBrownian.Space N =>
      f (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) s z.2))
      ((sphereLaw N).prod (VectorBrownian.law N)) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:State N) (Real.sqrt N)).bddAbove_image hf.norm.continuousOn
  have hm := hf.stronglyMeasurable.comp_measurable
    (terminal_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s)
  apply Integrable.of_bound hm.aestronglyMeasurable C
  have hall : ∀ᵐz ∂(sphereLaw N).prod (VectorBrownian.law N),OnSphere
      (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) s z.2) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_onSphere.preimage (terminal_measurable _ β R hR J s))).mpr
    filter_upwards [sphereLaw_support hN] with x hx
    exact (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x
      ((onSphere_iff_norm_sq x).mpr hx)).mono (fun ω hω => hω s)
  filter_upwards [hall] with z hz
  apply hC
  refine ⟨_,?_,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (((onSphere_iff_norm_sq _).mp hz).trans (Real.sq_sqrt (Nat.cast_nonneg N)).symm) |>.le

theorem densityResponse_eq_tangentMeanTrace (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t s : ℝ) :
    SphereQuenchedFDT.quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s=
      (∫x : State N,forwardDensity β R hR J s x*tangentMeanTrace β R hR J (t-s) x ∂sphereLaw N)/(N:ℝ) := by
  classical
  have hρs : Continuous (forwardDensity β R hR J s) :=
    (forwardDensity_spatial_contDiff hN hp β R hR J s).continuous
  have hi (i : Fin N) : Integrable (fun x : State N => forwardDensity β R hR J s x*
      rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N) (coordinateObservable i)
        (fun y => realMean β R hR J (t-s) y i) x) (sphereLaw N) :=
    continuous_sphere_integrable hN (hρs.mul (SphereFDTAlgebra.rotationGamma_continuous
      _ _ ((coordinateObservable_contDiff i).of_le (by simp))
      ((ActualSphereMeanSpatialInterface.realMean_coordinate_spatial_contDiff β R hR J i (t-s)).of_le
        (by norm_num))))
  unfold SphereQuenchedFDT.quenchedResponse
  rw [←integral_finsetSum Finset.univ (fun i _ => hi i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hxS := (onSphere_iff_norm_sq x).mpr hx
  simp_rw [canonicalGamma_coordinate_mean hN
    ((realMean_spatial_contDiff β R hR J (t-s)).differentiable (by norm_num)) x hxS]
  unfold tangentMeanTrace
  rw [Finset.mul_sum]

theorem densityResponse_eq_uniform_initial (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (H s : ℝ≥0) :
    SphereQuenchedFDT.quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H s=
      (∫z : State N×VectorBrownian.Space N,tangentMeanTrace β R hR J ((H:ℝ)-(s:ℝ))
        (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) s z.2)
        ∂(sphereLaw N).prod (VectorBrownian.law N))/(N:ℝ) := by
  rw [densityResponse_eq_tangentMeanTrace hN hp β R hR J,
    ←densityLaw_test_integral hN hp β R hR hNR J s,
    ←waitingLaw_eq_densityLaw hN hp β R hR hNR J s,waitingLaw,
    integral_map (terminal_measurable _ β R hR J s).aemeasurable
      (tangentMeanTrace_continuous β R hR J ((H:ℝ)-(s:ℝ))).aestronglyMeasurable]

theorem densityResponse_annealed_eq_responseMeanPair (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H s : ℝ≥0) (hs : s≤H) :
    (∫J : Disorder N p,SphereQuenchedFDT.quenchedResponse (forwardDensity β R hR J)
      (realMean β R hR J) H s ∂disorderLaw N p)=responseMeanPair (N:=N) (p:=p) β R hR H s := by
  have hN0 : 0<N := by omega
  have he (J : Disorder N p) :
      SphereQuenchedFDT.quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H s=
      ∫x : State N,∫ω : VectorBrownian.Space N,backwardTraceField β R hR ((H,s),((J,x),ω))
        ∂VectorBrownian.law N ∂sphereLaw N := by
    have hrm : realMean β R hR J ((H-s:ℝ≥0):ℝ)=
        mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (H-s) := by
      funext y
      simp only [ActualSphereMeanSpatialInterface.realMean,Real.toNNReal_coe]
    rw [densityResponse_eq_uniform_initial hN0 (by omega) β R hR hNR J H s,
      integral_prod _ (uniformWaiting_continuous_test_integrable hN0 β R hR hNR J s
        (tangentMeanTrace_continuous β R hR J ((H:ℝ)-(s:ℝ)))),←integral_div]
    apply integral_congr_ae
    exact .of_forall (fun x => by
      dsimp only
      rw [←integral_div]
      apply integral_congr_ae
      exact .of_forall (fun ω => by
        simp only [tangentMeanTrace,←NNReal.coe_sub hs,backwardTraceField,trajectory]
        rw [hrm]))
  simp_rw [he]
  have hi := backwardTraceField_integrable hN hp β R hR hNR H s
  unfold responseMeanPair AnnealedModelLaw.law AnnealedModelLaw.parameterLaw at *
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]

theorem densityResponse_annealed_eq_physicalResponse (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H : ℝ≥0) (s : TwoTimeResponseTimeParameter.WaitingTime H) :
    (∫J : Disorder N p,SphereQuenchedFDT.quenchedResponse (forwardDensity β R hR J)
      (realMean β R hR J) H (s:ℝ≥0) ∂disorderLaw N p)=
      ActualResponseKernel.annealedResponse (p:=p) (by omega : N≠0) β R hR hNR H s := by
  rw [densityResponse_annealed_eq_responseMeanPair hN hp β R hR hNR H s s.property.2]
  exact responseMeanPair_eq_annealedResponse hN hp β R hR hNR H s

end SphericalAging.ActualSphereDensityResponse
