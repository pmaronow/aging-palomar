module

public import SphericalAging.ActualSphereDensityResponse
public import SphericalAging.ActualForwardDensityMeasurability
public import SphericalAging.SphereResponseGradientBound
public import SphericalAging.SphereSharpMeanGradient

public section

/-! Actual density-response disorder/time measurability and finite-window
Fubini. The integrable Gaussian landscape envelope follows from the true
sharp tangent derivative of the SDE conditional mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereDensityResponseMoments
open FiniteModel HardSphereDynamics SphereInitialLaw SphericalIntegrationByParts SphereQuenchedFDT
open SphereCoordinateScore SphereGeneratorIntegrationByParts SphereFDTAlgebra
open ActualSphereTransition ActualSphereMeanSpatialInterface ActualSphereGibbsDensity
open ActualSphereDensityResponse ActualForwardDensityMeasurability ActualResponseJointKernel
open SphereResponseGradientBound SphereSharpMeanGradient GaussianLandscape GaussianLandscapeMoments
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem densityResponse_row_joint_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (H : ℝ) :
    StronglyMeasurable (fun z : Disorder N p×ℝ =>
      quenchedResponse (forwardDensity β R hR z.1) (realMean β R hR z.1) H z.2) := by
  have hDcomp : StronglyMeasurable ((fun q : ℝ≥0×(Disorder N p×State N) =>
      fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.2.1 q.1) q.2.2)∘
      (fun z : (Disorder N p×ℝ)×State N => ((H-z.1.2).toNNReal,(z.1.1,z.2)))) :=
    (mean_fderiv_time_parameter_stronglyMeasurable β R hR).comp_measurable (by fun_prop)
  have hD : StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N =>
      fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR z.1.1
        (H-z.1.2).toNNReal) z.2) := by simpa only [Function.comp_def] using hDcomp
  have htrace : StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N =>
      ∑i : Fin N,⟪basisVector i,fderiv ℝ
        (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR z.1.1 (H-z.1.2).toNNReal)
        z.2 (projection z.2 (basisVector i))⟫_ℝ) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    have hpj : Continuous (fun x : State N => projection x (basisVector i)) := by unfold projection;fun_prop
    exact stronglyMeasurable_const.inner ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hD.prodMk (hpj.stronglyMeasurable.comp_measurable measurable_snd)))
  have hi := ((forwardDensity_joint_stronglyMeasurable β R hR).mul htrace).integral_prod_right'
    (ν:=sphereLaw N)
  have hm := hi.mul_const ((N:ℝ)⁻¹)
  convert hm using 1
  funext z
  rw [densityResponse_eq_tangentMeanTrace hN hp β R hR z.1 H z.2,div_eq_mul_inv]
  rfl

theorem densityResponse_abs_le_exp (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (H s : ℝ≥0) (hs : s≤H) :
    |quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H s|≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J)*(H:ℝ)) := by
  classical
  let B := Real.exp (((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J)*(H:ℝ))
  have hρs : Continuous (forwardDensity β R hR J s) :=
    (forwardDensity_spatial_contDiff hN (by omega) β R hR J s).continuous
  have hm : ContDiff ℝ 1 (realMean β R hR J ((H:ℝ)-(s:ℝ))) :=
    (realMean_spatial_contDiff β R hR J ((H:ℝ)-(s:ℝ))).of_le (by norm_num)
  have hrm : realMean β R hR J ((H:ℝ)-(s:ℝ))=
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (H-s) := by
    funext y
    rw [←NNReal.coe_sub hs]
    simp only [realMean,Real.toNNReal_coe]
  have hDm (x : State N) (hx : OnSphere x) (v : State N) :
      ‖fderiv ℝ (realMean β R hR J ((H:ℝ)-(s:ℝ))) x (projection x v)‖≤B*‖v‖ := by
    rw [hrm]
    have hRate : 0≤(β:ℝ)*(p:ℝ)^2*landscapeNorm N p J := by
      have := landscapeNorm_nonnegative N p J
      positivity
    exact (actual_mean_tangent_derivative_bound hN hp (VectorBrownian.driver N) β R hR hNR J x v hx (H-s)).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (show ((H-s:ℝ≥0):ℝ)≤H from by exact_mod_cast (tsub_le_self : H-s≤H)) hRate)) (norm_nonneg v))
  have hi (i : Fin N) := continuous_sphere_integrable hN
    (hρs.mul (rotationGamma_continuous (1/(2*(N:ℝ))) (canonicalRotations N) ((coordinateObservable_contDiff i).of_le (by simp))
      ((realMean_coordinate_spatial_contDiff β R hR J i ((H:ℝ)-(s:ℝ))).of_le (by norm_num)))).norm
  have hbound (i : Fin N) :
      |∫x : State N,forwardDensity β R hR J s x*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
        (coordinateObservable i) (fun y => realMean β R hR J ((H:ℝ)-(s:ℝ)) y i) x ∂sphereLaw N|≤B := by
    have hmono := integral_mono_ae (hi i) ((continuous_sphere_integrable hN hρs).mul_const B) (by
      filter_upwards [sphereLaw_support hN] with x hx
      have hxS := (onSphere_iff_norm_sq x).mpr hx
      have hpos := forwardDensity_positive_onSphere hN (by omega) β R hR hNR J s x hxS
      change ‖forwardDensity β R hR J s x*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
        (coordinateObservable i) (fun y => realMean β R hR J ((H:ℝ)-(s:ℝ)) y i) x‖≤_
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left (coordinate_gamma_bound hN hm x hxS (hDm x hxS) i) hpos.le)
    rw [integral_mul_const,forwardDensity_mass_one hN (by omega) β R hR hNR J s,one_mul] at hmono
    exact (norm_integral_le_integral_norm _).trans hmono
  unfold quenchedResponse
  rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_pos (Nat.cast_pos.mpr hN)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => hbound i)).trans_eq (by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring))

theorem densityResponse_window_product_integrable (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H s : ℝ≥0) (hs : s≤H) :
    Integrable (fun z : Disorder N p×ℝ =>
      quenchedResponse (forwardDensity β R hR z.1) (realMean β R hR z.1) H z.2)
      ((disorderLaw N p).prod (volume.restrict (Ioc (0:ℝ) (s:ℝ)))) := by
  have hE := (uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p)
    ((β:ℝ)*(p:ℝ)^2*(H:ℝ))).1
  have hEnv : Integrable (fun J : Disorder N p =>
      Real.exp (((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J)*(H:ℝ))) (disorderLaw N p) := by
    convert hE using 1
    funext J
    congr 1
    ring
  apply (hEnv.comp_fst (volume.restrict (Ioc (0:ℝ) (s:ℝ)))).mono'
    (densityResponse_row_joint_stronglyMeasurable hN (by omega) β R hR H).aestronglyMeasurable
  have ht : ∀ᵐz ∂(disorderLaw N p).prod (volume.restrict (Ioc (0:ℝ) (s:ℝ))),z.2∈Ioc (0:ℝ) (s:ℝ) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
      (.of_forall (fun _ => ae_restrict_mem measurableSet_Ioc))
  filter_upwards [ht] with z hz
  have hzh : z.2.toNNReal≤H := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hz.1.le]
    exact hz.2.trans hs
  simpa only [Real.norm_eq_abs,Real.coe_toNNReal _ hz.1.le] using
    densityResponse_abs_le_exp hN hp β R hR hNR z.1 H z.2.toNNReal hzh

theorem densityResponse_interval_fubini (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H s : ℝ≥0) (hs : s≤H) :
    Integrable (fun J : Disorder N p => ∫u in (0:ℝ)..(s:ℝ),
      quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H u) (disorderLaw N p) ∧
      (∫J : Disorder N p,(∫u in (0:ℝ)..(s:ℝ),
        quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H u) ∂disorderLaw N p)=
        ∫u in (0:ℝ)..(s:ℝ),∫J : Disorder N p,
          quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) H u ∂disorderLaw N p := by
  have hi := densityResponse_window_product_integrable hN hp β R hR hNR H s hs
  simp_rw [intervalIntegral.integral_of_le s.coe_nonneg]
  exact ⟨hi.integral_prod_left,integral_integral_swap hi⟩

end SphericalAging.ActualSphereDensityResponseMoments
