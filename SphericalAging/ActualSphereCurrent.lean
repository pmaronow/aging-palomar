module

public import SphericalAging.SphereOnlyFisherCurrent
public import SphericalAging.ActualForwardFisherMeasurability
public import SphericalAging.ActualSphereMeanSpatialInterface

public section

/-! Literal current of the constructed forward density and actual backward
mean: its quenched Fisher square estimate and genuine disorder/time
measurability follow from the actual stochastic process. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace NNReal ENNReal
namespace SphericalAging.ActualSphereCurrent
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry
open SphereFisherCurrent SphereOnlyParameterIntegral SphereOnlyFisherCurrent
open ActualSphereTransition ActualSphereMeanSpatialInterface ActualSphereGibbsDensity
open ActualSphereForwardDensityRegularity ActualForwardDensityMeasurability ActualForwardFisherMeasurability
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

@[expose] def current (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t s : ℝ) : ℝ :=
  currentDefect β J (forwardDensity β R hR J s) (realMean β R hR J (t-s))

theorem actual_current_square_le_fisher (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0≤s) :
    (current β R hR J t s)^2≤fisherInformation β J (forwardDensity β R hR J s)/(N:ℝ) := by
  apply currentDefect_fisher_bound_onSphere hN β J
    (forwardDensity_spatial_contDiff hN hp β R hR J s)
    (fun x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J s x hx)
    (forwardDensity_mass_one hN hp β R hR hNR J ⟨s,hs⟩)
    (realMean_spatial_contDiff β R hR J (t-s)).continuous
  exact fun x hx => mean_norm_sq_le (Nat.ne_of_gt hN) (VectorBrownian.driver N)
    β R hR hNR J (t-s).toNNReal x hx

theorem realMean_joint_stronglyMeasurable (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) :
    StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N => realMean β R hR z.1.1 z.1.2 z.2) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let V : ((Disorder N p×ℝ)×State N)×VectorBrownian.Space N→State N :=
    fun z => jointProcess D β R hR (z.1.1.1,z.1.2) z.1.1.2.toNNReal z.2
  have hV : StronglyMeasurable V := (jointProcess_measurable D β R hR).comp_measurable
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      (((continuous_real_toNNReal.measurable.comp
        (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk measurable_snd)))
  change StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N =>
    ∫ω,jointProcess D β R hR (z.1.1,z.2) z.1.2.toNNReal ω ∂VectorBrownian.law N)
  exact hV.integral_prod_right' (ν:=VectorBrownian.law N)

theorem actual_current_joint_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) :
    StronglyMeasurable (fun z : (Disorder N p×ℝ)×ℝ => current β R hR z.1.1 z.1.2 z.2) := by
  let A : (((Disorder N p×ℝ)×ℝ)×State N)→(Disorder N p×ℝ)×State N :=
    fun z => ((z.1.1.1,z.1.2),z.2)
  let B : (((Disorder N p×ℝ)×ℝ)×State N)→(Disorder N p×ℝ)×State N :=
    fun z => ((z.1.1.1,z.1.1.2-z.1.2),z.2)
  have hA : Measurable A :=
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hB : Measurable B :=
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).sub
        (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  have hρC : StronglyMeasurable ((fun z : (Disorder N p×ℝ)×State N =>
      forwardDensity β R hR z.1.1 z.1.2 z.2)∘A) :=
    (forwardDensity_joint_stronglyMeasurable β R hR).comp_measurable hA
  have hρ : StronglyMeasurable (fun z : (((Disorder N p×ℝ)×ℝ)×State N) =>
      forwardDensity β R hR z.1.1.1 z.1.2 z.2) := by
    simpa only [Function.comp_def,A] using hρC
  have hMC : StronglyMeasurable ((fun z : (Disorder N p×ℝ)×State N =>
      realMean β R hR z.1.1 z.1.2 z.2)∘B) :=
    (realMean_joint_stronglyMeasurable β R hR).comp_measurable hB
  have hM : StronglyMeasurable (fun z : (((Disorder N p×ℝ)×ℝ)×State N) =>
      realMean β R hR z.1.1.1 (z.1.1.2-z.1.2) z.2) := by
    simpa only [Function.comp_def,B] using hMC
  have hSC : StronglyMeasurable ((fun z : (Disorder N p×ℝ)×State N =>
      explicitScore β R hR z.1.1 z.1.2 z.2)∘A) :=
    (explicitScore_joint_measurable hN hp β R hR).stronglyMeasurable.comp_measurable hA
  have hS : StronglyMeasurable (fun z : (((Disorder N p×ℝ)×ℝ)×State N) =>
      explicitScore β R hR z.1.1.1 z.1.2 z.2) := by
    simpa only [Function.comp_def,A] using hSC
  have hi := (hρ.mul (hM.inner hS)).integral_prod_right' (ν:=sphereLaw N)
  have hiN := hi.mul_const ((N:ℝ)⁻¹)
  convert hiN using 1
  funext z
  unfold current currentDefect
  rw [div_eq_mul_inv]
  congr 1
  apply integral_congr_ae
  filter_upwards [SphereOnlyParameterIntegral.physicalSphere_ae hN] with x hx
  simp only [Pi.mul_apply]
  rw [explicitScore_eq_tangentScore hN hp β R hR hNR z.1.1 z.2 hx]

end SphericalAging.ActualSphereCurrent
