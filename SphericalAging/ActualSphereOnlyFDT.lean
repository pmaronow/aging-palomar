module

public import SphericalAging.SphereOnlyOnSphereFDT
public import SphericalAging.SphereOnlyFisherCurrentContinuity
public import SphericalAging.SphereAnnealedCurrentFDT
public import SphericalAging.ActualSphereMeanSpatialInterface

public section

/-! Actual causal nonequilibrium FDT and finite current increments of the
constructed sphere density and backward mean. All spatial jets and both
sphere evolution equations are proved; no abstract density realization or
ambient mixed time-space smoothness is an input. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BigOperators
namespace SphericalAging.ActualSphereOnlyFDT
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry SphereEntropyDissipation
open SphericalIntegrationByParts SphereGeneratorIntegrationByParts SphereCoordinateScore SphereQuenchedFDT
open SphereOnlyOnSphereFDT SphereOnlyFisherCurrentContinuity SphereOnlyAllTimeContinuity
open ActualSphereMeanSpatialInterface ActualSphereMeanBackward ActualSphereGibbsDensity
open ActualSphereForwardDensityRegularity ActualSphereCurrent
open SphereAnnealedCurrentFDT (rowPrimitive)
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem actual_quenched_fdt_hasDerivAt (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {t s : ℝ} (hs : 0<s) (hst : s<t) :
    HasDerivAt (fun v => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t v)
      (quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s-current β R hR J t s) s := by
  apply quenched_fdt_hasDerivAt_onSphere hN β J
    (ρdot:=fun v x => SphereCanonicalEntropy.sphericalForwardDensitySlope β J
      (forwardDensity β R hR J v) x)
    (forwardDensity_joint_continuous hN hp β R hR J)
    (forwardDensity_spatial_contDiff hN hp β R hR J)
    (forwardDensity_slope_joint_continuous hN hp β R hR J)
    (forwardDensity_hasDerivAt_forwardPDE hN hp β R hR hNR J)
    (realMean_joint_continuous β R hR J)
    (realMean_spatial_contDiff β R hR J)
    (realMean_coordinate_generator_joint_continuous β R hR J)
    (fun i v hv x hx => mean_coordinate_backward_canonical_hasDerivAt
      (Nat.ne_of_gt hN) β R hR hNR J i v hv x hx) hs hst
    (fun x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J s x hx)
  exact fun _ _ => rfl

theorem actual_quenchedResponse_row_continuous (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ) :
    Continuous (fun s => quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s) := by
  classical
  have hcomp : Continuous (fun z : ℝ×State N => (t-z.1,z.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  unfold quenchedResponse
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply SphereEntropyBudget.continuous_sphere_parameter_integral hN
  apply (forwardDensity_joint_continuous hN hp β R hR J).mul
  unfold rotationGamma
  apply continuous_const.mul
  apply continuous_finsetSum
  intro ij _
  exact ((lieDerivative_continuous (canonicalRotations N ij)
    ((coordinateObservable_contDiff i).of_le (by simp))).comp continuous_snd).mul
      ((SphereSpatialGeneratorRegularity.joint_lieDerivative_continuous (canonicalRotations N ij)
        (m:=fun τ x => realMean β R hR J τ x i)
        (realMean_coordinate_first_joint_continuous β R hR J i)).comp hcomp)

theorem actual_quenchedCorrelation_row_continuous (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ) :
    Continuous (fun s => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t s) :=
  SphereIntegratedFDT.quenchedCorrelation_row_continuous hN
    (forwardDensity_joint_continuous hN hp β R hR J) (realMean_joint_continuous β R hR J) t

theorem actual_rowPrimitive_increment_current (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t b-
      rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t a=
        -(∫u in a..b,current β R hR J t u) := by
  have hC := actual_quenchedCorrelation_row_continuous hN hp β R hR J t
  have hRrow := actual_quenchedResponse_row_continuous hN hp β R hR J t
  have hD := actual_current_row_continuous hN hp β R hR hNR J t
  have hder u (hu : u∈Ioo a b) := actual_quenched_fdt_hasDerivAt hN hp β R hR hNR J
    (ha.trans_lt hu.1) (hu.2.trans_le hbt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hC.continuousOn hder
    ((hRrow.sub hD).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (hRrow.intervalIntegrable a b) (hD.intervalIntegrable a b)] at hFTC
  have hRadd := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hRrow.intervalIntegrable 0 a) (hRrow.intervalIntegrable a b)
  unfold rowPrimitive
  linarith

theorem actual_rowPrimitive_increment_fisher_bound (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    (rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t b-
      rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t a)^2≤
        (b-a)*(∫u in a..b,fisherInformation β J (forwardDensity β R hR J u)/(N:ℝ)) := by
  rw [actual_rowPrimitive_increment_current hN hp β R hR hNR J ha hab hbt,neg_sq]
  rcases hab.eq_or_lt with he | hlt
  · subst b
    simp
  have hD := actual_current_row_continuous hN hp β R hR hNR J t
  have hFI := (SphereOnlyAllTimeContinuity.fisher_continuous hN β J
    (forwardDensity_joint_continuous hN hp β R hR J)
    (forwardDensity_first_joint_continuous hN hp β R hR J)
    (forwardDensity_spatial_contDiff hN hp β R hR J)
    (fun u x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J u x hx)).div_const (N:ℝ)
  have hm := intervalIntegral.integral_mono_on (μ:=volume) hab ((hD.pow 2).intervalIntegrable a b)
    (hFI.intervalIntegrable a b)
    (fun u hu => actual_current_square_le_fisher hN hp β R hR hNR J (ha.trans hu.1))
  exact (ResponseTransport.interval_square_bound hlt (hD.intervalIntegrable a b)
    ((hD.pow 2).intervalIntegrable a b)).trans
      (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hab))

end SphericalAging.ActualSphereOnlyFDT
