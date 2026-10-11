module

public import SphericalAging.ActualSphereAnnealedFDT
public import SphericalAging.ActualSphereRestrictedFisherBudget

public section

/-! Genuine signed integrated FDT for the constructed density and backward
mean, including its actual diagonal and annealed Fisher window estimate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace SphericalAging.ActualSphereIntegratedFDT
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry
open SphereQuenchedFDT SphereIntegratedFDT SphereAnnealedIntegratedFDT
open ActualSphereGibbsDensity ActualSphereTransition ActualSphereMeanBackward
open ActualSphereMeanSpatialInterface ActualSphereCurrent ActualSphereCurrentMoment
open ActualSphereOnlyFDT ActualSphereAnnealedFDT ActualSphereAnnealedFisherBudget
open ActualSphereRestrictedFisherBudget SphereAnnealedFisherBudget
open SphereAnnealedCurrentFDT (rowPrimitive)
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem actual_realMean_zero (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (x : State N) :
    realMean β R hR J 0 x=x := by
  ext i
  change mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (0:ℝ).toNNReal x i=x i
  rw [Real.toNNReal_zero,←transition_coordinate_eq_mean β R hR J 0 i x,transition_zero]

theorem actual_quenchedCorrelation_diagonal (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {t : ℝ} (ht : 0≤t) :
    quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t t=1 := by
  apply quenchedCorrelation_diagonal hN (forwardDensity_joint_continuous hN hp β R hR J)
    (realMean_joint_continuous β R hR J) (actual_realMean_zero β R hR J) t
  simpa only [Real.coe_toNNReal _ ht] using forwardDensity_mass_one hN hp β R hR hNR J t.toNNReal

theorem actual_integratedDefect_eq_row_increment (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s=
      rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t t-
        rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s := by
  have hRrow := actual_quenchedResponse_row_continuous hN hp β R hR J t
  have hRadd := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hRrow.intervalIntegrable 0 s) (hRrow.intervalIntegrable s t)
  unfold integratedDefect rowPrimitive
  rw [actual_quenchedCorrelation_diagonal hN hp β R hR hNR J (hs.trans hst)]
  linarith

theorem actual_integratedDefect_current (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s=
      -(∫u in s..t,current β R hR J t u) := by
  rw [actual_integratedDefect_eq_row_increment hN hp β R hR hNR J hs hst,
    actual_rowPrimitive_increment_current hN hp β R hR hNR J hs hst le_rfl]

theorem actual_integratedDefect_fisher_bound (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    (integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s)^2≤
      (t-s)*(∫u in s..t,fisherInformation β J (forwardDensity β R hR J u)/(N:ℝ)) := by
  rw [actual_integratedDefect_eq_row_increment hN hp β R hR hNR J hs hst]
  exact actual_rowPrimitive_increment_fisher_bound hN hp β R hR hNR J hs hst le_rfl

theorem actual_annealed_integratedDefect_current (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    Integrable (fun J : Disorder N p =>
      integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s) (disorderLaw N p) ∧
      (∫J : Disorder N p,integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s
        ∂disorderLaw N p)=-(∫u in s..t,∫J : Disorder N p,current β R hR J t u ∂disorderLaw N p) := by
  have he : (fun J : Disorder N p => integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s)=
      (fun J : Disorder N p => rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t t-
        rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s) :=
    funext (fun J => actual_integratedDefect_eq_row_increment hN hp β R hR hNR J hs hst)
  refine ⟨?_,?_⟩
  · rw [he]
    exact (actual_rowPrimitive_disorder_integrable hN hp β R hR hNR (hs.trans hst) le_rfl).sub
      (actual_rowPrimitive_disorder_integrable hN hp β R hR hNR hs hst)
  · simp_rw [actual_integratedDefect_current hN hp β R hR hNR _ hs hst]
    rw [integral_neg,←actual_current_interval_fubini hN hp β R hR hNR t hs hst]

theorem actual_annealed_integratedDefect_fisher_bound (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    (∫J : Disorder N p,integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s
      ∂disorderLaw N p)^2≤(t-s)*(∫u in s..t,
        annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) u) := by
  simp_rw [actual_integratedDefect_eq_row_increment hN hp β R hR hNR _ hs hst]
  rw [integral_sub (actual_rowPrimitive_disorder_integrable hN hp β R hR hNR (hs.trans hst) le_rfl)
    (actual_rowPrimitive_disorder_integrable hN hp β R hR hNR hs hst)]
  exact actual_annealedRowPrimitive_increment_fisher_bound hN hp β R hR hNR hs hst le_rfl

theorem actual_annealed_fisher_interval_budget (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    (∫u in s..t,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) u)≤(β:ℝ)^2/2 := by
  have hb := actual_annealed_fisher_time_budget hN hp β R hR hNR
  have hn (u : ℝ) : 0≤annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) u := by
    unfold annealedFisher
    exact div_nonneg (integral_nonneg (fun J => actual_fisher_nonneg hN hp β R hR hNR J u))
      (Nat.cast_nonneg N)
  rw [intervalIntegral.integral_of_le hst]
  exact (setIntegral_mono_set hb.1 (.of_forall hn)
    (.of_forall (fun u hu => hs.trans_lt hu.1))).trans hb.2.2

theorem actual_annealed_integratedDefect_entropy_bound (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    (∫J : Disorder N p,integratedDefect (forwardDensity β R hR J) (realMean β R hR J) t s
      ∂disorderLaw N p)^2≤(t-s)*(β:ℝ)^2/2 := by
  exact (actual_annealed_integratedDefect_fisher_bound hN hp β R hR hNR hs hst).trans
    ((mul_le_mul_of_nonneg_left (actual_annealed_fisher_interval_budget hN hp β R hR hNR hs hst)
      (sub_nonneg.mpr hst)).trans_eq (by ring))

end SphericalAging.ActualSphereIntegratedFDT
