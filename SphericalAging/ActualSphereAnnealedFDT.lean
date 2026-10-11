module

public import SphericalAging.ActualSphereOnlyFDT
public import SphericalAging.ActualSphereCurrentMoment
public import SphericalAging.SphereAnnealedIntegratedFDT

public section

/-! The literal disorder mean of the constructed sphere FDT row primitive.
Disorder measurability, integrability, current Fubini and the finite Fisher
window bound all follow from the actual supported evolution equations. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace SphericalAging.ActualSphereAnnealedFDT
open FiniteModel SphereInitialLaw SphereRotationGeometry ActualSphereGibbsDensity
open ActualSphereMeanSpatialInterface ActualSphereCurrent ActualSphereCurrentMoment
open ActualSphereOnlyFDT ActualSphereAnnealedFisherBudget SphereAnnealedFisherBudget
open SphereAnnealedIntegratedFDT
open SphereAnnealedCurrentFDT (rowPrimitive)
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

@[expose] def annealedRowPrimitive (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t s : ℝ) : ℝ :=
  ∫J : Disorder N p,rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s ∂disorderLaw N p

theorem actual_fisher_interval_disorder_integrable_fubini (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    Integrable (fun J : Disorder N p => ∫u in a..b,
      fisherInformation β J (forwardDensity β R hR J u)/(N:ℝ)) (disorderLaw N p) ∧
      (∫J : Disorder N p,(∫u in a..b,fisherInformation β J (forwardDensity β R hR J u)/(N:ℝ))
        ∂disorderLaw N p)=(∫u in a..b,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) u) := by
  have hsub : Ioc a b⊆Ioi (0:ℝ) := fun _ hu => ha.trans_lt hu.1
  have hw := ((actual_fisher_product_integrable hN hp β R hR hNR).div_const (N:ℝ)).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl))
  refine ⟨?_,?_⟩
  · simpa only [intervalIntegral.integral_of_le hab] using hw.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_le hab]
    rw [integral_integral_swap hw]
    unfold annealedFisher
    simp_rw [integral_div]

theorem actual_rowPrimitive_eq_current (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s=
      -(∫u in (0:ℝ)..s,current β R hR J t u) := by
  simpa only [rowPrimitive,intervalIntegral.integral_same,sub_self,sub_zero] using
    actual_rowPrimitive_increment_current hN hp β R hR hNR J (a:=0) (by norm_num) hs hst

theorem actual_rowPrimitive_disorder_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    StronglyMeasurable (fun J : Disorder N p =>
      rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s) := by
  have he : (fun J : Disorder N p => rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s)=
      (fun J : Disorder N p => -(∫u in Ioc (0:ℝ) s,current β R hR J t u)) := by
    funext J
    rw [actual_rowPrimitive_eq_current hN hp β R hR hNR J hs hst,
      intervalIntegral.integral_of_le hs]
  rw [he]
  exact ((actual_current_row_joint_stronglyMeasurable hN hp β R hR hNR t).integral_prod_right'
    (ν:=volume.restrict (Ioc (0:ℝ) s))).neg

theorem actual_rowPrimitive_disorder_integrable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    Integrable (fun J : Disorder N p =>
      rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s) (disorderLaw N p) := by
  have he : (fun J : Disorder N p => rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t s)=
      (fun J : Disorder N p => -(∫u in Ioc (0:ℝ) s,current β R hR J t u)) := by
    funext J
    rw [actual_rowPrimitive_eq_current hN hp β R hR hNR J hs hst,
      intervalIntegral.integral_of_le hs]
  rw [he]
  exact (actual_current_window_product_integrable hN hp β R hR hNR t (b:=s)
    (a:=0) (by norm_num)).integral_prod_left.neg

theorem actual_annealedRowPrimitive_increment_current (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    annealedRowPrimitive (N:=N) (p:=p) β R hR t b-annealedRowPrimitive (N:=N) (p:=p) β R hR t a=
      -(∫u in a..b,∫J : Disorder N p,current β R hR J t u ∂disorderLaw N p) := by
  have hiA := actual_rowPrimitive_disorder_integrable hN hp β R hR hNR ha (hab.trans hbt)
  have hiB := actual_rowPrimitive_disorder_integrable hN hp β R hR hNR (ha.trans hab) hbt
  unfold annealedRowPrimitive
  rw [←integral_sub hiB hiA]
  simp_rw [actual_rowPrimitive_increment_current hN hp β R hR hNR _ ha hab hbt]
  rw [integral_neg,←actual_current_interval_fubini hN hp β R hR hNR t ha hab]

theorem actual_row_increment_annealed_fisher_bound (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    Integrable (fun J : Disorder N p =>
      (rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t b-
        rowPrimitive (forwardDensity β R hR J) (realMean β R hR J) t a)^2) (disorderLaw N p) ∧
      (annealedRowPrimitive (N:=N) (p:=p) β R hR t b-annealedRowPrimitive (N:=N) (p:=p) β R hR t a)^2≤
        (b-a)*(∫u in a..b,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) u) := by
  have hFI := actual_fisher_interval_disorder_integrable_fubini hN hp β R hR hNR ha hab
  have hmeas := (actual_rowPrimitive_disorder_stronglyMeasurable hN hp β R hR hNR
    (ha.trans hab) hbt).sub (actual_rowPrimitive_disorder_stronglyMeasurable hN hp β R hR hNR
      ha (hab.trans hbt))
  have hi := integrable_and_integrable_sq_of_square_bound (disorderLaw N p) hmeas.aestronglyMeasurable
    (hFI.1.const_mul (b-a)) (fun J => actual_rowPrimitive_increment_fisher_bound hN hp β R hR hNR J ha hab hbt)
  refine ⟨hi.2,?_⟩
  have hmono := integral_mono hi.2 (hFI.1.const_mul (b-a))
    (fun J => actual_rowPrimitive_increment_fisher_bound hN hp β R hR hNR J ha hab hbt)
  rw [integral_const_mul,hFI.2] at hmono
  have hsq := (probability_integral_square_le (disorderLaw N p) hi.1 hi.2).trans hmono
  unfold annealedRowPrimitive
  rw [←integral_sub (actual_rowPrimitive_disorder_integrable hN hp β R hR hNR (ha.trans hab) hbt)
    (actual_rowPrimitive_disorder_integrable hN hp β R hR hNR ha (hab.trans hbt))]
  exact hsq

theorem actual_annealedRowPrimitive_increment_fisher_bound (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    (annealedRowPrimitive (N:=N) (p:=p) β R hR t b-annealedRowPrimitive (N:=N) (p:=p) β R hR t a)^2≤
      (b-a)*(∫u in a..b,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) u) :=
  (actual_row_increment_annealed_fisher_bound hN hp β R hR hNR ha hab hbt).2

end SphericalAging.ActualSphereAnnealedFDT
