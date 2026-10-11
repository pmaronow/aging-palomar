module

public import SphericalAging.SphereOnSphereFDT
public import SphericalAging.SphereAnnealedIntegratedFDT

public section

/-! The true finite row-current increment, derived from the honest forward
density and backward mean PDEs, and its annealed Fisher interval estimate. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereOnSphereCurrent
open MeasureTheory Set FiniteModel SphereInitialLaw SphereRotationGeometry
open SphereCanonicalEntropy SphereMixedDerivatives SphereAnnealedFisherBudget
open SphereFisherHelly SphereQuenchedFDT SphereIntegratedFDT SphereFisherCurrent
open SphereEntropyDissipation SphereEntropyBudget SphericalIntegrationByParts
open SphereGeneratorIntegrationByParts SphereAnnealedIntegratedFDT
open SphereCarreDuChamp SphereOnSphereFDT
open SphereAnnealedCurrentFDT (rowPrimitive fisher_interval_disorder_integrable_fubini)

structure SphereBackwardMean (N p : ℕ) (β : ℝ) where
  m : Disorder N p → ℝ → Vector N → Vector N
  smooth : ∀ J,ContDiff ℝ 2 (Function.uncurry (m J))
  initial : ∀ J x,m J 0 x=x
  backward : ∀ J i t,0<t → ∀ x,HardSphereDynamics.OnSphere x → HasDerivAt (fun s => m J s x i)
    (rotationGenerator (1/(2*(N : ℝ))) β J (canonicalRotations N) (fun y => m J t y i) x) t
  norm_bound : ∀ J t,0≤t → ∀ x,HardSphereDynamics.OnSphere x → ‖m J t x‖^2≤(N : ℝ)

@[expose] def annealedRowPrimitive {N p : ℕ} {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (t s : ℝ) : ℝ :=
  ∫ J : Disorder N p,rowPrimitive (E.ρ J) (M.m J) t s ∂disorderLaw N p

theorem rowPrimitive_increment_current {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β) (J : Disorder N p)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    rowPrimitive (E.ρ J) (M.m J) t b-rowPrimitive (E.ρ J) (M.m J) t a=
      -(∫ u in a..b,currentDefect β J (E.ρ J u) (M.m J (t-u))) := by
  have hρ₂ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hC := quenchedCorrelation_row_continuous hN hρ₂.continuous (M.smooth J).continuous t
  have hR := quenchedResponse_row_continuous hN hρ₂.continuous (M.smooth J) t
  have hD := currentDefect_row_continuous hN β J hρ₂ (E.positive J) (M.smooth J).continuous t
  have hder u (hu : u∈Ioo a b) := quenched_fdt_hasDerivAt_onSphere hN β J hρ₂
    (timeSlope_contDiff_one hρ₂).continuous
    (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num))) (M.smooth J) (M.backward J)
    (hu.2.trans_le hbt) (E.positive J u) (fun x _ => E.forward J u (ha.trans hu.1.le) x)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hC.continuousOn hder
    ((hR.sub hD).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (hR.intervalIntegrable a b) (hD.intervalIntegrable a b)] at hFTC
  have hRadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hR.intervalIntegrable 0 a) (hR.intervalIntegrable a b)
  unfold rowPrimitive
  linarith

theorem rowPrimitive_increment_fisher_bound {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β) (J : Disorder N p)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    (rowPrimitive (E.ρ J) (M.m J) t b-rowPrimitive (E.ρ J) (M.m J) t a)^2≤
      (b-a)*(∫ u in a..b,fisherInformation β J (E.ρ J u)/(N : ℝ)) := by
  rw [rowPrimitive_increment_current hN E M J ha hab hbt,neg_sq]
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    simp
  have hρ₂ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hD := currentDefect_row_continuous hN β J hρ₂ (E.positive J) (M.smooth J).continuous t
  have hFI := (SphereFisherClock.spherical_fisher_continuous hN β J hρ₂ (E.positive J)).div_const (N : ℝ)
  have hpoint u (hu : u∈Icc a b) : (currentDefect β J (E.ρ J u) (M.m J (t-u)))^2≤
      fisherInformation β J (E.ρ J u)/(N : ℝ) := by
    have hu0 : 0≤u := ha.trans hu.1
    have hmass := density_mass_one hN (1/(2*(N : ℝ))) β J (canonicalRotations N)
      (fun ij => coordinateRotation_skew ij.1 ij.2) hρ₂ (timeSlope_contDiff_one hρ₂).continuous
      (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num))) (E.initial J) hu0
      (fun v hv => E.forward J v hv.1)
    apply currentDefect_fisher_bound hN β J _ (E.positive J u) hmass
      ((M.smooth J).continuous.comp (continuous_const.prodMk continuous_id))
      (M.norm_bound J (t-u) (by linarith [hu.2]))
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ₂.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (u,x)))
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab ((hD.pow 2).intervalIntegrable a b)
    (hFI.intervalIntegrable a b) hpoint
  exact (ResponseTransport.interval_square_bound hlt (hD.intervalIntegrable a b)
    ((hD.pow 2).intervalIntegrable a b)).trans
      (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hab))

/-- The literal disorder mean of the actual finite row increment obeys the
true annealed Fisher interval bound. Its disorder integrability and square
integrability are derived, rather than assumed. -/
theorem row_increment_annealed_fisher_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t)
    (hmeas : AEStronglyMeasurable
      (fun J => rowPrimitive (E.ρ J) (M.m J) t b-rowPrimitive (E.ρ J) (M.m J) t a)
      (disorderLaw N p)) :
    Integrable (fun J => rowPrimitive (E.ρ J) (M.m J) t b-rowPrimitive (E.ρ J) (M.m J) t a)
      (disorderLaw N p) ∧
      (∫ J : Disorder N p,rowPrimitive (E.ρ J) (M.m J) t b-rowPrimitive (E.ρ J) (M.m J) t a
        ∂disorderLaw N p)^2≤(b-a)*(∫ u in a..b,E.full u) := by
  have hFI := fisher_interval_disorder_integrable_fubini hN hp hβ E ha hab
  have hdelta := integrable_and_integrable_sq_of_square_bound (disorderLaw N p) hmeas
    (hFI.1.const_mul (b-a)) (fun J => rowPrimitive_increment_fisher_bound hN E M J ha hab hbt)
  refine ⟨hdelta.1,?_⟩
  have hm := integral_mono hdelta.2 (hFI.1.const_mul (b-a))
    (fun J => rowPrimitive_increment_fisher_bound hN E M J ha hab hbt)
  rw [integral_const_mul,hFI.2] at hm
  exact (probability_integral_square_le (disorderLaw N p) hdelta.1 hdelta.2).trans hm

theorem rowPrimitive_disorder_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t)
    (hmeas : AEStronglyMeasurable (fun J => rowPrimitive (E.ρ J) (M.m J) t s) (disorderLaw N p)) :
    Integrable (fun J => rowPrimitive (E.ρ J) (M.m J) t s) (disorderLaw N p) := by
  have hm : AEStronglyMeasurable
      (fun J => rowPrimitive (E.ρ J) (M.m J) t s-rowPrimitive (E.ρ J) (M.m J) t 0)
      (disorderLaw N p) := by
    simpa only [rowPrimitive,intervalIntegral.integral_same,sub_self,sub_zero] using hmeas
  simpa only [rowPrimitive,intervalIntegral.integral_same,sub_self,sub_zero] using
    (row_increment_annealed_fisher_bound hN hp hβ E M (by norm_num) hs hst hm).1

/-- The actual annealed correlation-minus-response row primitive has the
finite interval estimate required for the source dimension-limit transfer. -/
theorem annealedRowPrimitive_increment_fisher_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    {a b t : ℝ} (ha : 0≤a) (hab : a≤b) (hbt : b≤t)
    (hmeas : ∀ s,AEStronglyMeasurable (fun J => rowPrimitive (E.ρ J) (M.m J) t s) (disorderLaw N p)) :
    (annealedRowPrimitive E M t b-annealedRowPrimitive E M t a)^2≤
      (b-a)*(∫ u in a..b,E.full u) := by
  have haInt := rowPrimitive_disorder_integrable hN hp hβ E M ha (hab.trans hbt) (hmeas a)
  have hbInt := rowPrimitive_disorder_integrable hN hp hβ E M (ha.trans hab) hbt (hmeas b)
  unfold annealedRowPrimitive
  rw [← integral_sub hbInt haInt]
  exact (row_increment_annealed_fisher_bound hN hp hβ E M ha hab hbt ((hmeas b).sub (hmeas a))).2

end SphericalAging.SphereOnSphereCurrent
