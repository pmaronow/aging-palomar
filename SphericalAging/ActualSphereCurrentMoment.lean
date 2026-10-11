module

public import SphericalAging.ActualSphereCurrent
public import SphericalAging.ActualSphereAnnealedFisherBudget
public import Mathlib.MeasureTheory.Function.L2Space

public section

/-! Genuine disorder-time square moments and finite-window Fubini for the
actual Fisher current. The square budget follows directly from the actual
quenched current estimate and constructed annealed entropy budget. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SphericalAging.ActualSphereCurrentMoment
open FiniteModel SphereInitialLaw SphereRotationGeometry ActualSphereGibbsDensity
open ActualSphereCurrent ActualSphereAnnealedFisherBudget SphereAnnealedFisherBudget
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem actual_current_row_joint_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ) :
    StronglyMeasurable (fun z : Disorder N p×ℝ => current β R hR z.1 t z.2) := by
  have hc : StronglyMeasurable ((fun z : (Disorder N p×ℝ)×ℝ =>
      current β R hR z.1.1 z.1.2 z.2)∘(fun z : Disorder N p×ℝ => ((z.1,t),z.2))) :=
    (actual_current_joint_stronglyMeasurable hN hp β R hR hNR).comp_measurable
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  simpa only [Function.comp_def] using hc

theorem actual_current_square_bound_ae (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ) :
    ∀ᵐz ∂(disorderLaw N p).prod (volume.restrict (Ioi (0:ℝ))),
      (current β R hR z.1 t z.2)^2≤fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)/(N:ℝ) := by
  have hpos : ∀ᵐz ∂(disorderLaw N p).prod (volume.restrict (Ioi (0:ℝ))),0<z.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_snd)).mpr
      (Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi)
  exact hpos.mono fun z hz => actual_current_square_le_fisher hN hp β R hR hNR z.1 hz.le

theorem actual_current_product_square_integrable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ) :
    Integrable (fun z : Disorder N p×ℝ => (current β R hR z.1 t z.2)^2)
      ((disorderLaw N p).prod (volume.restrict (Ioi (0:ℝ)))) := by
  apply ((actual_fisher_product_integrable hN hp β R hR hNR).div_const (N:ℝ)).mono'
    ((actual_current_row_joint_stronglyMeasurable hN hp β R hR hNR t).aestronglyMeasurable.pow 2)
  filter_upwards [actual_current_square_bound_ae hN hp β R hR hNR t] with z hz
  change ‖(current β R hR z.1 t z.2)^2‖≤_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hz

theorem actual_current_product_square_budget (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ) :
    (∫z : Disorder N p×ℝ,(current β R hR z.1 t z.2)^2
      ∂(disorderLaw N p).prod (volume.restrict (Ioi (0:ℝ))))≤(β:ℝ)^2/2 := by
  have hFI := (actual_fisher_product_integrable hN hp β R hR hNR).div_const (N:ℝ)
  have hh := integral_mono_ae (actual_current_product_square_integrable hN hp β R hR hNR t)
    hFI (actual_current_square_bound_ae hN hp β R hR hNR t)
  have he : (∫z : Disorder N p×ℝ,fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)/(N:ℝ)
      ∂(disorderLaw N p).prod (volume.restrict (Ioi (0:ℝ))))=
      (∫s in Ioi 0,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) s) := by
    rw [integral_prod_symm _ hFI]
    unfold annealedFisher
    simp_rw [integral_div]
  rw [he] at hh
  exact hh.trans (actual_annealed_fisher_time_budget hN hp β R hR hNR).2.2

theorem actual_current_window_product_integrable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ)
    {a b : ℝ} (ha : 0≤a) :
    Integrable (fun z : Disorder N p×ℝ => current β R hR z.1 t z.2)
      ((disorderLaw N p).prod (volume.restrict (Ioc a b))) := by
  have hsub : Ioc a b⊆Ioi (0:ℝ) := fun _ hx => ha.trans_lt hx.1
  have hsq := (actual_current_product_square_integrable hN hp β R hR hNR t).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl))
  have hlp : MemLp (fun z : Disorder N p×ℝ => current β R hR z.1 t z.2) 2
      ((disorderLaw N p).prod (volume.restrict (Ioc a b))) :=
    (memLp_two_iff_integrable_sq
      (actual_current_row_joint_stronglyMeasurable hN hp β R hR hNR t).aestronglyMeasurable).mpr hsq
  exact hlp.integrable (by norm_num)

theorem actual_current_window_fubini (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ)
    {a b : ℝ} (ha : 0≤a) :
    IntegrableOn (fun s => ∫J : Disorder N p,current β R hR J t s ∂disorderLaw N p) (Ioc a b) ∧
      (∫s in Ioc a b,∫J : Disorder N p,current β R hR J t s ∂disorderLaw N p)=
        (∫J : Disorder N p,(∫s in Ioc a b,current β R hR J t s) ∂disorderLaw N p) := by
  have hi := actual_current_window_product_integrable hN hp β R hR hNR t (b:=b) ha
  exact ⟨hi.integral_prod_right,(integral_integral_swap hi).symm⟩

theorem actual_current_interval_fubini (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    (∫s in a..b,∫J : Disorder N p,current β R hR J t s ∂disorderLaw N p)=
      (∫J : Disorder N p,(∫s in a..b,current β R hR J t s) ∂disorderLaw N p) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  exact (actual_current_window_fubini hN hp β R hR hNR t ha).2

end SphericalAging.ActualSphereCurrentMoment
