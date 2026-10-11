module

public import SphericalAging.ActualForwardFisherMeasurability
public import SphericalAging.SphereOnlyFisherBudget
public import SphericalAging.SphereAnnealedFisherBudget

public section

/-! The concrete forward density has a genuine normalized annealed
Fisher time budget at most β²/2. True product integrability and Fubini
follow from the actual sphere-only entropy budget and proved measurability. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereAnnealedFisherBudget
open FiniteModel HardSphereDynamics SphereInitialLaw SphereGibbsEntropy SphereRotationGeometry
open ActualSphereGibbsDensity ActualForwardFisherMeasurability SphereOnlyFisherBudget
open SphereAnnealedFisherBudget
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem actual_annealed_fisher_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) :
    StronglyMeasurable (annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR)) := by
  have hm := forwardDensity_fisher_joint_stronglyMeasurable hN hp β R hR hNR
  change StronglyMeasurable (fun t : ℝ =>
    (∫J : Disorder N p,fisherInformation β J (forwardDensity β R hR J t) ∂disorderLaw N p)/(N : ℝ))
  simpa only [div_eq_mul_inv] using
    (hm.integral_prod_left' (μ:=disorderLaw N p)).mul_const ((N : ℝ)⁻¹)

theorem actual_fisher_product_integrable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) :
    Integrable (fun z : Disorder N p×ℝ => fisherInformation β z.1 (forwardDensity β R hR z.1 z.2))
      ((disorderLaw N p).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable
      (fun z : Disorder N p×ℝ => fisherInformation β z.1 (forwardDensity β R hR z.1 z.2))
      ((disorderLaw N p).prod (volume.restrict (Ioi 0))) :=
    (forwardDensity_fisher_joint_stronglyMeasurable hN hp β R hR hNR).aestronglyMeasurable
  have hb (J : Disorder N p) := actual_forwardDensity_fisher_budget hN hp β R hR hNR J
  have hn (J : Disorder N p) (t : ℝ) : 0≤fisherInformation β J (forwardDensity β R hR J t) :=
    fisher_nonnegative_onSphere hN β J (fun x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J t x hx)
  apply (integrable_prod_iff hm).mpr
  refine ⟨Eventually.of_forall (fun J => (hb J).1),?_⟩
  apply (initialEntropy_annealed_integrable hN hp β.coe_nonneg).mono' hm.norm.integral_prod_right'
  apply Eventually.of_forall
  intro J
  have he : (∫t in Ioi 0,‖fisherInformation β J (forwardDensity β R hR J t)‖)=
      (∫t in Ioi 0,fisherInformation β J (forwardDensity β R hR J t)) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => Real.norm_of_nonneg (hn J t))
  rw [he,Real.norm_of_nonneg (integral_nonneg (hn J))]
  exact (hb J).2

theorem actual_annealed_fisher_time_budget (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) :
    IntegrableOn (annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR)) (Ioi 0) ∧
      (∫t in Ioi 0,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) t)=
        (∫J : Disorder N p,(∫t in Ioi 0,fisherInformation β J (forwardDensity β R hR J t))/(N : ℝ) ∂disorderLaw N p) ∧
      (∫t in Ioi 0,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) t)≤(β : ℝ)^2/2 := by
  have hi := actual_fisher_product_integrable hN hp β R hR hNR
  have htime : IntegrableOn (annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR)) (Ioi 0) :=
    hi.integral_prod_right.div_const _
  have he : (∫t in Ioi 0,annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) t)=
      (∫J : Disorder N p,(∫t in Ioi 0,fisherInformation β J (forwardDensity β R hR J t))/(N : ℝ) ∂disorderLaw N p) := by
    unfold annealedFisher
    rw [integral_div,←integral_integral_swap hi,integral_div]
  refine ⟨htime,he,?_⟩
  rw [he]
  apply (integral_mono_ae (hi.integral_prod_left.div_const _)
    ((initialEntropy_annealed_integrable hN hp β.coe_nonneg).div_const _)
    (Eventually.of_forall (fun J => div_le_div_of_nonneg_right
      (actual_forwardDensity_fisher_budget hN hp β R hR hNR J).2 (Nat.cast_nonneg N)))).trans
      (initialEntropy_normalized_annealed hN hp β.coe_nonneg)

end SphericalAging.ActualSphereAnnealedFisherBudget
