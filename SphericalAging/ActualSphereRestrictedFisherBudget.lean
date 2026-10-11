module

public import SphericalAging.ActualSphereAnnealedFisherBudget
public import SphericalAging.SphereBadEventFisherMass

public section

/-! Event-restricted Fisher budgets for the literal constructed forward density.
All product integrability and entropy domination are derived from the genuine
sphere-only quenched budget. No ambient positive-density extension is used. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereRestrictedFisherBudget
open FiniteModel HardSphereDynamics SphereInitialLaw GaussianLandscape SphereGibbsEntropy
open SphereRotationGeometry SphereOnlyFisherBudget ActualSphereGibbsDensity
open ActualForwardFisherMeasurability ActualSphereAnnealedFisherBudget
open SphereAnnealedFisherBudget SphereGoodEventFisherClock SphereTruncatedFisherBudget
open SphereBadEventFisherMass
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def full (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t : ℝ) : ℝ :=
  annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) t
@[expose] def good (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t : ℝ) : ℝ :=
  goodFisher (N:=N) (p:=p) β (cutoff p) (forwardDensity β R hR) t
@[expose] def bad (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t : ℝ) : ℝ :=
  restrictedFisher (N:=N) (p:=p) β (forwardDensity β R hR)
    (goodEvent N p (cutoff p))ᶜ t

theorem actual_fisher_nonneg (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (t : ℝ) :
    0≤fisherInformation β J (forwardDensity β R hR J t) :=
  fisher_nonnegative_onSphere hN β J
    (fun x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J t x hx)

theorem actual_restricted_fisher_nonneg (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : Set (Disorder N p)) (t : ℝ) :
    0≤restrictedFisher β (forwardDensity β R hR) E t := by
  apply integral_nonneg
  intro J
  change (0:ℝ)≤E.indicator
    (fun K => fisherInformation β K (forwardDensity β R hR K t)/(N:ℝ)) J
  by_cases h : J∈E
  · simp only [indicator_of_mem h]
    exact div_nonneg (actual_fisher_nonneg hN hp β R hR hNR J t) (Nat.cast_nonneg N)
  · simp only [indicator_of_notMem h,le_refl]

theorem actual_restricted_fisher_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : Set (Disorder N p)) (hE : MeasurableSet E) :
    StronglyMeasurable (restrictedFisher β (forwardDensity β R hR) E) := by
  have hm := (forwardDensity_fisher_joint_stronglyMeasurable hN hp β R hR hNR).mul_const
    ((N:ℝ)⁻¹)
  have hi := hm.indicator (hE.preimage measurable_fst)
  have he : (fun z : Disorder N p×ℝ =>
      E.indicator (fun J => fisherInformation β J (forwardDensity β R hR J z.2)/(N:ℝ)) z.1)=
      ({z : Disorder N p×ℝ | z.1∈E}).indicator
        (fun z => fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)*(N:ℝ)⁻¹) := by
    funext z
    by_cases hz : z.1∈E <;> simp [hz,div_eq_mul_inv]
  change StronglyMeasurable (fun t : ℝ => ∫J : Disorder N p,
    E.indicator (fun K => fisherInformation β K (forwardDensity β R hR K t)/(N:ℝ)) J ∂disorderLaw N p)
  change StronglyMeasurable (({z : Disorder N p×ℝ | z.1∈E}).indicator
    (fun z => fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)*(N:ℝ)⁻¹)) at hi
  rw [← he] at hi
  exact hi.integral_prod_left' (μ:=disorderLaw N p)

theorem actual_restricted_fisher_time_budget (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : Set (Disorder N p)) (hE : MeasurableSet E) :
    IntegrableOn (restrictedFisher β (forwardDensity β R hR) E) (Ioi 0) ∧
      (∫t in Ioi 0,restrictedFisher β (forwardDensity β R hR) E t)=
        (∫J : Disorder N p,E.indicator (fun K =>
          (∫t in Ioi 0,fisherInformation β K (forwardDensity β R hR K t))/(N:ℝ)) J ∂disorderLaw N p) ∧
      (∫t in Ioi 0,restrictedFisher β (forwardDensity β R hR) E t)≤
        (∫J : Disorder N p,E.indicator (fun K => initialEntropy N p β K/(N:ℝ)) J ∂disorderLaw N p) ∧
      (∫t in Ioi 0,restrictedFisher β (forwardDensity β R hR) E t)≤(β:ℝ)^2/2 ∧
      (∫t in Ioi 0,restrictedFisher β (forwardDensity β R hR) E t)≤
        2*(β:ℝ)*(∫J : Disorder N p,E.indicator (landscapeNorm N p) J ∂disorderLaw N p) := by
  let μ := disorderLaw N p
  let ν := volume.restrict (Ioi (0:ℝ))
  let F (z : Disorder N p×ℝ) := fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)/(N:ℝ)
  let FE (z : Disorder N p×ℝ) := E.indicator
    (fun J => fisherInformation β J (forwardDensity β R hR J z.2)/(N:ℝ)) z.1
  have hprod : Integrable F (μ.prod ν) :=
    (actual_fisher_product_integrable hN hp β R hR hNR).div_const _
  have hFE : FE=({z : Disorder N p×ℝ | z.1∈E}).indicator F := by
    funext z
    by_cases h : z.1∈E <;> simp [FE,F,h]
  have hiFE : Integrable FE (μ.prod ν) := by
    rw [hFE]
    exact hprod.indicator (hE.preimage measurable_fst)
  have hi : IntegrableOn (restrictedFisher β (forwardDensity β R hR) E) (Ioi 0) :=
    hiFE.integral_prod_right
  have he : (∫t in Ioi 0,restrictedFisher β (forwardDensity β R hR) E t)=
      (∫J : Disorder N p,E.indicator (fun K =>
        (∫t in Ioi 0,fisherInformation β K (forwardDensity β R hR K t))/(N:ℝ)) J ∂μ) := by
    unfold restrictedFisher
    change (∫t,∫J,FE (J,t) ∂μ ∂ν)=_
    rw [←integral_integral_swap hiFE]
    apply integral_congr_ae
    exact Eventually.of_forall fun J => by
      by_cases h : J∈E
      · simp only [FE,indicator_of_mem h]
        rw [integral_div]
      · simp only [FE,indicator_of_notMem h,integral_zero]
  let B (J : Disorder N p) := (∫t in Ioi 0,fisherInformation β J (forwardDensity β R hR J t))/(N:ℝ)
  let D (J : Disorder N p) := initialEntropy N p β J/(N:ℝ)
  have hiBbase : Integrable B μ := by
    simpa only [F,B,ν,integral_div] using hprod.integral_prod_left
  have hiB : Integrable (E.indicator B) μ := hiBbase.indicator hE
  have hiD : Integrable D μ := (initialEntropy_annealed_integrable hN hp β.coe_nonneg).div_const _
  have hiDE : Integrable (E.indicator D) μ := hiD.indicator hE
  have hiQ : Integrable (E.indicator (landscapeNorm N p)) μ :=
    (landscapeNorm_integrable hN hp).indicator hE
  have hBD J : B J≤D J := div_le_div_of_nonneg_right
    (actual_forwardDensity_fisher_budget hN hp β R hR hNR J).2 (Nat.cast_nonneg N)
  have hED J : E.indicator B J≤D J := by
    by_cases h : J∈E
    · simpa only [indicator_of_mem h] using hBD J
    · simpa only [indicator_of_notMem h] using
        (initialEntropy_normalized_quenched hN hp β.coe_nonneg J).1
  have hEQ J : E.indicator B J≤2*(β:ℝ)*(E.indicator (landscapeNorm N p) J) := by
    by_cases h : J∈E
    · simp only [indicator_of_mem h]
      exact (hBD J).trans (initialEntropy_normalized_quenched hN hp β.coe_nonneg J).2
    · simp only [indicator_of_notMem h,mul_zero,le_refl]
  refine ⟨hi,he,?_,?_,?_⟩
  · rw [he]
    exact integral_mono hiB hiDE (fun J => by
      by_cases h : J∈E
      · simpa only [indicator_of_mem h] using hBD J
      · simp only [indicator_of_notMem h,le_refl])
  · rw [he]
    exact (integral_mono hiB hiD hED).trans (initialEntropy_normalized_annealed hN hp β.coe_nonneg)
  · rw [he,←integral_const_mul]
    exact integral_mono hiB (hiQ.const_mul _) hEQ

theorem actual_full_eq_good_add_bad_of_integrable
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t : ℝ)
    (hi : Integrable (fun J : Disorder N p =>
      fisherInformation β J (forwardDensity β R hR J t)/(N:ℝ)) (disorderLaw N p)) :
    full (N:=N) (p:=p) β R hR t=good (N:=N) (p:=p) β R hR t+bad (N:=N) (p:=p) β R hR t := by
  unfold full annealedFisher good goodFisher bad restrictedFisher
  rw [←integral_div,integral_indicator (goodEvent_measurable N p (cutoff p)),
    integral_indicator (goodEvent_measurable N p (cutoff p)).compl]
  exact (integral_add_compl (goodEvent_measurable N p (cutoff p)) hi).symm

theorem actual_full_split_ae (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) :
    ∀ᵐt ∂volume.restrict (Ioi (0:ℝ)),
      full (N:=N) (p:=p) β R hR t=good (N:=N) (p:=p) β R hR t+bad (N:=N) (p:=p) β R hR t := by
  filter_upwards [(actual_fisher_product_integrable hN hp β R hR hNR).prod_left_ae] with t ht
  exact actual_full_eq_good_add_bad_of_integrable β R hR t (ht.div_const _)

theorem actual_good_le_full_ae (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) :
    ∀ᵐt ∂volume.restrict (Ioi (0:ℝ)),
      good (N:=N) (p:=p) β R hR t≤full (N:=N) (p:=p) β R hR t := by
  filter_upwards [actual_full_split_ae hN hp β R hR hNR] with t ht
  rw [ht]
  exact le_add_of_nonneg_right (actual_restricted_fisher_nonneg hN hp β R hR hNR _ t)

theorem actual_good_time_budget (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) :
    IntegrableOn (good (N:=N) (p:=p) β R hR) (Ioi 0) ∧
      (∫t in Ioi 0,good (N:=N) (p:=p) β R hR t)≤(β:ℝ)^2/2 := by
  have h := actual_restricted_fisher_time_budget hN hp β R hR hNR
    (goodEvent N p (cutoff p)) (goodEvent_measurable N p (cutoff p))
  exact ⟨h.1,h.2.2.2.1⟩

theorem actual_full_good_bad_time_decomposition (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) :
    (∫t in Ioi 0,full (N:=N) (p:=p) β R hR t)=
      (∫t in Ioi 0,good (N:=N) (p:=p) β R hR t)+
      (∫t in Ioi 0,bad (N:=N) (p:=p) β R hR t) := by
  have hg := (actual_good_time_budget hN hp β R hR hNR).1
  have hb := (actual_restricted_fisher_time_budget hN hp β R hR hNR
    (goodEvent N p (cutoff p))ᶜ (goodEvent_measurable N p (cutoff p)).compl).1
  rw [integral_congr_ae (actual_full_split_ae hN hp β R hR hNR)]
  exact integral_add hg hb

end SphericalAging.ActualSphereRestrictedFisherBudget
