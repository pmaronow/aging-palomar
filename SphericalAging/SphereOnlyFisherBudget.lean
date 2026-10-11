module

public import SphericalAging.SphereOnlyEntropyDissipation
public import SphericalAging.SphereOnlyEntropyBounds
public import SphericalAging.SphereOnlyAllTimeContinuity

public section

/-! Actual all-positive-time Fisher budget. Entropy differentiation is
needed only in the interior of the time interval, so the actual initial
sphere law and positive-time sphere PDE suffice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyFisherBudget
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereEntropyDissipation SphereRotationGeometry
open SphereOnlyEntropyBounds SphereOnlyAllTimeContinuity SphereOnlyEntropyDissipation
open ActualSphereGibbsDensity ActualSphereForwardDensityRegularity SphereGibbsEntropy
open scoped Topology NNReal
variable {N p : ℕ}

theorem fisher_nonnegative_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    0≤fisherInformation β J ρ := by
  apply integral_nonneg_of_ae
  exact (physicalSphere_ae hN).mono fun x hx => mul_nonneg (hpos x hx).le (sq_nonneg _)

theorem integrated_entropy_dissipation_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→HasDerivAt (fun s => relativeEntropy β J (ρ s))
      (-fisherInformation β J (ρ t)) t) {T : ℝ} (hT : 0≤T) :
    (∫t in 0..T,fisherInformation β J (ρ t))=
      relativeEntropy β J (ρ 0)-relativeEntropy β J (ρ T) := by
  have hF := fisher_continuous hN β J hρ hD hspace hpos
  have hE := relativeEntropy_continuous hN β J hρ hpos
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hE.continuousOn
    (fun t ht => hd t ht.1) (hF.neg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg] at hh
  linarith only [hh]

theorem finite_fisher_budget_onSphere (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→HasDerivAt (fun s => relativeEntropy β J (ρ s))
      (-fisherInformation β J (ρ t)) t)
    (hmass : ∀t,0≤t→(∫x,ρ t x ∂sphereLaw N)=1)
    (hinit : ∀x,x∈physicalSphere N→ρ 0 x=1) {T : ℝ} (hT : 0≤T) :
    (∫t in 0..T,fisherInformation β J (ρ t)) ≤ initialEntropy N p β J := by
  rw [integrated_entropy_dissipation_onSphere hN β J hρ hD hspace hpos hd hT,
    relativeEntropy_uniform_onSphere hN hp hβ J hinit]
  have he := relativeEntropy_nonnegative_onSphere hN hp hβ J
    (hρ.comp (continuous_const.prodMk continuous_id)) (hpos T) (hmass T hT)
  change 0≤relativeEntropy β J (ρ T) at he
  linarith only [he]

theorem infinite_fisher_budget_onSphere (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→HasDerivAt (fun s => relativeEntropy β J (ρ s))
      (-fisherInformation β J (ρ t)) t)
    (hmass : ∀t,0≤t→(∫x,ρ t x ∂sphereLaw N)=1)
    (hinit : ∀x,x∈physicalSphere N→ρ 0 x=1) :
    IntegrableOn (fun t => fisherInformation β J (ρ t)) (Ioi 0) ∧
      (∫t in Ioi 0,fisherInformation β J (ρ t)) ≤ initialEntropy N p β J := by
  let F := fun t => fisherInformation β J (ρ t)
  have hc : Continuous F := fisher_continuous hN β J hρ hD hspace hpos
  have hpF : ∀t,0≤F t := fun t => fisher_nonnegative_onSphere hN β J (hpos t)
  have hb : ∀T,0≤T→(∫t in 0..T,F t) ≤ initialEntropy N p β J :=
    fun T hT => finite_fisher_budget_onSphere hN hp hβ J hρ hD hspace hpos hd hmass hinit hT
  have hi : IntegrableOn F (Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (initialEntropy N p β J) (0:ℝ)
      (b:=fun T : ℝ => T) (l:=atTop)
      (fun T => (hc.intervalIntegrable 0 T).1) tendsto_id
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpF _)] using hb T hT
  refine ⟨hi,?_⟩
  have hh := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hi
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  apply le_of_tendsto hh
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  exact hb T hT

theorem actual_forwardDensity_fisher_budget (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) :
    IntegrableOn (fun t => fisherInformation β J (forwardDensity β R hR J t)) (Ioi 0) ∧
      (∫t in Ioi 0,fisherInformation β J (forwardDensity β R hR J t)) ≤ initialEntropy N p β J := by
  exact infinite_fisher_budget_onSphere hN hp β.coe_nonneg J
    (forwardDensity_joint_continuous hN hp β R hR J)
    (forwardDensity_first_joint_continuous hN hp β R hR J)
    (forwardDensity_spatial_contDiff hN hp β R hR J)
    (fun t x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J t x hx)
    (fun t ht => actual_forwardDensity_entropy_hasDerivAt hN hp β R hR hNR J ht)
    (fun t ht => forwardDensity_mass_one hN hp β R hR hNR J ⟨t,ht⟩)
    (fun x hx => forwardDensity_initial_onSphere hN hp β R hR hNR J x hx)

end SphericalAging.SphereOnlyFisherBudget
