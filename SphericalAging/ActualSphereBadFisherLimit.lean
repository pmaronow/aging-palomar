module

public import SphericalAging.ActualSphereRestrictedFisherBudget

public section

/-! Exponentially vanishing bad-event Fisher mass for the actual forward
density, including arbitrary diverging dimension nets and varying cutoffs. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereBadFisherLimit
open FiniteModel HardSphereDynamics SphereInitialLaw GaussianLandscape GaussianLandscapeMoments
open SphereGoodEventFisherClock SphereTruncatedFisherBudget SphereBadEventFisherMass
open ActualSphereGibbsDensity ActualSphereRestrictedFisherBudget
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem actual_bad_fisher_mass_bound (hN : 2≤N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) :
    IntegrableOn (bad (N:=N) (p:=p) β R hR) (Ioi 0) ∧
      0≤(∫t in Ioi 0,bad (N:=N) (p:=p) β R hR t) ∧
      (∫t in Ioi 0,bad (N:=N) (p:=p) β R hR t)≤
        2*(β:ℝ)*Real.sqrt (momentCeiling p 2)*Real.sqrt (Real.exp (-(N:ℝ))) := by
  have h := actual_restricted_fisher_time_budget (by omega : 0<N) hp β R hR hNR
    (goodEvent N p (cutoff p))ᶜ (goodEvent_measurable N p (cutoff p)).compl
  refine ⟨h.1,integral_nonneg (fun t =>
    actual_restricted_fisher_nonneg (by omega : 0<N) hp β R hR hNR _ t),?_⟩
  apply h.2.2.2.2.trans
  change 2*(β:ℝ)*badLandscapeMoment N p≤_
  exact (mul_le_mul_of_nonneg_left (badLandscapeMoment_bound hN (by omega : 0<p))
    (mul_nonneg (by norm_num) β.coe_nonneg)).trans_eq (by ring)

theorem actual_bad_fisher_mass_tendsto_zero {ι : Type*} {l : Filter ι}
    (p : ℕ) (hp : 1≤p) (β : ℝ≥0) (dim : ι→ℕ)
    (hdim : Tendsto dim l atTop) (R : ι→ℝ≥0)
    (hR : ∀i,0<(R i:ℝ)) (hNR : ∀i,(dim i:ℝ)<(R i:ℝ)^2) :
    Tendsto (fun i => ∫t in Ioi 0,bad (N:=dim i) (p:=p) β (R i) (hR i) t) l (𝓝 0) := by
  have hlarge : ∀ᶠi in l,2≤dim i := hdim.eventually (eventually_ge_atTop 2)
  have he : Tendsto (fun i => Real.exp (-(dim i:ℝ))) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.comp hdim))
  have hs := (Real.continuous_sqrt.tendsto 0).comp he
  apply squeeze_zero' (hlarge.mono fun i hi =>
    (actual_bad_fisher_mass_bound hi hp β (R i) (hR i) (hNR i)).2.1)
    (hlarge.mono fun i hi =>
      (actual_bad_fisher_mass_bound hi hp β (R i) (hR i) (hNR i)).2.2)
  simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using
    hs.const_mul (2*(β:ℝ)*Real.sqrt (momentCeiling p 2))

end SphericalAging.ActualSphereBadFisherLimit
