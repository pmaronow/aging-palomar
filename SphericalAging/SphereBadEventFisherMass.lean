module

public import SphericalAging.SphereTruncatedFisherBudget
public import Mathlib.MeasureTheory.Function.L2Space

public section

/-! The genuine Gaussian bad-event contribution has vanishing total Fisher
mass as the dimension grows. The event probability and landscape moment are
proved for the actual ordered tensor law. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereBadEventFisherMass

open MeasureTheory Set Filter FiniteModel SphereInitialLaw GaussianLandscape
open GaussianLandscapeMoments SphereGoodEventFisherClock SphereTruncatedFisherBudget
open SphereRotationGeometry SphereCanonicalEntropy
open scoped Topology

@[expose] def cutoff (p : ℕ) : ℝ := landscapeThreshold p+4

@[expose] def badLandscapeMoment (N p : ℕ) : ℝ :=
  ∫ J : Disorder N p,(goodEvent N p (cutoff p))ᶜ.indicator (landscapeNorm N p) J ∂disorderLaw N p

/-- Cauchy--Schwarz with the true probability of the truncation event. -/
theorem event_integral_le_sqrt_moment_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hsq : Integrable (fun x => (f x)^2) μ)
    (hn : ∀ x,0≤f x) (E : Set α) (hE : MeasurableSet E) :
    (∫ x,E.indicator f x ∂μ) ≤ Real.sqrt (∫ x,(f x)^2 ∂μ)*Real.sqrt (μ.real E) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hlp : MemLp f (ENNReal.ofReal 2) μ := by
    simpa using (memLp_two_iff_integrable_sq hf).mpr hsq
  have hg : MemLp (E.indicator (fun _ : α => (1 : ℝ))) (ENNReal.ofReal 2) μ :=
    memLp_indicator_const _ hE 1 (Or.inr (measure_ne_top μ E))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ hn)
    (ae_of_all _ fun x => by by_cases hx : x∈E <;> simp [hx]) hlp hg
  have he : (fun x => f x*E.indicator (fun _ : α => (1 : ℝ)) x)=E.indicator f := by
    funext x
    by_cases hx : x∈E <;> simp [hx]
  have he2 : (fun x => (E.indicator (fun _ : α => (1 : ℝ)) x)^(2 : ℝ))=
      E.indicator (fun _ : α => (1 : ℝ)) := by
    funext x
    by_cases hx : x∈E <;> simp [hx]
  rw [he,he2,integral_indicator_const 1 hE] at h
  simpa only [Real.rpow_two,← Real.sqrt_eq_rpow,smul_eq_mul,mul_one] using h

theorem badLandscapeMoment_nonneg (N p : ℕ) : 0≤badLandscapeMoment N p := by
  unfold badLandscapeMoment
  apply integral_nonneg
  intro J
  change (0 : ℝ)≤((goodEvent N p (cutoff p))ᶜ).indicator (landscapeNorm N p) J
  by_cases h : J∈(goodEvent N p (cutoff p))ᶜ
  · simpa only [indicator_of_mem h] using landscapeNorm_nonnegative N p J
  · simp only [indicator_of_notMem h,le_refl]

theorem badLandscapeMoment_bound {N p : ℕ} (hN : 2≤N) (hp : 0<p) :
    badLandscapeMoment N p ≤ Real.sqrt (momentCeiling p 2)*Real.sqrt (Real.exp (-(N : ℝ))) := by
  have hQsq : Integrable (fun J : Disorder N p => (landscapeNorm N p J)^2) (disorderLaw N p) := by
    simpa only [Real.rpow_two] using
      (uniform_real_power_moment (by omega : 1≤N) hp (by norm_num : (0 : ℝ)≤2)).1
  have hQbound : (∫ J : Disorder N p,(landscapeNorm N p J)^2 ∂disorderLaw N p)≤momentCeiling p 2 := by
    simpa only [Real.rpow_two] using
      (uniform_real_power_moment (by omega : 1≤N) hp (by norm_num : (0 : ℝ)≤2)).2
  have hprob : (disorderLaw N p).real (goodEvent N p (cutoff p))ᶜ≤Real.exp (-(N : ℝ)) := by
    have he : (goodEvent N p (cutoff p))ᶜ={J | landscapeThreshold p+4<landscapeNorm N p J} := by
      ext J
      simp [goodEvent,cutoff]
    rw [he]
    exact landscape_exponential_dimension_bound hN hp
  exact (event_integral_le_sqrt_moment_probability (disorderLaw N p)
    (landscapeNorm_continuous N p).aestronglyMeasurable hQsq (landscapeNorm_nonnegative N p)
    _ (goodEvent_measurable N p (cutoff p)).compl).trans
    (mul_le_mul (Real.sqrt_le_sqrt hQbound) (Real.sqrt_le_sqrt hprob)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The actual truncated landscape first moment vanishes with dimension. -/
theorem badLandscapeMoment_tendsto_zero (p : ℕ) (hp : 0<p) :
    Tendsto (fun N : ℕ => badLandscapeMoment N p) atTop (𝓝 0) := by
  have he : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hlim := (Real.continuous_sqrt.tendsto 0).comp he
  apply squeeze_zero' (Eventually.of_forall fun N => badLandscapeMoment_nonneg N p)
    ((eventually_ge_atTop 2).mono fun N hN => badLandscapeMoment_bound hN hp)
  simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using hlim.const_mul (Real.sqrt (momentCeiling p 2))

/-- Explicit exponentially vanishing bad-event total Fisher mass, derived
from the actual smooth forward density and its entropy dissipation. -/
theorem bad_event_fisher_mass_bound {N p : ℕ} (hN : 2≤N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {ρ ρdot : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 2 (Function.uncurry (ρ J)))
    (hdot : ∀ J,Continuous (Function.uncurry (ρdot J)))
    (hpos : ∀ J t x,0<ρ J t x)
    (hderiv : ∀ J t x,HasDerivAt (fun s => ρ J s x) (ρdot J t x) t)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,ρdot J t x=sphericalForwardDensitySlope β J (ρ J t) x)
    (hmeas : AEStronglyMeasurable
      (fun z : Disorder N p × ℝ => fisherInformation β z.1 (ρ z.1 z.2))
      ((disorderLaw N p).prod (volume.restrict (Ioi 0)))) :
    IntegrableOn (restrictedFisher β ρ (goodEvent N p (cutoff p))ᶜ) (Ioi 0) ∧
      (∫ t in Ioi 0,restrictedFisher β ρ (goodEvent N p (cutoff p))ᶜ t) ≤
        2*β*Real.sqrt (momentCeiling p 2)*Real.sqrt (Real.exp (-(N : ℝ))) := by
  have h := restricted_fisher_time_budget (by omega : 0<N) hp hβ hρ hdot hpos hderiv hinit hPDE hmeas
    (goodEvent N p (cutoff p))ᶜ (goodEvent_measurable N p (cutoff p)).compl
  refine ⟨h.1,h.2.2.2.trans ?_⟩
  change 2*β*badLandscapeMoment N p≤_
  exact (mul_le_mul_of_nonneg_left (badLandscapeMoment_bound hN (by omega : 0<p))
    (mul_nonneg (by norm_num) hβ)).trans_eq (by ring)

end SphericalAging.SphereBadEventFisherMass
