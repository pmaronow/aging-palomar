module

public import SphericalAging.MonotoneHelly
public import SphericalAging.SphereBadEventFisherMass

public section

/-! Dimension subsequences of the actual spherical Fisher information.
The only analytic inputs describe the honest positive smooth forward density
and measurability of its constructed Fisher integrands. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFisherHelly
open MeasureTheory Set Filter FiniteModel SphereInitialLaw SphereRotationGeometry
open SphereCanonicalEntropy SphereMixedDerivatives SphereAnnealedFisherBudget
open SphereGoodEventFisherClock SphereTruncatedFisherBudget SphereBadEventFisherMass
open GaussianLandscapeMoments
open scoped Topology

/-- Honest forward density data, without a Fisher estimate, clock, limit,
or total-mass conclusion among its fields. -/
structure FisherDensity (N p : ℕ) (β : ℝ) where
  ρ : Disorder N p → ℝ → Vector N → ℝ
  smooth : ∀ J,ContDiff ℝ 3 (Function.uncurry (ρ J))
  positive : ∀ J t x,0<ρ J t x
  initial : ∀ J x,ρ J 0 x=1
  forward : ∀ J t,0≤t → ∀ x,timeSlope (ρ J) t x=sphericalForwardDensitySlope β J (ρ J t) x
  fisher_measurable : ∀ t,AEStronglyMeasurable (fun J => fisherInformation β J (ρ J t)) (disorderLaw N p)
  fisher_product_measurable : AEStronglyMeasurable
    (fun z : Disorder N p × ℝ => fisherInformation β z.1 (ρ z.1 z.2))
    ((disorderLaw N p).prod (volume.restrict (Ioi 0)))

namespace FisherDensity
variable {N p : ℕ} {β : ℝ}

@[expose] def full (E : FisherDensity N p β) (t : ℝ) : ℝ := annealedFisher β E.ρ t
@[expose] def good (E : FisherDensity N p β) (t : ℝ) : ℝ := goodFisher β (cutoff p) E.ρ t
@[expose] def bad (E : FisherDensity N p β) (t : ℝ) : ℝ :=
  restrictedFisher β E.ρ (goodEvent N p (cutoff p))ᶜ t
@[expose] def clock (E : FisherDensity N p β) (t : ℝ) : ℝ :=
  Real.exp (-ceilingRate p β (cutoff p)*max t 0)*E.good (max t 0)

theorem full_nonneg (E : FisherDensity N p β) (t : ℝ) : 0≤E.full t := by
  apply div_nonneg _ (Nat.cast_nonneg N)
  exact integral_nonneg fun J => SphereFisherClockDecay.spherical_fisher_nonneg β J (E.positive J) t

theorem bad_nonneg (E : FisherDensity N p β) (t : ℝ) : 0≤E.bad t := by
  unfold bad restrictedFisher
  apply integral_nonneg
  intro J
  change (0 : ℝ)≤((goodEvent N p (cutoff p))ᶜ).indicator
    (fun K => fisherInformation β K (E.ρ K t)/(N : ℝ)) J
  by_cases h : J∈(goodEvent N p (cutoff p))ᶜ
  · rw [indicator_of_mem h]
    exact div_nonneg (SphereFisherClockDecay.spherical_fisher_nonneg β J (E.positive J) t)
      (Nat.cast_nonneg N)
  · simp only [indicator_of_notMem h,le_refl]

theorem full_eq_good_add_bad (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (E : FisherDensity N p β) {t : ℝ} (ht : 0≤t) : E.full t=E.good t+E.bad t := by
  have hi := fisher_disorder_integrable hN hp hβ E.smooth E.positive E.initial E.forward ht
    (E.fisher_measurable t)
  unfold full annealedFisher good goodFisher bad restrictedFisher
  rw [← integral_div,integral_indicator (goodEvent_measurable N p (cutoff p)),
    integral_indicator (goodEvent_measurable N p (cutoff p)).compl]
  exact (integral_add_compl (goodEvent_measurable N p (cutoff p)) hi).symm

theorem full_budget (hN : 0<N) (hp : 1≤p) (hβ : 0≤β) (E : FisherDensity N p β) :
    IntegrableOn E.full (Ioi 0) ∧ (∫ t in Ioi 0,E.full t)≤β^2/2 := by
  have h := annealed_fisher_time_budget hN hp hβ (ρ := E.ρ) (ρdot := fun J => timeSlope (E.ρ J))
    (fun J => (E.smooth J).of_le (by norm_num))
    (fun J => (timeSlope_contDiff_one ((E.smooth J).of_le (by norm_num))).continuous)
    E.positive (fun J => timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num)))
    E.initial E.forward E.fisher_product_measurable
  exact ⟨h.1,h.2.2⟩

theorem event_budget (hN : 0<N) (hp : 1≤p) (hβ : 0≤β) (E : FisherDensity N p β)
    (D : Set (Disorder N p)) (hD : MeasurableSet D) :
    IntegrableOn (restrictedFisher β E.ρ D) (Ioi 0) ∧
      (∫ t in Ioi 0,restrictedFisher β E.ρ D t)≤β^2/2 := by
  have h := restricted_fisher_time_budget hN hp hβ (ρ := E.ρ) (ρdot := fun J => timeSlope (E.ρ J))
    (fun J => (E.smooth J).of_le (by norm_num))
    (fun J => (timeSlope_contDiff_one ((E.smooth J).of_le (by norm_num))).continuous)
    E.positive (fun J => timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num)))
    E.initial E.forward E.fisher_product_measurable D hD
  exact ⟨h.1,h.2.2.1⟩

theorem bad_mass_bound (hN : 2≤N) (hp : 1≤p) (hβ : 0≤β) (E : FisherDensity N p β) :
    IntegrableOn E.bad (Ioi 0) ∧ (∫ t in Ioi 0,E.bad t)≤
      2*β*Real.sqrt (momentCeiling p 2)*Real.sqrt (Real.exp (-(N : ℝ))) := by
  exact bad_event_fisher_mass_bound hN hp hβ
    (fun J => (E.smooth J).of_le (by norm_num))
    (fun J => (timeSlope_contDiff_one ((E.smooth J).of_le (by norm_num))).continuous)
    E.positive (fun J => timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num)))
    E.initial E.forward E.fisher_product_measurable

theorem clock_antitone (hN : 0<N) (hp : 2≤p) (hβ : 0≤β) (E : FisherDensity N p β) :
    Antitone E.clock := by
  intro s t hst
  exact goodFisher_clock_antitoneOn hN hp hβ (cutoff p) E.smooth E.positive E.initial E.forward
    E.fisher_measurable (show max s 0∈Ici (0 : ℝ) from le_max_right s 0)
    (show max t 0∈Ici (0 : ℝ) from le_max_right t 0) (max_le_max hst (le_refl 0))

theorem clock_bounds (hN : 0<N) (hp : 2≤p) (hβ : 0≤β) (E : FisherDensity N p β) (t : ℝ) :
    0≤E.clock t ∧ E.clock t≤β^2*(p : ℝ) :=
  goodFisher_clock_uniform_bound hN hp hβ (cutoff p) E.smooth E.positive E.initial E.forward
    E.fisher_measurable (le_max_right t 0)

theorem good_eq_exp_clock (E : FisherDensity N p β) {t : ℝ} (ht : 0≤t) :
    E.good t=Real.exp (ceilingRate p β (cutoff p)*t)*E.clock t := by
  unfold clock
  rw [max_eq_left ht,← mul_assoc,← Real.exp_add]
  simp

end FisherDensity

/-- The actual dimension family has one genuine rational/Helly subsequence;
the good-event Fisher limit is right-continuous and has the common clock. -/
theorem actual_clock_Helly {p : ℕ} (hp : 2≤p) {β : ℝ} (hβ : 0≤β)
    (E : ∀ n : ℕ,FisherDensity (n+2) p β) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ),StrictMono φ ∧ Antitone g ∧
      (∀ t,0≤g t ∧ g t≤β^2*(p : ℝ)) ∧ (∀ t,ContinuousWithinAt g (Ici t) t) ∧
      (∀ᵐ t ∂volume,Tendsto (fun n => (E (φ n)).clock t) atTop (𝓝 (g t))) ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ t in Ioc 0 T,|(E (φ n)).clock t-g t|) atTop (𝓝 0)) := by
  exact MonotoneHelly.subsequence_L1loc
    (fun n => (E n).clock_antitone (by omega) hp hβ)
    (fun n t => (E n).clock_bounds (by omega) hp hβ t)

/-- The constructed limit of the literal full annealed Fisher information:
one dimension subsequence, local L¹ convergence, nonnegative right-continuous
limit, common exponential clock, and the genuine total entropy mass bound. -/
theorem actual_Fisher_subsequence {p : ℕ} (hp : 2≤p) {β : ℝ} (hβ : 0≤β)
    (E : ∀ n : ℕ,FisherDensity (n+2) p β) :
    ∃ (φ : ℕ → ℕ) (aF : ℝ → ℝ),StrictMono φ ∧
      (∀ t,0≤aF t) ∧
      (∀ t,aF t≤Real.exp (ceilingRate p β (cutoff p)*t)*(β^2*(p : ℝ))) ∧
      (∀ t,ContinuousWithinAt aF (Ici t) t) ∧
      Antitone (fun t => Real.exp (-ceilingRate p β (cutoff p)*t)*aF t) ∧
      IntegrableOn aF (Ioi 0) ∧ (∫ t in Ioi 0,aF t)≤β^2/2 ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ t in Ioc 0 T,|(E (φ n)).full t-aF t|) atTop (𝓝 0)) := by
  obtain ⟨φ,g,hφ,hgm,hgb,hgc,hae,_⟩ := actual_clock_Helly hp hβ E
  let K : ℝ := ceilingRate p β (cutoff p)
  let B : ℝ := β^2*(p : ℝ)
  let aF (t : ℝ) := Real.exp (K*t)*g t
  have hK : 0≤K := by
    have hc : 0≤cutoff p := by
      unfold cutoff
      linarith [GaussianLandscape.landscapeThreshold_pos p]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) (sq_nonneg _)) hc
  have hB : 0≤B := by unfold B; positivity
  have hExp : Continuous (fun t : ℝ => Real.exp (K*t)) := by fun_prop
  have han t : 0≤aF t := mul_nonneg (Real.exp_nonneg _) (hgb t).1
  have hab t : aF t≤Real.exp (K*t)*B :=
    mul_le_mul_of_nonneg_left (hgb t).2 (Real.exp_nonneg _)
  have hgInt n : IntegrableOn (E n).good (Ioi 0) :=
    ((E n).event_budget (by omega) (by omega) hβ _ (goodEvent_measurable (n+2) p (cutoff p))).1
  have hgMass n : (∫ t in Ioi 0,(E n).good t)≤β^2/2 :=
    ((E n).event_budget (by omega) (by omega) hβ _ (goodEvent_measurable (n+2) p (cutoff p))).2
  have hgAE : ∀ᵐ t ∂volume.restrict (Ioi 0),
      Tendsto (fun n => (E (φ n)).good t) atTop (𝓝 (aF t)) := by
    filter_upwards [ae_restrict_of_ae hae,ae_restrict_mem measurableSet_Ioi] with t ht htpos
    convert ht.const_mul (Real.exp (K*t)) using 1
    · funext n
      exact (E (φ n)).good_eq_exp_clock htpos.le
  have haBudget : IntegrableOn aF (Ioi 0) ∧ (∫ t in Ioi 0,aF t)≤β^2/2 :=
    MonotoneHelly.nonnegative_ae_limit_budget (by positivity) (fun n => hgInt (φ n))
      (fun n t => goodFisher_nonneg β (cutoff p) (E (φ n)).positive t)
      han (fun n => hgMass (φ n)) hgAE
  have hbadInt n := ((E n).bad_mass_bound (by omega) (by omega) hβ).1
  have hbadZero : Tendsto (fun n => ∫ t in Ioi 0,(E (φ n)).bad t) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => φ n+2) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right (φ n) 2) hφ.tendsto_atTop
    have he : Tendsto (fun n => Real.exp (-((φ n+2 : ℕ) : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.comp hn))
    have hs := ((Real.continuous_sqrt.tendsto 0).comp he).const_mul
      (2*β*Real.sqrt (momentCeiling p 2))
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg ((E (φ n)).bad_nonneg))
      (Eventually.of_forall fun n => ((E (φ n)).bad_mass_bound (by omega) (by omega) hβ).2)
    simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using hs
  refine ⟨φ,aF,hφ,han,hab,fun t => hExp.continuousWithinAt.mul (hgc t),?_,haBudget.1,haBudget.2,?_⟩
  · convert hgm using 1
    funext t
    dsimp only [aF,K]
    rw [← mul_assoc,← Real.exp_add]
    simp
  · intro T
    have hgoodZero := MonotoneHelly.exponential_L1loc hK hB
      (fun n => ((E (φ n)).clock_antitone (by omega) hp hβ).measurable) hgm.measurable
      (fun n t => (E (φ n)).clock_bounds (by omega) hp hβ t) hgb hae T
    have hgoodEq n : (∫ t in Ioc 0 T,|(E (φ n)).good t-aF t|)=
        (∫ t in Ioc 0 T,|Real.exp (K*t)*(E (φ n)).clock t-Real.exp (K*t)*g t|) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [(E (φ n)).good_eq_exp_clock ht.1.le]
    have hgoodZero' : Tendsto (fun n => ∫ t in Ioc 0 T,|(E (φ n)).good t-aF t|) atTop (𝓝 0) := by
      simpa only [hgoodEq] using hgoodZero
    have hlocal : Ioc (0 : ℝ) T⊆Ioi 0 := fun _ ht => ht.1
    have hbound n : (∫ t in Ioc 0 T,|(E (φ n)).full t-aF t|)≤
        (∫ t in Ioi 0,(E (φ n)).bad t)+(∫ t in Ioc 0 T,|(E (φ n)).good t-aF t|) := by
      have hfInt := ((E (φ n)).full_budget (by omega) (by omega) hβ).1.mono_set hlocal
      have haInt := haBudget.1.mono_set hlocal
      have hdInt := ((hgInt (φ n)).mono_set hlocal).sub haInt
      have hbInt := (hbadInt (φ n)).mono_set hlocal
      have hmono : (∫ t in Ioc 0 T,|(E (φ n)).full t-aF t|)≤
          (∫ t in Ioc 0 T,(E (φ n)).bad t+|(E (φ n)).good t-aF t|) := by
        apply integral_mono_ae ((hfInt.sub haInt).abs) (hbInt.add hdInt.abs)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        change |(E (φ n)).full t-aF t|≤(E (φ n)).bad t+|(E (φ n)).good t-aF t|
        rw [(E (φ n)).full_eq_good_add_bad (by omega) hp hβ ht.1.le]
        have hh := abs_add_le ((E (φ n)).bad t) ((E (φ n)).good t-aF t)
        rw [abs_of_nonneg ((E (φ n)).bad_nonneg t)] at hh
        have he : (E (φ n)).good t+(E (φ n)).bad t-aF t=
            (E (φ n)).bad t+((E (φ n)).good t-aF t) := by ring
        rw [he]
        exact hh
      rw [integral_add (f := fun t => (E (φ n)).bad t)
        (g := fun t => |(E (φ n)).good t-aF t|) hbInt hdInt.abs] at hmono
      have htail := setIntegral_mono_set (hbadInt (φ n))
        (ae_of_all _ ((E (φ n)).bad_nonneg)) (ae_of_all volume hlocal)
      exact hmono.trans (add_le_add htail (le_refl _))
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun t => abs_nonneg _)
      (Eventually.of_forall hbound)
    simpa only [add_zero] using hbadZero.add hgoodZero'

end SphericalAging.SphereFisherHelly
