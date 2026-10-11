module

public import SphericalAging.SphereFisherHelly

public section

/-! Functional compactness data for actual Fisher families. This interface
contains only normalized Fisher values, genuine budgets and clocks; it does
not require an ambient positive forward density or ambient time PDE.
The concrete actual-density constructor is supplied separately. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SphericalAging.SphereFisherCompactData
open MeasureTheory Set Filter FiniteModel SphereRotationGeometry
open GaussianLandscape GaussianLandscapeMoments SphereGoodEventFisherClock
open SphereBadEventFisherMass
open scoped Topology

structure FisherCompactData (N p : ℕ) (β : ℝ) where
  full : ℝ→ℝ
  good : ℝ→ℝ
  bad : ℝ→ℝ
  clock : ℝ→ℝ
  full_nonneg : ∀t,0≤full t
  good_nonneg : ∀t,0≤good t
  bad_nonneg : ∀t,0≤bad t
  full_eq_good_add_bad : ∀{t},0≤t→full t=good t+bad t
  full_integrable : IntegrableOn full (Ioi 0)
  good_integrable : IntegrableOn good (Ioi 0)
  good_mass : (∫t in Ioi 0,good t)≤β^2/2
  bad_integrable : IntegrableOn bad (Ioi 0)
  bad_mass : (∫t in Ioi 0,bad t)≤
    2*β*Real.sqrt (momentCeiling p 2)*Real.sqrt (Real.exp (-(N:ℝ)))
  clock_antitone : Antitone clock
  clock_bounds : ∀t,0≤clock t ∧ clock t≤β^2*(p:ℝ)
  good_eq_exp_clock : ∀{t},0≤t→good t=Real.exp (ceilingRate p β (cutoff p)*t)*clock t

/-- The actual dimension family has one genuine rational/Helly subsequence;
the good-event Fisher limit is right-continuous and has the common clock. -/
theorem compact_clock_Helly {p : ℕ} (hp : 2≤p) {β : ℝ} (hβ : 0≤β)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (E : ∀n,FisherCompactData (dim n) p β) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ),StrictMono φ ∧ Antitone g ∧
      (∀ t,0≤g t ∧ g t≤β^2*(p : ℝ)) ∧ (∀ t,ContinuousWithinAt g (Ici t) t) ∧
      (∀ᵐ t ∂volume,Tendsto (fun n => (E (φ n)).clock t) atTop (𝓝 (g t))) ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ t in Ioc 0 T,|(E (φ n)).clock t-g t|) atTop (𝓝 0)) := by
  exact MonotoneHelly.subsequence_L1loc
    (fun n => (E n).clock_antitone)
    (fun n t => (E n).clock_bounds t)

/-- The constructed limit of the literal full annealed Fisher information:
one dimension subsequence, local L¹ convergence, nonnegative right-continuous
limit, common exponential clock, and the genuine total entropy mass bound. -/
theorem compact_Fisher_subsequence {p : ℕ} (hp : 2≤p) {β : ℝ} (hβ : 0≤β)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (E : ∀n,FisherCompactData (dim n) p β) :
    ∃ (φ : ℕ → ℕ) (aF : ℝ → ℝ),StrictMono φ ∧
      (∀ t,0≤aF t) ∧
      (∀ t,aF t≤Real.exp (ceilingRate p β (cutoff p)*t)*(β^2*(p : ℝ))) ∧
      (∀ t,ContinuousWithinAt aF (Ici t) t) ∧
      Antitone (fun t => Real.exp (-ceilingRate p β (cutoff p)*t)*aF t) ∧
      IntegrableOn aF (Ioi 0) ∧ (∫ t in Ioi 0,aF t)≤β^2/2 ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ t in Ioc 0 T,|(E (φ n)).full t-aF t|) atTop (𝓝 0)) := by
  obtain ⟨φ,g,hφ,hgm,hgb,hgc,hae,_⟩ := compact_clock_Helly hp hβ dim hdim E
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
    (E n).good_integrable
  have hgMass n : (∫ t in Ioi 0,(E n).good t)≤β^2/2 :=
    (E n).good_mass
  have hgAE : ∀ᵐ t ∂volume.restrict (Ioi 0),
      Tendsto (fun n => (E (φ n)).good t) atTop (𝓝 (aF t)) := by
    filter_upwards [ae_restrict_of_ae hae,ae_restrict_mem measurableSet_Ioi] with t ht htpos
    convert ht.const_mul (Real.exp (K*t)) using 1
    · funext n
      exact (E (φ n)).good_eq_exp_clock htpos.le
  have haBudget : IntegrableOn aF (Ioi 0) ∧ (∫ t in Ioi 0,aF t)≤β^2/2 :=
    MonotoneHelly.nonnegative_ae_limit_budget (by positivity) (fun n => hgInt (φ n))
      (fun n t => (E (φ n)).good_nonneg t)
      han (fun n => hgMass (φ n)) hgAE
  have hbadInt n := (E n).bad_integrable
  have hbadZero : Tendsto (fun n => ∫ t in Ioi 0,(E (φ n)).bad t) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => dim (φ n)) atTop atTop := hdim.comp hφ.tendsto_atTop
    have he : Tendsto (fun n => Real.exp (-((dim (φ n) : ℕ) : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.comp hn))
    have hs := ((Real.continuous_sqrt.tendsto 0).comp he).const_mul
      (2*β*Real.sqrt (momentCeiling p 2))
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg ((E (φ n)).bad_nonneg))
      (Eventually.of_forall fun n => (E (φ n)).bad_mass)
    simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using hs
  refine ⟨φ,aF,hφ,han,hab,fun t => hExp.continuousWithinAt.mul (hgc t),?_,haBudget.1,haBudget.2,?_⟩
  · convert hgm using 1
    funext t
    dsimp only [aF,K]
    rw [← mul_assoc,← Real.exp_add]
    simp
  · intro T
    have hgoodZero := MonotoneHelly.exponential_L1loc hK hB
      (fun n => ((E (φ n)).clock_antitone).measurable) hgm.measurable
      (fun n t => (E (φ n)).clock_bounds t) hgb hae T
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
      have hfInt := (E (φ n)).full_integrable.mono_set hlocal
      have haInt := haBudget.1.mono_set hlocal
      have hdInt := ((hgInt (φ n)).mono_set hlocal).sub haInt
      have hbInt := (hbadInt (φ n)).mono_set hlocal
      have hmono : (∫ t in Ioc 0 T,|(E (φ n)).full t-aF t|)≤
          (∫ t in Ioc 0 T,(E (φ n)).bad t+|(E (φ n)).good t-aF t|) := by
        apply integral_mono_ae ((hfInt.sub haInt).abs) (hbInt.add hdInt.abs)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        change |(E (φ n)).full t-aF t|≤(E (φ n)).bad t+|(E (φ n)).good t-aF t|
        rw [(E (φ n)).full_eq_good_add_bad ht.1.le]
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


end SphericalAging.SphereFisherCompactData
