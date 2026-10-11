module

public import SphericalAging.SphereFisherHelly

public section

/-! Genuine Fisher Helly extraction along an arbitrary preceding diverging
sequence of dimensions, so it can refine the source 5.1 CK subsequence. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFisherSubsequence
open MeasureTheory Set Filter FiniteModel SphereInitialLaw SphereFisherHelly
open SphereGoodEventFisherClock SphereBadEventFisherMass GaussianLandscapeMoments
open scoped Topology

/-- The constructed limit of the literal full annealed Fisher information:
one dimension subsequence, local L¹ convergence, nonnegative right-continuous
limit, common exponential clock, and the genuine total entropy mass bound. -/
theorem actual_Fisher_subsequence_dimensions {p : ℕ} (hp : 2≤p) {β : ℝ} (hβ : 0≤β)
    (dim : ℕ → ℕ) (hDim : ∀ n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (E : ∀ n : ℕ,FisherDensity (dim n) p β) :
    ∃ (φ : ℕ → ℕ) (aF : ℝ → ℝ),StrictMono φ ∧
      (∀ t,0≤aF t) ∧
      (∀ t,aF t≤Real.exp (ceilingRate p β (cutoff p)*t)*(β^2*(p : ℝ))) ∧
      (∀ t,ContinuousWithinAt aF (Ici t) t) ∧
      Antitone (fun t => Real.exp (-ceilingRate p β (cutoff p)*t)*aF t) ∧
      IntegrableOn aF (Ioi 0) ∧ (∫ t in Ioi 0,aF t)≤β^2/2 ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ t in Ioc 0 T,|(E (φ n)).full t-aF t|) atTop (𝓝 0)) := by
  have hN n : 0<dim n := lt_of_lt_of_le (by norm_num : 0<2) (hDim n)
  obtain ⟨φ,g,hφ,hgm,hgb,hgc,hae,_⟩ := MonotoneHelly.subsequence_L1loc
    (fun n => (E n).clock_antitone (hN n) hp hβ)
    (fun n s => (E n).clock_bounds (hN n) hp hβ s)
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
    ((E n).event_budget (hN n) (by omega) hβ _ (goodEvent_measurable (dim n) p (cutoff p))).1
  have hgMass n : (∫ t in Ioi 0,(E n).good t)≤β^2/2 :=
    ((E n).event_budget (hN n) (by omega) hβ _ (goodEvent_measurable (dim n) p (cutoff p))).2
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
  have hbadInt n := ((E n).bad_mass_bound (hDim n) (by omega) hβ).1
  have hbadZero : Tendsto (fun n => ∫ t in Ioi 0,(E (φ n)).bad t) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => dim (φ n)) atTop atTop := hTop.comp hφ.tendsto_atTop
    have he : Tendsto (fun n => Real.exp (-((dim (φ n) : ℕ) : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.comp hn))
    have hs := ((Real.continuous_sqrt.tendsto 0).comp he).const_mul
      (2*β*Real.sqrt (momentCeiling p 2))
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg ((E (φ n)).bad_nonneg))
      (Eventually.of_forall fun n => ((E (φ n)).bad_mass_bound (hDim (φ n)) (by omega) hβ).2)
    simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using hs
  refine ⟨φ,aF,hφ,han,hab,fun t => hExp.continuousWithinAt.mul (hgc t),?_,haBudget.1,haBudget.2,?_⟩
  · convert hgm using 1
    funext t
    dsimp only [aF,K]
    rw [← mul_assoc,← Real.exp_add]
    simp
  · intro T
    have hgoodZero := MonotoneHelly.exponential_L1loc hK hB
      (fun n => ((E (φ n)).clock_antitone (hN (φ n)) hp hβ).measurable) hgm.measurable
      (fun n t => (E (φ n)).clock_bounds (hN (φ n)) hp hβ t) hgb hae T
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
      have hfInt := ((E (φ n)).full_budget (hN (φ n)) (by omega) hβ).1.mono_set hlocal
      have haInt := haBudget.1.mono_set hlocal
      have hdInt := ((hgInt (φ n)).mono_set hlocal).sub haInt
      have hbInt := (hbadInt (φ n)).mono_set hlocal
      have hmono : (∫ t in Ioc 0 T,|(E (φ n)).full t-aF t|)≤
          (∫ t in Ioc 0 T,(E (φ n)).bad t+|(E (φ n)).good t-aF t|) := by
        apply integral_mono_ae ((hfInt.sub haInt).abs) (hbInt.add hdInt.abs)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        change |(E (φ n)).full t-aF t|≤(E (φ n)).bad t+|(E (φ n)).good t-aF t|
        rw [(E (φ n)).full_eq_good_add_bad (hN (φ n)) hp hβ ht.1.le]
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

end SphericalAging.SphereFisherSubsequence
