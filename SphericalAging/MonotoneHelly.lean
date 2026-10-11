module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Instances.Rat
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-! Genuine Helly extraction for uniformly bounded antitone real functions.
The subsequence is obtained from compactness of the countable rational product;
the right-continuous representative and local L¹ convergence are constructed. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.MonotoneHelly
open Set Filter MeasureTheory
open scoped Topology

/-- Simultaneous convergence at every rational point, with one actual strictly
increasing subsequence. -/
theorem rational_subsequence {f : ℕ → ℝ → ℝ} {B : ℝ}
    (hb : ∀ n x,0≤f n x ∧ f n x≤B) :
    ∃ (φ : ℕ → ℕ) (g : ℚ → ℝ),StrictMono φ ∧
      (∀ q,0≤g q ∧ g q≤B) ∧
      (∀ q : ℚ,Tendsto (fun n => f (φ n) (q : ℝ)) atTop (𝓝 (g q))) := by
  have hc : IsCompact {g : ℚ → ℝ | ∀ q,g q∈Icc 0 B} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨g,hg,φ,hφ,ht⟩ := hc.tendsto_subseq (x := fun n (q : ℚ) => f n (q : ℝ))
    (fun n q => hb n (q : ℝ))
  refine ⟨φ,g,hφ,hg,fun q => ?_⟩
  exact (continuous_apply q).tendsto g |>.comp ht

theorem limsup_antitone {f : ℕ → ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n,Antitone (f n)) (hb : ∀ n x,0≤f n x ∧ f n x≤B) :
    Antitone (fun x => limsup (fun n => f n x) atTop) := by
  intro x y hxy
  exact limsup_le_limsup (Eventually.of_forall fun n => hmono n hxy)
    (isCoboundedUnder_le_of_le atTop fun n => (hb n y).1)
    (isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hb n x).2))

theorem limsup_bounds {f : ℕ → ℝ → ℝ} {B : ℝ}
    (hb : ∀ n x,0≤f n x ∧ f n x≤B) (x : ℝ) :
    0≤limsup (fun n => f n x) atTop ∧ limsup (fun n => f n x) atTop≤B := by
  have hbd : atTop.IsBoundedUnder (· ≤ ·) (fun n => f n x) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hb n x).2)
  refine ⟨le_limsup_of_le hbd ?_,limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop fun n => (hb n x).1)
    (Eventually.of_forall fun n => (hb n x).2)⟩
  intro b hh
  obtain ⟨n,hn⟩ := hh.exists
  exact (hb n x).1.trans hn

/-- Rational convergence and monotonicity imply convergence at every
continuity point of the actual limsup function. -/
theorem tendsto_at_continuity {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hmono : ∀ n,Antitone (f n))
    (hrat : ∀ q : ℚ,Tendsto (fun n => f n (q : ℝ)) atTop (𝓝 (g q)))
    {x : ℝ} (hc : ContinuousAt g x) :
    Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨l,u,hx,hU⟩ := (hc.eventually (lt_mem_nhds ha)).exists_Ioo_subset
    obtain ⟨q,hxq,hqu⟩ := exists_rat_btwn hx.2
    have haq : a<g (q : ℝ) := hU ⟨hx.1.trans hxq,hqu⟩
    exact ((hrat q).eventually (lt_mem_nhds haq)).mono fun n hn =>
      hn.trans_le (hmono n hxq.le)
  · intro a ha
    obtain ⟨l,u,hx,hU⟩ := (hc.eventually (gt_mem_nhds ha)).exists_Ioo_subset
    obtain ⟨q,hlq,hqx⟩ := exists_rat_btwn hx.1
    have hqa : g (q : ℝ)<a := hU ⟨hlq,hqx.trans hx.2⟩
    exact ((hrat q).eventually (gt_mem_nhds hqa)).mono fun n hn =>
      (hmono n hqx.le).trans_lt hn

/-- Helly's subsequence with the constructed right-continuous antitone
representative and almost-everywhere convergence under Lebesgue measure. -/
theorem subsequence_ae_rightContinuous {f : ℕ → ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n,Antitone (f n)) (hb : ∀ n x,0≤f n x ∧ f n x≤B) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ),StrictMono φ ∧ Antitone g ∧
      (∀ x,0≤g x ∧ g x≤B) ∧ (∀ x,ContinuousWithinAt g (Ici x) x) ∧
      (∀ᵐ x ∂volume,Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x))) := by
  obtain ⟨φ,r,hφ,_,hr⟩ := rational_subsequence hb
  let b (x : ℝ) := limsup (fun n => f (φ n) x) atTop
  have hbm : Antitone b := limsup_antitone (fun n => hmono (φ n)) (fun n x => hb (φ n) x)
  have hbb (x : ℝ) : 0≤b x ∧ b x≤B := limsup_bounds (fun n x => hb (φ n) x) x
  have hrat (q : ℚ) : Tendsto (fun n => f (φ n) (q : ℝ)) atTop (𝓝 (b q)) := by
    have he : b (q : ℝ)=r q := (hr q).limsup_eq
    rw [he]
    exact hr q
  refine ⟨φ,b.rightLim,hφ,hbm.rightLim,?_,?_,?_⟩
  · intro x
    exact isClosed_Icc.mem_of_tendsto (hbm.tendsto_rightLim x)
      (Eventually.of_forall fun y => hbb y)
  · intro x
    exact continuousWithinAt_rightLim_Ici (hbm.tendsto_rightLim x)
  · have hnull : volume {x | ¬ContinuousAt b x}=0 := hbm.countable_not_continuousAt.measure_zero volume
    have hae : ∀ᵐ x ∂volume,ContinuousAt b x := by
      simpa only [ae_iff,not_not] using hnull
    filter_upwards [hae] with x hx
    have he : b.rightLim x=b x := hx.continuousWithinAt.rightLim_eq
    rw [he]
    exact tendsto_at_continuity (fun n => hmono (φ n)) hrat hx

/-- The same subsequence converges locally in L¹, with the literal integral
of absolute differences. -/
theorem subsequence_L1loc {f : ℕ → ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n,Antitone (f n)) (hb : ∀ n x,0≤f n x ∧ f n x≤B) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ),StrictMono φ ∧ Antitone g ∧
      (∀ x,0≤g x ∧ g x≤B) ∧ (∀ x,ContinuousWithinAt g (Ici x) x) ∧
      (∀ᵐ x ∂volume,Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x))) ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ t in Ioc 0 T,|f (φ n) t-g t|) atTop (𝓝 0)) := by
  obtain ⟨φ,g,hφ,hgm,hgb,hgc,hae⟩ := subsequence_ae_rightContinuous hmono hb
  refine ⟨φ,g,hφ,hgm,hgb,hgc,hae,fun T => ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc 0 T))
    (F := fun n t => |f (φ n) t-g t|) (f := fun _ => (0 : ℝ)) (fun _ => 2*B)
    (fun n => (continuous_abs.measurable.comp
      ((hmono (φ n)).measurable.sub hgm.measurable)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs,abs_abs]
      exact abs_sub_le_iff.mpr ⟨by linarith [(hb (φ n) t).1,(hb (φ n) t).2,(hgb t).1,(hgb t).2],
        by linarith [(hb (φ n) t).1,(hb (φ n) t).2,(hgb t).1,(hgb t).2]⟩)
    (by
      filter_upwards [ae_restrict_of_ae hae] with t ht
      simpa only [sub_self,abs_zero] using (ht.sub_const (g t)).abs)
  simpa only [integral_zero] using ht

/-- Undoing a fixed exponential clock preserves local L¹ convergence. -/
theorem exponential_L1loc {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B K : ℝ}
    (hK : 0≤K) (hB : 0≤B)
    (hm : ∀ n,Measurable (f n)) (hgm : Measurable g)
    (hb : ∀ n t,0≤f n t ∧ f n t≤B) (hgb : ∀ t,0≤g t ∧ g t≤B)
    (hae : ∀ᵐ t ∂volume,Tendsto (fun n => f n t) atTop (𝓝 (g t))) (T : ℝ) :
    Tendsto (fun n => ∫ t in Ioc 0 T,|Real.exp (K*t)*f n t-Real.exp (K*t)*g t|)
      atTop (𝓝 0) := by
  have hExp : Continuous (fun t : ℝ => Real.exp (K*t)) := by fun_prop
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc 0 T))
    (F := fun n t => |Real.exp (K*t)*f n t-Real.exp (K*t)*g t|)
    (f := fun _ => (0 : ℝ)) (fun _ => Real.exp (K*max T 0)*(2*B))
    (fun n => (continuous_abs.measurable.comp
      ((hExp.measurable.mul (hm n)).sub (hExp.measurable.mul hgm))).aestronglyMeasurable)
    (integrable_const _)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs,abs_abs,← mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (K*t)≤Real.exp (K*max T 0) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ht.2.trans (le_max_left T 0)) hK)
      have hs : |f n t-g t|≤2*B := abs_sub_le_iff.mpr
        ⟨by linarith [(hb n t).1,(hb n t).2,(hgb t).1,(hgb t).2],
         by linarith [(hb n t).1,(hb n t).2,(hgb t).1,(hgb t).2]⟩
      exact mul_le_mul he hs (abs_nonneg _) (Real.exp_nonneg _))
    (by
      filter_upwards [ae_restrict_of_ae hae] with t ht
      simpa only [sub_self,abs_zero] using
        (((ht.const_mul (Real.exp (K*t))).sub_const (Real.exp (K*t)*g t)).abs))
  simpa only [integral_zero] using ht

/-- Fatou's lemma gives the true total mass bound of a nonnegative
almost-everywhere limit, including its integrability. -/
theorem nonnegative_ae_limit_budget {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {μ : Measure ℝ}
    {C : ℝ} (hC : 0≤C) (hi : ∀ n,Integrable (F n) μ)
    (hn : ∀ n t,0≤F n t) (hfn : ∀ t,0≤f t)
    (hb : ∀ n,(∫ t,F n t ∂μ)≤C)
    (hae : ∀ᵐ t ∂μ,Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    Integrable f μ ∧ (∫ t,f t ∂μ)≤C := by
  have hnorm n : (∫ t,‖F n t‖ ∂μ)=(∫ t,F n t ∂μ) := by
    apply integral_congr_ae
    exact ae_of_all _ fun t => Real.norm_of_nonneg (hn n t)
  have hb' n : (∫⁻ t,‖F n t‖ₑ ∂μ)≤ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi n),hnorm n]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hlim : liminf (fun n => ∫⁻ t,‖F n t‖ₑ ∂μ) atTop≤ENNReal.ofReal C :=
    liminf_le_of_frequently_le' (Eventually.of_forall hb').frequently
  have hfi : Integrable f μ := integrable_of_tendsto hae (fun n => (hi n).aestronglyMeasurable)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  refine ⟨hfi,?_⟩
  have hfat := (lintegral_enorm_le_liminf_of_tendsto hae
    (fun n => (hi n).aestronglyMeasurable.aemeasurable.enorm)).trans hlim
  have hfnorm : (∫ t,‖f t‖ ∂μ)=(∫ t,f t ∂μ) :=
    integral_congr_ae (ae_of_all _ fun t => Real.norm_of_nonneg (hfn t))
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi,hfnorm] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hfat

end SphericalAging.MonotoneHelly
