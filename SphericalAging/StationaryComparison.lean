module

public import SphericalAging.StationaryNormalization
public import SphericalAging.IntervalGronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

public section

/-!
# Comparison for locally absolutely continuous Volterra profiles

Actual a.e. derivatives and Lebesgue convolutions are used throughout.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryComparison

noncomputable section

/-- Reflection of an absolutely continuous function preserves absolute
continuity, with the interval reflected as well. -/
theorem absolutelyContinuous_reflect (f : ℝ → ℝ) (a b c : ℝ)
    (hf : AbsolutelyContinuousOnInterval f (c - b) (c - a)) :
    AbsolutelyContinuousOnInterval (fun t => f (c - t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlength
  let F : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => (c - (E.2 i).2, c - (E.2 i).1))
  have hinterval (x : ℝ) : x ∈ uIcc a b → c - x ∈ uIcc (c - b) (c - a) := by
    simp only [mem_uIcc]
    intro hx
    rcases hx with hx | hx <;> [left; right] <;> constructor <;> linarith
  have hF : F ∈ AbsolutelyContinuousOnInterval.disjWithin (c - b) (c - a) := by
    refine ⟨fun i hi => ⟨hinterval _ (hE.1 i hi).2, hinterval _ (hE.1 i hi).1⟩, ?_⟩
    intro i hi j hj hij
    have hd := hE.2 hi hj hij
    simp only [F, uIoc, Function.onFun] at hd ⊢
    rw [Ioc_disjoint_Ioc] at hd ⊢
    simp only [min_sub_sub_left, max_sub_sub_left]
    rw [min_comm (E.2 i).2 (E.2 i).1, min_comm (E.2 j).2 (E.2 j).1,
      max_comm (E.2 i).2 (E.2 i).1, max_comm (E.2 j).2 (E.2 j).1]
    linarith
  have hlengthF : ∑ i ∈ Finset.range F.1, dist (F.2 i).1 (F.2 i).2 < δ := by
    convert hlength using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [F, Real.dist_eq]
    congr 1
    ring
  have hbound := hcontrol F hF hlengthF
  simpa only [F, dist_comm] using hbound

/-- The Volterra integration-by-parts identity for genuine absolutely
continuous functions, including kernels whose derivatives are only L¹. -/
theorem convolution_integration_by_parts (f g : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : AbsolutelyContinuousOnInterval f 0 t)
    (hg : AbsolutelyContinuousOnInterval g 0 t) :
    (∫ s in 0..t, f (t - s) * deriv g s) =
      f 0 * g t - f t * g 0 + ∫ s in 0..t, deriv f (t - s) * g s := by
  have hfr : AbsolutelyContinuousOnInterval (fun s => f (t - s)) 0 t := by
    apply absolutelyContinuous_reflect
    simpa using hf
  have hdiff : ∀ᵐ s ∂volume, s ∈ uIcc 0 t →
      deriv (fun z => f (t - z)) s = -deriv f (t - s) := by
    have ha := (volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae hf.ae_differentiableAt
    filter_upwards [ha] with s hs hsint
    have his : t - s ∈ uIcc 0 t := by
      rw [uIcc_of_le ht] at hsint ⊢
      constructor <;> linarith [hsint.1, hsint.2]
    have hc := (hs his).hasDerivAt.comp s ((hasDerivAt_id s).const_sub t)
    have hd : HasDerivAt (fun z => f (t - z)) (-deriv f (t - s)) s := by
      convert hc using 1 <;> simp [Function.comp_def]
    exact hd.deriv
  have hidentity := hfr.integral_mul_deriv_eq_deriv_mul hg
  simp only [sub_self, sub_zero] at hidentity
  rw [hidentity]
  have hei : (∫ s in 0..t, deriv (fun z => f (t - z)) s * g s) =
      -(∫ s in 0..t, deriv f (t - s) * g s) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdiff] with s hs his
    rw [hs (uIoc_subset_uIcc his)]
    ring
  rw [hei]
  ring

/-- Negative part as an actual real function. -/
@[expose] def negativePart (w : ℝ → ℝ) (t : ℝ) : ℝ := max (-w t) 0

theorem negativePart_absolutelyContinuous (w : ℝ → ℝ) (a b : ℝ)
    (hw : AbsolutelyContinuousOnInterval w a b) :
    AbsolutelyContinuousOnInterval (negativePart w) a b := by
  exact (LipschitzWith.id.neg.max_const 0).comp_absolutelyContinuousOnInterval hw

/-- A negative-part differential estimate uses actual derivatives. At a
zero of w the negative part has a minimum, so any existing derivative is zero. -/
theorem negativePart_deriv_le (w : ℝ → ℝ) (t b H : ℝ) (hb : 0 ≤ b) (hH : 0 ≤ H)
    (hw : DifferentiableAt ℝ w t)
    (hineq : -H ≤ deriv w t + b * w t) :
    deriv (negativePart w) t ≤ H := by
  rcases lt_trichotomy (w t) 0 with hneg | hzero | hpos
  · have heq : negativePart w =ᶠ[𝓝 t] (fun s => -w s) := by
      filter_upwards [hw.continuousAt.eventually (Iio_mem_nhds hneg)] with s hs
      exact max_eq_left (by linarith : 0 ≤ -w s)
    have hd : deriv (negativePart w) t = -deriv w t := by
      rw [heq.deriv_eq]
      convert hw.hasDerivAt.neg.deriv using 1
    rw [hd]
    have hmul : b * w t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hneg.le
    linarith
  · have hmin : IsLocalMin (negativePart w) t := by
      show ∀ᶠ s in 𝓝 t, negativePart w t ≤ negativePart w s
      filter_upwards with s
      simp only [negativePart, hzero, neg_zero, max_self]
      exact le_max_right _ _
    rw [hmin.deriv_eq_zero]
    exact hH
  · have heq : negativePart w =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hw.continuousAt.eventually (Ioi_mem_nhds hpos)] with s hs
      exact max_eq_right (by linarith : -w s ≤ 0)
    rw [heq.deriv_eq, deriv_const]
    exact hH

/-- Actual derivatives have the right sign even at the boundary of the
nonnegative ray. Outside differentiability their totalized value is zero. -/
theorem antitoneOn_deriv_nonpos (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 0))
    (t : ℝ) (ht : 0 ≤ t) : deriv f t ≤ 0 := by
  by_cases hd : DifferentiableAt ℝ f t
  · rw [← hd.derivWithin (uniqueDiffOn_Ici _ t ht)]
    exact hf.derivWithin_nonpos
  · rw [deriv_zero_of_not_differentiableAt hd]

/-- Tonelli/Fubini bound for causal convolution on a finite interval.
Both factors are genuine locally integrable functions; no convolution
bound is an input. -/
theorem causalConvolution_integral_le (f k : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hfi : IntervalIntegrable f volume 0 T) (hki : IntervalIntegrable k volume 0 T)
    (hfn : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hkn : ∀ t ∈ Icc 0 T, 0 ≤ k t) :
    IntervalIntegrable (StationaryNormalization.causalConvolution f k) volume 0 T ∧
      (∫ t in 0..T, StationaryNormalization.causalConvolution f k t) ≤
        (∫ t in 0..T, k t) * (∫ t in 0..T, f t) := by
  let F := (Icc 0 T).indicator f
  let K := (Icc 0 T).indicator k
  let H := MeasureTheory.convolution K F (ContinuousLinearMap.mul ℝ ℝ) volume
  have hF : Integrable F volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hfi)
  have hK : Integrable K volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hki)
  have hFn (t : ℝ) : 0 ≤ F t := by
    by_cases ht : t ∈ Icc 0 T
    · simpa [F, ht] using hfn t ht
    · simp [F, ht]
  have hKn (t : ℝ) : 0 ≤ K t := by
    by_cases ht : t ∈ Icc 0 T
    · simpa [K, ht] using hkn t ht
    · simp [K, ht]
  have hH : Integrable H volume := (hK.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hF).integral_prod_left
  have hHn (t : ℝ) : 0 ≤ H t := by
    apply integral_nonneg
    intro s
    exact mul_nonneg (hKn s) (hFn (t - s))
  have heq (t : ℝ) (ht : t ∈ Icc 0 T) : H t =
      StationaryNormalization.causalConvolution f k t := by
    have hins : (fun s => K s * F (t - s)) =
        (Icc 0 t).indicator (fun s => f (t - s) * k s) := by
      funext s
      by_cases hs : s ∈ Icc 0 t
      · have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
        have hts : t - s ∈ Icc 0 T := ⟨sub_nonneg.mpr hs.2, by linarith [hs.1, ht.2]⟩
        simp only [F, K, indicator_of_mem hsT, indicator_of_mem hts, indicator_of_mem hs]
        ring
      · rw [indicator_of_notMem hs]
        rcases not_and_or.mp hs with hlow | hhigh
        · have hns : s ∉ Icc 0 T := fun h => hlow h.1
          simp [K, hns]
        · have hnts : t - s ∉ Icc 0 T := by
            intro h
            have : s ≤ t := by linarith [h.1]
            exact hhigh this
          simp [F, hnts]
    change (∫ s, K s * F (t - s)) = ∫ s in 0..t, f (t - s) * k s
    rw [hins, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le ht.1]
  have hHinterval : IntervalIntegrable H volume 0 T := hH.intervalIntegrable
  have hconv : IntervalIntegrable (StationaryNormalization.causalConvolution f k) volume 0 T :=
    hHinterval.congr (by
      intro t ht
      exact heq t (by simpa only [uIcc_of_le hT] using uIoc_subset_uIcc ht))
  refine ⟨hconv, ?_⟩
  calc
    (∫ t in 0..T, StationaryNormalization.causalConvolution f k t) = ∫ t in Icc 0 T, H t := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
      apply intervalIntegral.integral_congr
      intro t ht
      exact (heq t (by simpa only [uIcc_of_le hT] using ht)).symm
    _ ≤ ∫ t, H t := setIntegral_le_integral hH (ae_of_all volume hHn)
    _ = (∫ t, K t) * (∫ t, F t) := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hK hF
    _ = (∫ t in 0..T, k t) * (∫ t in 0..T, f t) := by
      simp only [K, F, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hT]

/-- Positivity for an AC Volterra differential inequality. Kernel masses
and the L¹ convolution estimate are proved analytically, before Gronwall. -/
theorem volterra_nonnegative (w v k : ℝ → ℝ) (T b L V K : ℝ)
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hw : AbsolutelyContinuousOnInterval w 0 T) (hw0 : w 0 = 0)
    (hv : IntervalIntegrable v volume 0 T) (hk : IntervalIntegrable k volume 0 T)
    (hvn : ∀ t ∈ Icc 0 T, 0 ≤ v t) (hkn : ∀ t ∈ Icc 0 T, 0 ≤ k t)
    (hvmass : ∀ t ∈ Icc 0 T, (∫ s in 0..t, v s) ≤ V)
    (hkmass : ∀ t ∈ Icc 0 T, (∫ s in 0..t, k s) ≤ K)
    (hineq : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      -(L * StationaryNormalization.causalConvolution (negativePart w) v t +
        StationaryNormalization.causalConvolution (negativePart w) k t) ≤
      deriv w t + b * w t) :
    ∀ t ∈ Icc 0 T, 0 ≤ w t := by
  let f := negativePart w
  have hfac : AbsolutelyContinuousOnInterval f 0 T := negativePart_absolutelyContinuous w 0 T hw
  have hfc : ContinuousOn f (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using hfac.continuousOn
  have hfn (t : ℝ) : 0 ≤ f t := le_max_right _ _
  have hf0 : f 0 = 0 := by simp [f, negativePart, hw0]
  have hgron : ∀ t ∈ Icc 0 T, f t ≤ (L * V + K) * ∫ s in 0..t, f s := by
    intro t ht
    have hsub : uIcc 0 t ⊆ uIcc 0 T := by
      simp only [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2
    have hfit : IntervalIntegrable f volume 0 t := (hfac.mono hsub).continuousOn.intervalIntegrable
    have hvt := hv.mono_set hsub
    have hkt := hk.mono_set hsub
    have hvnt : ∀ s ∈ Icc 0 t, 0 ≤ v s := fun s hs => hvn s ⟨hs.1, hs.2.trans ht.2⟩
    have hknt : ∀ s ∈ Icc 0 t, 0 ≤ k s := fun s hs => hkn s ⟨hs.1, hs.2.trans ht.2⟩
    obtain ⟨hcvi, hcvb⟩ := causalConvolution_integral_le f v t ht.1 hfit hvt
      (fun s _ => hfn s) hvnt
    obtain ⟨hcki, hckb⟩ := causalConvolution_integral_le f k t ht.1 hfit hkt
      (fun s _ => hfn s) hknt
    have hHn (s : ℝ) (hs : s ∈ Icc 0 t) : 0 ≤
        L * StationaryNormalization.causalConvolution f v s +
          StationaryNormalization.causalConvolution f k s := by
      have hcvn : 0 ≤ StationaryNormalization.causalConvolution f v s :=
        intervalIntegral.integral_nonneg hs.1 (fun z hz =>
          mul_nonneg (hfn (s - z)) (hvnt z ⟨hz.1, hz.2.trans hs.2⟩))
      have hckn : 0 ≤ StationaryNormalization.causalConvolution f k s :=
        intervalIntegral.integral_nonneg hs.1 (fun z hz =>
          mul_nonneg (hfn (s - z)) (hknt z ⟨hz.1, hz.2.trans hs.2⟩))
      exact add_nonneg (mul_nonneg hL hcvn) hckn
    have hderive : ∀ᵐ s ∂volume, s ∈ Icc 0 t → deriv f s ≤
        L * StationaryNormalization.causalConvolution f v s +
          StationaryNormalization.causalConvolution f k s := by
      filter_upwards [hw.ae_differentiableAt, hineq] with s hds hqs hs
      have his : s ∈ Icc 0 t := hs
      have hiT : s ∈ Icc 0 T := ⟨his.1, his.2.trans ht.2⟩
      exact negativePart_deriv_le w s b _ hb (hHn s his)
        (hds (by simpa only [uIcc_of_le hT] using hiT)) (hqs hiT)
    have hineqint : f t ≤ ∫ s in 0..t,
        L * StationaryNormalization.causalConvolution f v s +
          StationaryNormalization.causalConvolution f k s := by
      have hdint := intervalIntegral.integral_mono_ae_restrict ht.1
        (hfac.mono hsub).intervalIntegrable_deriv ((hcvi.const_mul L).add hcki) ((ae_restrict_iff' measurableSet_Icc).mpr hderive)
      rw [(hfac.mono hsub).integral_deriv_eq_sub, hf0, sub_zero] at hdint
      exact hdint
    have hfiNonneg : 0 ≤ ∫ s in 0..t, f s :=
      intervalIntegral.integral_nonneg ht.1 (fun s _ => hfn s)
    calc
      f t ≤ ∫ s in 0..t, L * StationaryNormalization.causalConvolution f v s +
          StationaryNormalization.causalConvolution f k s := hineqint
      _ = L * (∫ s in 0..t, StationaryNormalization.causalConvolution f v s) +
          ∫ s in 0..t, StationaryNormalization.causalConvolution f k s := by
        rw [intervalIntegral.integral_add (hcvi.const_mul L) hcki,
          intervalIntegral.integral_const_mul]
      _ ≤ L * ((∫ s in 0..t, v s) * ∫ s in 0..t, f s) +
          (∫ s in 0..t, k s) * ∫ s in 0..t, f s :=
        add_le_add (mul_le_mul_of_nonneg_left hcvb hL) hckb
      _ ≤ L * (V * ∫ s in 0..t, f s) + K * ∫ s in 0..t, f s :=
        add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hvmass t ht) hfiNonneg) hL)
          (mul_le_mul_of_nonneg_right (hkmass t ht) hfiNonneg)
      _ = (L * V + K) * ∫ s in 0..t, f s := by ring
  have hzero := IntervalGronwall.integral_gronwall_zero f T (L * V + K) hT hfc
    (fun t _ => hfn t) hgron
  intro t ht
  have hft := hzero t ht
  have hh : -w t ≤ f t := le_max_left _ _
  linarith

/-- Causal convolution commutes by the real reflected change of variables. -/
theorem causalConvolution_comm (f g : ℝ → ℝ) (t : ℝ) :
    StationaryNormalization.causalConvolution f g t =
      StationaryNormalization.causalConvolution g f t := by
  have h := intervalIntegral.integral_comp_sub_left (fun s => f (t - s) * g s) t
    (a := 0) (b := t)
  simpa only [sub_self, sub_zero, sub_sub_cancel, mul_comm,
    StationaryNormalization.causalConvolution] using h.symm

/-- Monotonicity and a Lipschitz bound give the one-sided estimate needed
for comparison. -/
theorem memory_difference_lower_bound (M : ℝ → ℝ) (L : ℝ≥0)
    (hM : MonotoneOn M (Icc 0 1)) (hLip : LipschitzOnWith L M (Icc 0 1))
    (x y : ℝ) (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    -(L : ℝ) * max (-(x - y)) 0 ≤ M x - M y := by
  by_cases hxy : y ≤ x
  · have hm := hM hy hx hxy
    have hn : 0 ≤ max (-(x - y)) 0 := le_max_right _ _
    have hln : 0 ≤ (L : ℝ) := L.coe_nonneg
    nlinarith
  · have hxy' : x < y := lt_of_not_ge hxy
    have hd := hLip.dist_le_mul x hx y hy
    rw [Real.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hxy')] at hd
    have hab := neg_abs_le (M x - M y)
    rw [max_eq_left (by linarith : 0 ≤ -(x - y))]
    nlinarith

/-- The memory kernel is derived from the actual AC composition, and
its mass is the actual FTC decrement of the memory profile. -/
theorem memory_kernel_properties (M f : ℝ → ℝ) (L : ℝ≥0)
    (hM : MonotoneOn M (Icc 0 1)) (hLip : LipschitzOnWith L M (Icc 0 1))
    (hM0 : M 0 = 0) (hf : AntitoneOn f (Ici 0))
    (hfrange : ∀ t ∈ Ici 0, f t ∈ Icc 0 1) (hf0 : f 0 = 1)
    (T : ℝ) (hT : 0 ≤ T) (hfac : AbsolutelyContinuousOnInterval f 0 T) :
    AbsolutelyContinuousOnInterval (M ∘ f) 0 T ∧
      IntervalIntegrable (fun t => -deriv (M ∘ f) t) volume 0 T ∧
      (∀ t ∈ Ici 0, 0 ≤ -deriv (M ∘ f) t) ∧
      (∀ t ∈ Icc 0 T, (∫ s in 0..t, -deriv (M ∘ f) s) ≤ M 1) := by
  have hMac : AbsolutelyContinuousOnInterval (M ∘ f) 0 T :=
    hLip.comp_absolutelyContinuousOnInterval
      (fun t ht => hfrange t (by
        rw [uIcc_of_le hT] at ht
        exact ht.1)) hfac
  have hManti : AntitoneOn (M ∘ f) (Ici 0) := by
    intro x hx y hy hxy
    exact hM (hfrange y hy) (hfrange x hx) (hf hx hy hxy)
  refine ⟨hMac, hMac.intervalIntegrable_deriv.neg,
    (fun t ht => neg_nonneg.mpr (antitoneOn_deriv_nonpos (M ∘ f) hManti t ht)), ?_⟩
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    simp only [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2
  rw [intervalIntegral.integral_neg, (hMac.mono hsub).integral_deriv_eq_sub]
  have hm : 0 ≤ M (f t) := by
    have h := hM (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (hfrange t ht.1) (hfrange t ht.1).1
    simpa only [hM0] using h
  simp only [Function.comp_def, hf0]
  linarith

/-- Residual of the actual AC profile, using its a.e. real derivative. -/
@[expose] def profileResidual (M f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t + f t + StationaryNormalization.causalConvolution (M ∘ f) (deriv f) t

/-- The exact difference equation after genuine AC integration by parts. -/
theorem residual_difference (M f g : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hfac : AbsolutelyContinuousOnInterval f 0 t)
    (hgac : AbsolutelyContinuousOnInterval g 0 t)
    (hMac : AbsolutelyContinuousOnInterval (M ∘ f) 0 t)
    (hMgac : AbsolutelyContinuousOnInterval (M ∘ g) 0 t)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hfd : DifferentiableAt ℝ f t) (hgd : DifferentiableAt ℝ g t) :
    let w := fun s => f s - g s
    let v := fun s => -deriv g s
    let k := fun s => -deriv (M ∘ f) s
    deriv w t + (1 + M 1) * w t =
      profileResidual M f t - profileResidual M g t +
      StationaryNormalization.causalConvolution (fun s => M (f s) - M (g s)) v t +
      StationaryNormalization.causalConvolution w k t := by
  let w := fun s => f s - g s
  let v := fun s => -deriv g s
  let k := fun s => -deriv (M ∘ f) s
  change deriv w t + (1 + M 1) * w t =
    profileResidual M f t - profileResidual M g t +
      StationaryNormalization.causalConvolution (fun s => M (f s) - M (g s)) v t +
      StationaryNormalization.causalConvolution w k t
  have hwac : AbsolutelyContinuousOnInterval w 0 t := hfac.fun_sub hgac
  have hw0 : w 0 = 0 := by simp [w, hf0, hg0]
  have hMr : AbsolutelyContinuousOnInterval (fun s => M (f (t - s))) 0 t := by
    simpa only [Function.comp_def] using
      absolutelyContinuous_reflect (M ∘ f) 0 t t (by simpa using hMac)
  have hMgr : AbsolutelyContinuousOnInterval (fun s => M (g (t - s))) 0 t := by
    simpa only [Function.comp_def] using
      absolutelyContinuous_reflect (M ∘ g) 0 t t (by simpa using hMgac)
  have hfi := hfac.intervalIntegrable_deriv.continuousOn_mul hMr.continuousOn
  have hgi := hgac.intervalIntegrable_deriv.continuousOn_mul hMgr.continuousOn
  have hwi := hwac.intervalIntegrable_deriv.continuousOn_mul hMr.continuousOn
  have hdi := hgac.intervalIntegrable_deriv.neg.continuousOn_mul
    (hMr.continuousOn.sub hMgr.continuousOn)
  have hds : ∀ᵐ s ∂volume, s ∈ uIcc 0 t → deriv w s = deriv f s - deriv g s := by
    filter_upwards [hfac.ae_differentiableAt, hgac.ae_differentiableAt] with s hfs hgs hs
    have hd : HasDerivAt w (deriv f s - deriv g s) s := by
      convert (hfs hs).hasDerivAt.sub (hgs hs).hasDerivAt using 1
    exact hd.deriv
  have hd : deriv w t = deriv f t - deriv g t := by
    have hd : HasDerivAt w (deriv f t - deriv g t) t := by
      convert hfd.hasDerivAt.sub hgd.hasDerivAt using 1
    exact hd.deriv
  have hconv : StationaryNormalization.causalConvolution (M ∘ f) (deriv f) t -
      StationaryNormalization.causalConvolution (M ∘ g) (deriv g) t =
      StationaryNormalization.causalConvolution (M ∘ f) (deriv w) t -
      StationaryNormalization.causalConvolution (fun s => M (f s) - M (g s)) v t := by
    unfold StationaryNormalization.causalConvolution
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, v] at hfi hgi hwi hdi ⊢
    rw [← intervalIntegral.integral_sub hfi hgi, ← intervalIntegral.integral_sub hwi hdi]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hds] with s hs his
    rw [hs (uIoc_subset_uIcc his)]
    ring
  have hibp : StationaryNormalization.causalConvolution (M ∘ f) (deriv w) t =
      M 1 * w t - StationaryNormalization.causalConvolution w k t := by
    have hh := convolution_integration_by_parts (M ∘ f) w t ht hMac hwac
    simp only [Function.comp_apply, hf0, hw0, mul_zero, sub_zero] at hh
    unfold StationaryNormalization.causalConvolution
    simp only [Function.comp_apply]
    rw [hh]
    have hkconv := causalConvolution_comm w k t
    unfold StationaryNormalization.causalConvolution at hkconv
    rw [hkconv]
    dsimp [k]
    simp only [neg_mul, intervalIntegral.integral_neg, sub_neg_eq_add]
  unfold profileResidual
  rw [hd]
  have hconv' := hconv
  rw [hibp] at hconv'
  dsimp [w] at hconv' ⊢
  linarith

/-- Order lower bounds pass through the actual Lebesgue causal integral. -/
theorem convolution_lower_bound (f g k : ℝ → ℝ) (C t : ℝ) (ht : 0 ≤ t)
    (hf : ContinuousOn f (Icc 0 t)) (hg : ContinuousOn g (Icc 0 t))
    (hk : IntervalIntegrable k volume 0 t) (hkn : ∀ s ∈ Icc 0 t, 0 ≤ k s)
    (horder : ∀ s ∈ Icc 0 t, -C * g s ≤ f s) :
    -C * StationaryNormalization.causalConvolution g k t ≤
      StationaryNormalization.causalConvolution f k t := by
  have hfr : ContinuousOn (fun s => f (t - s)) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact hf.comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hgr : ContinuousOn (fun s => g (t - s)) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact hg.comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hfi := hk.continuousOn_mul hfr
  have hgi := hk.continuousOn_mul hgr
  have hmono := intervalIntegral.integral_mono_on ht (hgi.const_mul (-C)) hfi
    (fun s hs => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (horder (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩) (hkn s hs))
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- Comparison for two genuine locally AC monotone profiles. This single
statement implies both directions of manuscript Lemma 16.4. -/
theorem compare_profiles (M f g : ℝ → ℝ) (L : ℝ≥0)
    (hM : MonotoneOn M (Icc 0 1)) (hLip : LipschitzOnWith L M (Icc 0 1))
    (hM0 : M 0 = 0)
    (hfac : ∀ T ≥ 0, AbsolutelyContinuousOnInterval f 0 T)
    (hgac : ∀ T ≥ 0, AbsolutelyContinuousOnInterval g 0 T)
    (hfanti : AntitoneOn f (Ici 0)) (hganti : AntitoneOn g (Ici 0))
    (hfrange : ∀ t ∈ Ici 0, f t ∈ Icc 0 1)
    (hgrange : ∀ t ∈ Ici 0, g t ∈ Icc 0 1)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hresidual : ∀ᵐ t ∂volume, t ∈ Ici 0 → profileResidual M g t ≤ profileResidual M f t) :
    ∀ t ∈ Ici 0, g t ≤ f t := by
  intro T hT
  change 0 ≤ T at hT
  let w := fun s => f s - g s
  let v := fun s => -deriv g s
  let k := fun s => -deriv (M ∘ f) s
  let n := negativePart w
  have hwac : AbsolutelyContinuousOnInterval w 0 T := (hfac T hT).fun_sub (hgac T hT)
  have hw0 : w 0 = 0 := by simp [w, hf0, hg0]
  have hnac : AbsolutelyContinuousOnInterval n 0 T := negativePart_absolutelyContinuous w 0 T hwac
  obtain ⟨hMac, hki, hkn, hkmass⟩ := memory_kernel_properties M f L hM hLip hM0
    hfanti hfrange hf0 T hT (hfac T hT)
  obtain ⟨hMgac, _, _, _⟩ := memory_kernel_properties M g L hM hLip hM0
    hganti hgrange hg0 T hT (hgac T hT)
  have hvi : IntervalIntegrable v volume 0 T := (hgac T hT).intervalIntegrable_deriv.neg
  have hvn (s : ℝ) (hs : s ∈ Ici 0) : 0 ≤ v s :=
    neg_nonneg.mpr (antitoneOn_deriv_nonpos g hganti s hs)
  have hvmass (s : ℝ) (hs : s ∈ Icc 0 T) : (∫ z in 0..s, v z) ≤ 1 := by
    dsimp [v]
    rw [intervalIntegral.integral_neg, (hgac s hs.1).integral_deriv_eq_sub, hg0]
    have hnon := (hgrange s hs.1).1
    linarith
  have hb : 0 ≤ 1 + M 1 := by
    have hh := hM (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
    rw [hM0] at hh
    linarith
  have hineq : ∀ᵐ s ∂volume, s ∈ Icc 0 T →
      -((L : ℝ) * StationaryNormalization.causalConvolution n v s +
        StationaryNormalization.causalConvolution n k s) ≤
      deriv w s + (1 + M 1) * w s := by
    filter_upwards [(hfac T hT).ae_differentiableAt, (hgac T hT).ae_differentiableAt,
      hresidual] with s hfs hgs hrs hs
    have hsu : s ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using hs
    have hsub : uIcc 0 s ⊆ uIcc 0 T := by
      simp only [uIcc_of_le hs.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl hs.2
    have hfc : ContinuousOn f (Icc 0 s) := by
      simpa only [uIcc_of_le hs.1] using (hfac s hs.1).continuousOn
    have hgc : ContinuousOn g (Icc 0 s) := by
      simpa only [uIcc_of_le hs.1] using (hgac s hs.1).continuousOn
    have hδc : ContinuousOn (fun z => M (f z) - M (g z)) (Icc 0 s) := by
      have hc := ((hMac.mono hsub).continuousOn.sub (hMgac.mono hsub).continuousOn)
      rw [uIcc_of_le hs.1] at hc
      convert hc using 1
      funext z
      rfl
    have hnc : ContinuousOn n (Icc 0 s) := by
      simpa only [uIcc_of_le hs.1] using (hnac.mono hsub).continuousOn
    have hwc : ContinuousOn w (Icc 0 s) := hfc.sub hgc
    have hδlower : -(L : ℝ) * StationaryNormalization.causalConvolution n v s ≤
        StationaryNormalization.causalConvolution (fun z => M (f z) - M (g z)) v s := by
      apply convolution_lower_bound _ n v (L : ℝ) s hs.1 hδc hnc (hvi.mono_set hsub)
        (fun z hz => hvn z hz.1)
      intro z hz
      exact memory_difference_lower_bound M L hM hLip (f z) (g z)
        (hfrange z hz.1) (hgrange z hz.1)
    have hwlower : -StationaryNormalization.causalConvolution n k s ≤
        StationaryNormalization.causalConvolution w k s := by
      have hh := convolution_lower_bound w n k 1 s hs.1 hwc hnc (hki.mono_set hsub)
        (fun z hz => hkn z hz.1) (fun z hz => by
          have hnz : -w z ≤ n z := le_max_left _ _
          linarith)
      simpa only [neg_mul, one_mul] using hh
    have heq := residual_difference M f g s hs.1 (hfac s hs.1) (hgac s hs.1)
      (hMac.mono hsub) (hMgac.mono hsub) hf0 hg0 (hfs hsu) (hgs hsu)
    have hres := hrs hs.1
    change deriv w s + (1 + M 1) * w s =
      profileResidual M f s - profileResidual M g s +
        StationaryNormalization.causalConvolution (fun z => M (f z) - M (g z)) v s +
        StationaryNormalization.causalConvolution w k s at heq
    linarith
  have hpositive := volterra_nonnegative w v k T (1 + M 1) (L : ℝ) 1 (M 1)
    hT hb L.coe_nonneg hwac hw0 hvi hki
    (fun s hs => hvn s hs.1) (fun s hs => hkn s hs.1) hvmass hkmass hineq
  have hwT := hpositive T ⟨hT, le_rfl⟩
  dsimp [w] at hwT
  linarith

/-- Every finite polynomial with the manuscript's nonnegative memory
coefficients satisfies the actual comparison hypotheses. -/
theorem polynomial_memory_properties (s : Finset ℕ) (coeff : ℕ → ℝ)
    (hcoeff : ∀ j ∈ s, 0 ≤ coeff j) (M : ℝ → ℝ)
    (hMformula : ∀ y, M y = y + ∑ j ∈ s, coeff j * y ^ (j + 2)) :
    M 0 = 0 ∧ MonotoneOn M (Icc 0 1) ∧
      ∃ L : ℝ≥0, LipschitzOnWith L M (Icc 0 1) := by
  have hM0 : M 0 = 0 := by simp [hMformula]
  have hMmono : MonotoneOn M (Icc 0 1) := by
    intro x hx y hy hxy
    rw [hMformula, hMformula]
    exact add_le_add hxy (Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy (j + 2)) (hcoeff j hj)))
  let C : ℝ := 1 + ∑ j ∈ s, coeff j * (j + 2 : ℕ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun j hj =>
      mul_nonneg (hcoeff j hj) (Nat.cast_nonneg _)))
  refine ⟨hM0, hMmono, Real.toNNReal C, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  rw [Real.coe_toNNReal C hC, Real.dist_eq, Real.dist_eq]
  have hp (n : ℕ) : |x ^ n - y ^ n| ≤ (n : ℝ) * |x - y| := by
    have hmaxn : 0 ≤ max |x| |y| := (abs_nonneg x).trans (le_max_left _ _)
    have hmax : max |x| |y| ≤ 1 := by
      rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]
      exact max_le hx.2 hy.2
    have hp := abs_pow_sub_pow_le (a := x) (b := y) (n := n)
    have hpow : max |x| |y| ^ (n - 1) ≤ 1 := pow_le_one₀ hmaxn hmax
    calc
      |x ^ n - y ^ n| ≤ |x - y| * n * max |x| |y| ^ (n - 1) := hp
      _ ≤ |x - y| * n * 1 := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      _ = (n : ℝ) * |x - y| := by ring
  have hδ : M x - M y = (x - y) + ∑ j ∈ s, coeff j * (x ^ (j + 2) - y ^ (j + 2)) := by
    rw [hMformula, hMformula]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hδ]
  calc
    |(x - y) + ∑ j ∈ s, coeff j * (x ^ (j + 2) - y ^ (j + 2))| ≤
        |x - y| + |∑ j ∈ s, coeff j * (x ^ (j + 2) - y ^ (j + 2))| := abs_add_le _ _
    _ ≤ |x - y| + ∑ j ∈ s, |coeff j * (x ^ (j + 2) - y ^ (j + 2))| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |x - y| + ∑ j ∈ s, coeff j * ((j + 2 : ℕ) * |x - y|) := by
      gcongr with j hj
      rw [abs_mul, abs_of_nonneg (hcoeff j hj)]
      exact mul_le_mul_of_nonneg_left (hp (j + 2)) (hcoeff j hj)
    _ = C * |x - y| := by
      dsimp [C]
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The comparison hypotheses hold for the exact normalized polynomial
already derived from (S1)--(S4), without new assumptions on its coefficients. -/
theorem normalized_memory_properties (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : StationaryNormalization.NormalizedStationaryConclusions p β γ q c r) :
    let M := StationaryNormalization.normalizedMemory q
      (StationaryNormalization.purePhi p (β ^ 2) γ)
    M 0 = 0 ∧ MonotoneOn M (Icc 0 1) ∧ ∃ L : ℝ≥0, LipschitzOnWith L M (Icc 0 1) := by
  exact polynomial_memory_properties (Finset.range (p - 2))
    (fun j => StationaryNormalization.memoryCoefficient p q (j + 2))
    (fun j _ => h.coefficients_nonnegative (j + 2)) _ h.memory_expansion

/-- The exact profile hypotheses in manuscript Lemma 16.4. -/
structure AdmissibleProfile (P : ℝ → ℝ) : Prop where
  locally_AC : ∀ T ≥ 0, AbsolutelyContinuousOnInterval P 0 T
  nonincreasing : AntitoneOn P (Ici 0)
  values : ∀ t ∈ Ici 0, P t ∈ Icc 0 1
  initial : P 0 = 1

/-- All comparison hypotheses of u follow from the already proved
normalized stationary conclusions. The residual is its actual a.e. derivative. -/
theorem normalized_profile_admissible (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : StationaryNormalization.NormalizedStationaryConclusions p β γ q c r) :
    AdmissibleProfile (StationaryNormalization.normalizedProfile q c) ∧
      ∀ᵐ t ∂volume, t ∈ Ici 0 → profileResidual
        (StationaryNormalization.normalizedMemory q (StationaryNormalization.purePhi p (β ^ 2) γ))
        (StationaryNormalization.normalizedProfile q c) t = 0 := by
  let u := StationaryNormalization.normalizedProfile q c
  let v := StationaryNormalization.normalizedResponse q r
  let M := StationaryNormalization.normalizedMemory q (StationaryNormalization.purePhi p (β ^ 2) γ)
  have hanti : AntitoneOn u (Ici 0) := by
    apply StrictAntiOn.antitoneOn
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) h.profile_C1.continuousOn
    intro t ht
    have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hd := h.derivative t htpos.le
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds htpos)] at hd
    rw [hd]
    exact neg_neg_of_pos (h.response_positive t htpos.le)
  have hvalues : ∀ t ∈ Ici 0, u t ∈ Icc 0 1 := by
    intro t ht
    refine ⟨(h.profile_positive t ht).le, ?_⟩
    have hh := hanti (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
    simpa only [u, h.initial_profile] using hh
  refine ⟨⟨?_, hanti, hvalues, h.initial_profile⟩, ?_⟩
  · intro T hT
    have hc : ContDiffOn ℝ 1 u (uIcc 0 T) :=
      h.profile_C1.mono (by
        rw [uIcc_of_le hT]
        exact Icc_subset_Ici_self)
    exact hc.absolutelyContinuousOnInterval
  · filter_upwards [volume.ae_ne (0 : ℝ)] with t htne ht
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htne)
    have heq := h.equation t ht
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds htpos)] at heq
    have hconv : StationaryNormalization.causalConvolution (fun s => M (u s))
        (fun s => derivWithin u (Ici 0) s) t =
        StationaryNormalization.causalConvolution (M ∘ u) (deriv u) t := by
      unfold StationaryNormalization.causalConvolution
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      rw [uIoc_of_le ht] at hs
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds hs.1)]
      rfl
    change deriv u t + u t +
      StationaryNormalization.causalConvolution (fun s => M (u s))
        (fun s => derivWithin u (Ici 0) s) t = 0 at heq
    rw [hconv] at heq
    exact heq

/-- Lemma 16.4, upper comparison. P has exactly the stated locally AC,
nonincreasing, unit initial value and range hypotheses, and only an a.e.
residual inequality; u is supplied by the proved normalization theorem. -/
theorem normalized_comparison_upper (p : ℕ) (β γ q : ℝ) (c r P : ℝ → ℝ)
    (h : StationaryNormalization.NormalizedStationaryConclusions p β γ q c r)
    (hP : AdmissibleProfile P)
    (hresidual : ∀ᵐ t ∂volume, t ∈ Ici 0 → 0 ≤ profileResidual
      (StationaryNormalization.normalizedMemory q (StationaryNormalization.purePhi p (β ^ 2) γ)) P t) :
    ∀ t ∈ Ici 0, StationaryNormalization.normalizedProfile q c t ≤ P t := by
  obtain ⟨hM0, hM, L, hLip⟩ := normalized_memory_properties p β γ q c r h
  obtain ⟨hu, hur⟩ := normalized_profile_admissible p β γ q c r h
  apply compare_profiles _ P (StationaryNormalization.normalizedProfile q c) L hM hLip hM0
    hP.locally_AC hu.locally_AC hP.nonincreasing hu.nonincreasing hP.values hu.values
    hP.initial hu.initial
  filter_upwards [hur, hresidual] with t hut hPt ht
  rw [hut ht]
  exact hPt ht

/-- Lemma 16.4, lower comparison, with the same actual profile assumptions. -/
theorem normalized_comparison_lower (p : ℕ) (β γ q : ℝ) (c r P : ℝ → ℝ)
    (h : StationaryNormalization.NormalizedStationaryConclusions p β γ q c r)
    (hP : AdmissibleProfile P)
    (hresidual : ∀ᵐ t ∂volume, t ∈ Ici 0 → profileResidual
      (StationaryNormalization.normalizedMemory q (StationaryNormalization.purePhi p (β ^ 2) γ)) P t ≤ 0) :
    ∀ t ∈ Ici 0, P t ≤ StationaryNormalization.normalizedProfile q c t := by
  obtain ⟨hM0, hM, L, hLip⟩ := normalized_memory_properties p β γ q c r h
  obtain ⟨hu, hur⟩ := normalized_profile_admissible p β γ q c r h
  apply compare_profiles _ (StationaryNormalization.normalizedProfile q c) P L hM hLip hM0
    hu.locally_AC hP.locally_AC hu.nonincreasing hP.nonincreasing hu.values hP.values
    hu.initial hP.initial
  filter_upwards [hur, hresidual] with t hut hPt ht
  rw [hut ht]
  exact hPt ht

end
end SphericalAging.StationaryComparison
