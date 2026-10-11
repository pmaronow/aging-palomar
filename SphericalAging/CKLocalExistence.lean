module

public import SphericalAging.CKWellposedness
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Calculus.ParametricIntegral

public section

/-!
# A local Picard construction for the nonlinear CK system

A globally Lipschitz truncation is used during the construction. A sufficiently
short horizon keeps the resulting fixed point strictly inside the truncation
interval, where the equations are the original polynomial equations.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace SphericalAging.CKLocalExistence
open CKSpecification CKWellposedness

@[expose] abbrev UnitTime := Icc (0 : ℝ) 1
@[expose] abbrev Square := UnitTime × UnitTime
@[expose] abbrev State := C(Square, ℝ × ℝ)

@[expose] def clampTime (t : ℝ) : UnitTime :=
  ⟨max 0 (min 1 t),le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

@[expose] def clipValue (x : ℝ) : ℝ := max (-2) (min 2 x)

theorem clampTime_continuous : Continuous clampTime := by
  apply Continuous.subtype_mk
  fun_prop

theorem clampTime_eq {t : ℝ} (ht : t ∈ Icc 0 1) : (clampTime t : ℝ)=t := by
  simp [clampTime,min_eq_right ht.2,max_eq_right ht.1]

theorem clipValue_continuous : Continuous clipValue := by unfold clipValue; fun_prop

theorem clipValue_abs_le (x : ℝ) : |clipValue x| ≤ 2 := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clipValue_eq {x : ℝ} (hx : x ∈ Icc (-2) 2) : clipValue x=x := by
  simp [clipValue,min_eq_right hx.2,max_eq_right hx.1]

theorem clipValue_lipschitz : LipschitzWith 1 clipValue :=
  (LipschitzWith.id.const_min 2).const_max (-2)

@[expose] def sample (f : State) (t s : ℝ) : ℝ × ℝ :=
  f (clampTime (max t s),clampTime (min t s))

@[expose] def trialC (f : State) (t s : ℝ) : ℝ := clipValue (sample f t s).1
@[expose] def trialR (f : State) (t s : ℝ) : ℝ := clipValue (sample f t s).2

theorem sample_continuous (f : State) : Continuous (Function.uncurry (sample f)) := by
  apply f.continuous.comp
  exact (clampTime_continuous.comp (continuous_fst.max continuous_snd)).prodMk
    (clampTime_continuous.comp (continuous_fst.min continuous_snd))

theorem trialC_continuous (f : State) : Continuous (Function.uncurry (trialC f)) :=
  clipValue_continuous.comp ((sample_continuous f).fst)

theorem trialR_continuous (f : State) : Continuous (Function.uncurry (trialR f)) :=
  clipValue_continuous.comp ((sample_continuous f).snd)

theorem trialC_abs_le (f : State) (t s : ℝ) : |trialC f t s| ≤ 2 := clipValue_abs_le _
theorem trialR_abs_le (f : State) (t s : ℝ) : |trialR f t s| ≤ 2 := clipValue_abs_le _

theorem sample_symmetric (f : State) (t s : ℝ) : sample f t s=sample f s t := by
  simp only [sample,max_comm,min_comm]

theorem trialC_symmetric (f : State) (t s : ℝ) : trialC f t s=trialC f s t := by
  simp only [trialC,sample_symmetric f t s]

theorem trialR_symmetric (f : State) (t s : ℝ) : trialR f t s=trialR f s t := by
  simp only [trialR,sample_symmetric f t s]

theorem sample_difference_le (f g : State) (t s : ℝ) :
    ‖sample f t s-sample g t s‖ ≤ ‖f-g‖ := (f-g).norm_coe_le_norm _

theorem trialC_difference_le (f g : State) (t s : ℝ) :
    |trialC f t s-trialC g t s| ≤ ‖f-g‖ := by
  have hclip := clipValue_lipschitz.dist_le_mul (sample f t s).1 (sample g t s).1
  have hfst : |(sample f t s).1-(sample g t s).1| ≤ ‖f-g‖ := by
    have hh : |(sample f t s).1-(sample g t s).1| ≤ ‖sample f t s-sample g t s‖ := by
      simpa only [Real.norm_eq_abs,Prod.fst_sub] using norm_fst_le (sample f t s-sample g t s)
    exact hh.trans (sample_difference_le f g t s)
  simp only [Real.dist_eq,one_mul,NNReal.coe_one] at hclip
  exact hclip.trans hfst

theorem trialR_difference_le (f g : State) (t s : ℝ) :
    |trialR f t s-trialR g t s| ≤ ‖f-g‖ := by
  have hclip := clipValue_lipschitz.dist_le_mul (sample f t s).2 (sample g t s).2
  have hsnd : |(sample f t s).2-(sample g t s).2| ≤ ‖f-g‖ := by
    have hh : |(sample f t s).2-(sample g t s).2| ≤ ‖sample f t s-sample g t s‖ := by
      simpa only [Real.norm_eq_abs,Prod.snd_sub] using norm_snd_le (sample f t s-sample g t s)
    exact hh.trans (sample_difference_le f g t s)
  simp only [Real.dist_eq,one_mul,NNReal.coe_one] at hclip
  exact hclip.trans hsnd

@[expose] def trialData (p : ℕ) (β τ : ℝ) (f : State) : CKData where
  C := trialC f
  R := trialR f
  multiplier := fun t => 1+τ*β ^ 2*(p : ℝ)^2*
    (∫ u in (0 : ℝ)..t, trialC f t u ^ (p-1)*trialR f t u)

@[expose] def unitResponseSlope (p : ℕ) (β τ : ℝ) (f : State) (t s : ℝ) : ℝ :=
  -(trialData p β τ f).multiplier t*trialR f t s+
    τ*β ^ 2*((p : ℝ)*((p : ℝ)-1))*responseMemory (p-2) (trialData p β τ f) t s

@[expose] def unitCorrelationSlope (p : ℕ) (β τ : ℝ) (f : State) (t s : ℝ) : ℝ :=
  -(trialData p β τ f).multiplier t*trialC f t s+
    τ*β ^ 2*((p : ℝ)*((p : ℝ)-1))*correlationMemory (p-2) (trialData p β τ f) t s+
    τ*β ^ 2*(p : ℝ)*forcingMemory (p-1) (trialData p β τ f) t s

theorem trialMultiplier_continuous (p : ℕ) (β τ : ℝ) (f : State) :
    Continuous (trialData p β τ f).multiplier := by
  have hc := trialC_continuous f
  have hr := trialR_continuous f
  have hi : Continuous (fun t : ℝ => ∫ u in (0 : ℝ)..t,
      trialC f t u ^ (p-1)*trialR f t u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((hc.pow _).mul hr) continuous_id
  exact continuous_const.add (continuous_const.mul hi)

theorem continuous_moving_integral {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {a b : X → ℝ}
    (hF : Continuous (Function.uncurry F)) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => ∫ u in a x..b x, F x u) := by
  have hia : Continuous (fun x => ∫ u in (0 : ℝ)..a x, F x u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF ha
  have hib : Continuous (fun x => ∫ u in (0 : ℝ)..b x, F x u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF hb
  apply (hib.sub hia).congr
  intro x
  have hw : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) 0 (a x)) (hw.intervalIntegrable (a x) (b x))
  dsimp only [Pi.sub_apply]
  linarith

theorem responseMemory_continuous (n : ℕ) (f : State) (p : ℕ) (β τ : ℝ) :
    Continuous (Function.uncurry (responseMemory n (trialData p β τ f))) := by
  apply continuous_moving_integral
  · exact (((trialC_continuous f).comp
      (continuous_fst.fst.prodMk continuous_snd)).pow n).mul
        ((trialR_continuous f).comp (continuous_fst.fst.prodMk continuous_snd)) |>.mul
        ((trialR_continuous f).comp (continuous_snd.prodMk continuous_fst.snd))
  · fun_prop
  · fun_prop

theorem correlationMemory_continuous (n : ℕ) (f : State) (p : ℕ) (β τ : ℝ) :
    Continuous (Function.uncurry (correlationMemory n (trialData p β τ f))) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (((trialC_continuous f).comp
      (continuous_fst.fst.prodMk continuous_snd)).pow n).mul
        ((trialR_continuous f).comp (continuous_fst.fst.prodMk continuous_snd)) |>.mul
        ((trialC_continuous f).comp (continuous_snd.prodMk continuous_fst.snd))
  · fun_prop

theorem forcingMemory_continuous (n : ℕ) (f : State) (p : ℕ) (β τ : ℝ) :
    Continuous (Function.uncurry (forcingMemory n (trialData p β τ f))) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (((trialC_continuous f).comp
      (continuous_fst.fst.prodMk continuous_snd)).pow n).mul
        ((trialR_continuous f).comp (continuous_fst.snd.prodMk continuous_snd))
  · fun_prop

theorem unitResponseSlope_continuous (p : ℕ) (β τ : ℝ) (f : State) :
    Continuous (Function.uncurry (unitResponseSlope p β τ f)) :=
  (((trialMultiplier_continuous p β τ f).comp continuous_fst).neg.mul
    (trialR_continuous f)).add
      (continuous_const.mul (responseMemory_continuous (p-2) f p β τ))

theorem unitCorrelationSlope_continuous (p : ℕ) (β τ : ℝ) (f : State) :
    Continuous (Function.uncurry (unitCorrelationSlope p β τ f)) :=
  ((((trialMultiplier_continuous p β τ f).comp continuous_fst).neg.mul
    (trialC_continuous f)).add
      (continuous_const.mul (correlationMemory_continuous (p-2) f p β τ))).add
        (continuous_const.mul (forcingMemory_continuous (p-1) f p β τ))

attribute [irreducible] unitResponseSlope unitCorrelationSlope

@[expose] def picardValues (p : ℕ) (β τ : ℝ) (f : State) (t s : ℝ) : ℝ × ℝ :=
  (1+τ*(∫ u in min t s..max t s, unitCorrelationSlope p β τ f u (min t s)),
   1+τ*(∫ u in min t s..max t s, unitResponseSlope p β τ f u (min t s)))

theorem picardValues_continuous (p : ℕ) (β τ : ℝ) (f : State) :
    Continuous (Function.uncurry (picardValues p β τ f)) := by
  have hm : Continuous (fun z : (ℝ × ℝ) × ℝ => (z.2,min z.1.1 z.1.2)) :=
    continuous_snd.prodMk (continuous_fst.fst.min continuous_fst.snd)
  have hcF : Continuous (Function.uncurry
      (fun (z : ℝ × ℝ) u => unitCorrelationSlope p β τ f u (min z.1 z.2))) :=
    (unitCorrelationSlope_continuous p β τ f).comp hm
  have hrF : Continuous (Function.uncurry
      (fun (z : ℝ × ℝ) u => unitResponseSlope p β τ f u (min z.1 z.2))) :=
    (unitResponseSlope_continuous p β τ f).comp hm
  have hc := continuous_moving_integral hcF
    (continuous_fst.min continuous_snd) (continuous_fst.max continuous_snd)
  have hr := continuous_moving_integral hrF
    (continuous_fst.min continuous_snd) (continuous_fst.max continuous_snd)
  exact (continuous_const.add (continuous_const.mul hc)).prodMk
    (continuous_const.add (continuous_const.mul hr))

@[expose] def picardMap (p : ℕ) (β τ : ℝ) (f : State) : State :=
  ⟨fun z => picardValues p β τ f z.1 z.2,
    (picardValues_continuous p β τ f).comp (continuous_fst.subtype_val.prodMk continuous_snd.subtype_val)⟩

theorem interval_integral_abs_le {F : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hbound : ∀ u ∈ Icc a b, |F u| ≤ A) :
    |∫ u in a..b, F u| ≤ (b-a)*A := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := F) (a := a) (b := b) (C := A)
    (fun u hu => by
      rw [uIoc_of_le hab] at hu
      simpa only [Real.norm_eq_abs] using hbound u ⟨hu.1.le,hu.2⟩)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hh

theorem trial_pair_abs_le (f : State) (n : ℕ) (t s u : ℝ) :
    |trialC f t u ^ n*trialR f s u| ≤ (2 : ℝ)^n*2 := by
  rw [abs_mul,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (trialC_abs_le f t u) n)
    (trialR_abs_le f s u) (abs_nonneg _) (pow_nonneg (by norm_num) _)

theorem trial_triple_response_abs_le (f : State) (n : ℕ) (t s u : ℝ) :
    |trialC f t u ^ n*trialR f t u*trialR f u s| ≤ (2 : ℝ)^n*4 := by
  rw [abs_mul]
  have hh := mul_le_mul (trial_pair_abs_le f n t t u) (trialR_abs_le f u s)
    (abs_nonneg _) (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by norm_num))
  convert hh using 1; ring

theorem trial_triple_correlation_abs_le (f : State) (n : ℕ) (t s u : ℝ) :
    |trialC f t u ^ n*trialR f t u*trialC f u s| ≤ (2 : ℝ)^n*4 := by
  rw [abs_mul]
  have hh := mul_le_mul (trial_pair_abs_le f n t t u) (trialC_abs_le f u s)
    (abs_nonneg _) (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by norm_num))
  convert hh using 1; ring

@[expose] def fieldBound (p : ℕ) (β : ℝ) : ℝ := 3+β ^ 2*(p : ℝ)^2*((2 : ℝ)^(p-1)*2)

theorem fieldBound_ge_three (p : ℕ) (β : ℝ) : 3 ≤ fieldBound p β := by
  have hh : 0 ≤ β ^ 2*(p : ℝ)^2*((2 : ℝ)^(p-1)*2) := by positivity
  dsimp only [fieldBound]
  linarith

theorem trialMultiplier_abs_le (p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ∈ Icc 0 1)
    (f : State) {t : ℝ} (ht : t ∈ Icc 0 1) :
    |(trialData p β τ f).multiplier t| ≤ fieldBound p β := by
  have hmem := interval_integral_abs_le ht.1 (fun u _ => trial_pair_abs_le f (p-1) t t u)
  have hmem' : |∫ u in (0 : ℝ)..t, trialC f t u ^ (p-1)*trialR f t u| ≤
      (2 : ℝ)^(p-1)*2 := by
    apply hmem.trans
    rw [sub_zero]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by norm_num))
  have ha : 0 ≤ β ^ 2*(p : ℝ)^2 := mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ))
  have hτa : 0 ≤ τ*β ^ 2*(p : ℝ)^2 := mul_nonneg (mul_nonneg hτ.1 (sq_nonneg β)) (sq_nonneg _)
  have hτbound : τ*β ^ 2*(p : ℝ)^2 ≤ β ^ 2*(p : ℝ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hτ.2 ha]
  calc
    |(trialData p β τ f).multiplier t| ≤ 1+|τ*β ^ 2*(p : ℝ)^2*
        (∫ u in (0 : ℝ)..t, trialC f t u ^ (p-1)*trialR f t u)| := by
      simpa only [trialData,abs_one] using abs_add_le (1 : ℝ) _
    _ ≤ 1+(β ^ 2*(p : ℝ)^2)*((2 : ℝ)^(p-1)*2) := by
      rw [abs_mul,abs_of_nonneg hτa]
      exact add_le_add (le_refl 1) (mul_le_mul hτbound hmem' (abs_nonneg _) ha)
    _ ≤ fieldBound p β := by dsimp only [fieldBound]; linarith

theorem trialPair_integrable (f : State) (n : ℕ) (t s a b : ℝ) :
    IntervalIntegrable (fun u => trialC f t u ^ n*trialR f s u) volume a b := by
  have hc : Continuous (fun u => trialC f t u) :=
    (trialC_continuous f).comp (continuous_const.prodMk continuous_id)
  have hr : Continuous (fun u => trialR f s u) :=
    (trialR_continuous f).comp (continuous_const.prodMk continuous_id)
  exact ((hc.pow n).mul hr).intervalIntegrable a b

theorem trialResponse_integrable (f : State) (n : ℕ) (t s a b : ℝ) :
    IntervalIntegrable (fun u => trialC f t u ^ n*trialR f t u*trialR f u s) volume a b := by
  have hc : Continuous (fun u => trialC f t u) :=
    (trialC_continuous f).comp (continuous_const.prodMk continuous_id)
  have hr : Continuous (fun u => trialR f t u) :=
    (trialR_continuous f).comp (continuous_const.prodMk continuous_id)
  have hy : Continuous (fun u => trialR f u s) :=
    (trialR_continuous f).comp (continuous_id.prodMk continuous_const)
  exact (((hc.pow n).mul hr).mul hy).intervalIntegrable a b

theorem trialCorrelation_integrable (f : State) (n : ℕ) (t s a b : ℝ) :
    IntervalIntegrable (fun u => trialC f t u ^ n*trialR f t u*trialC f u s) volume a b := by
  have hc : Continuous (fun u => trialC f t u) :=
    (trialC_continuous f).comp (continuous_const.prodMk continuous_id)
  have hr : Continuous (fun u => trialR f t u) :=
    (trialR_continuous f).comp (continuous_const.prodMk continuous_id)
  have hy : Continuous (fun u => trialC f u s) :=
    (trialC_continuous f).comp (continuous_id.prodMk continuous_const)
  exact (((hc.pow n).mul hr).mul hy).intervalIntegrable a b

theorem interval_integral_abs_le_unit {F : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hA : 0 ≤ A) (hunit : b-a ≤ 1) (hbound : ∀ u ∈ Icc a b, |F u| ≤ A) :
    |∫ u in a..b, F u| ≤ A :=
  (interval_integral_abs_le hab hbound).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hunit hA)

theorem trialMemory_abs_bounds (p : ℕ) (β τ : ℝ) (f : State) {t s : ℝ}
    (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |responseMemory n (trialData p β τ f) t s| ≤ (2 : ℝ)^n*4 ∧
    |correlationMemory n (trialData p β τ f) t s| ≤ (2 : ℝ)^n*4 ∧
    |forcingMemory n (trialData p β τ f) t s| ≤ (2 : ℝ)^n*2 := by
  have hpow : 0 ≤ (2 : ℝ)^n := pow_nonneg (by norm_num) _
  refine ⟨?_,?_,?_⟩
  · exact interval_integral_abs_le_unit hs.2 (mul_nonneg hpow (by norm_num))
      (by linarith [ht.2,hs.1]) (fun u _ => trial_triple_response_abs_le f n t s u)
  · exact interval_integral_abs_le_unit ht.1 (mul_nonneg hpow (by norm_num))
      (by simpa using ht.2) (fun u _ => trial_triple_correlation_abs_le f n t s u)
  · exact interval_integral_abs_le_unit hs.1 (mul_nonneg hpow (by norm_num))
      (by simpa using hs.2.trans ht.2) (fun u _ => trial_pair_abs_le f n t s u)

theorem trialMemory_difference_bounds (p : ℕ) (β τ : ℝ) (f g : State) {t s : ℝ}
    (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |responseMemory n (trialData p β τ f) t s-responseMemory n (trialData p β τ g) t s| ≤
        tripleLip 2 n*‖f-g‖ ∧
    |correlationMemory n (trialData p β τ f) t s-correlationMemory n (trialData p β τ g) t s| ≤
        tripleLip 2 n*‖f-g‖ ∧
    |forcingMemory n (trialData p β τ f) t s-forcingMemory n (trialData p β τ g) t s| ≤
        pairLip 2 n*‖f-g‖ := by
  have hR (u : ℝ) := power_triple_difference_le (by norm_num : (0 : ℝ) ≤ 2)
    (norm_nonneg (f-g)) (trialC_abs_le f t u) (trialC_abs_le g t u)
    (trialR_abs_le f t u) (trialR_abs_le g t u)
    (trialR_abs_le f u s) (trialR_abs_le g u s)
    (trialC_difference_le f g t u) (trialR_difference_le f g t u)
    (trialR_difference_le f g u s) n
  have hC (u : ℝ) := power_triple_difference_le (by norm_num : (0 : ℝ) ≤ 2)
    (norm_nonneg (f-g)) (trialC_abs_le f t u) (trialC_abs_le g t u)
    (trialR_abs_le f t u) (trialR_abs_le g t u)
    (trialC_abs_le f u s) (trialC_abs_le g u s)
    (trialC_difference_le f g t u) (trialR_difference_le f g t u)
    (trialC_difference_le f g u s) n
  have hF (u : ℝ) := power_product_difference_le (by norm_num : (0 : ℝ) ≤ 2)
    (norm_nonneg (f-g)) (trialC_abs_le f t u) (trialC_abs_le g t u)
    (trialR_abs_le f s u) (trialR_abs_le g s u)
    (trialC_difference_le f g t u) (trialR_difference_le f g s u) n
  have htr : 0 ≤ tripleLip 2 n*‖f-g‖ :=
    mul_nonneg (tripleLip_nonneg (by norm_num) _) (norm_nonneg _)
  have hpr : 0 ≤ pairLip 2 n*‖f-g‖ :=
    mul_nonneg (pairLip_nonneg (by norm_num) _) (norm_nonneg _)
  refine ⟨?_,?_,?_⟩
  · have hh := interval_integral_difference_le hs.2
      (trialResponse_integrable f n t s s t) (trialResponse_integrable g n t s s t)
      (fun u _ => hR u)
    exact hh.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (show t-s ≤ 1 by linarith [ht.2,hs.1]) htr)
  · have hh := interval_integral_difference_le ht.1
      (trialCorrelation_integrable f n t s 0 t) (trialCorrelation_integrable g n t s 0 t)
      (fun u _ => hC u)
    exact hh.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (show t-0 ≤ 1 by simpa using ht.2) htr)
  · have hh := interval_integral_difference_le hs.1
      (trialPair_integrable f n t s 0 s) (trialPair_integrable g n t s 0 s)
      (fun u _ => hF u)
    exact hh.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (show s-0 ≤ 1 by simpa using hs.2.trans ht.2) hpr)

theorem trialMultiplier_difference_le (p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ∈ Icc 0 1)
    (f g : State) {t : ℝ} (ht : t ∈ Icc 0 1) :
    |(trialData p β τ f).multiplier t-(trialData p β τ g).multiplier t| ≤
      (β ^ 2*(p : ℝ)^2*pairLip 2 (p-1))*‖f-g‖ := by
  have hi := interval_integral_difference_le ht.1
    (trialPair_integrable f (p-1) t t 0 t) (trialPair_integrable g (p-1) t t 0 t)
    (fun u _ => power_product_difference_le (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg (f-g))
      (trialC_abs_le f t u) (trialC_abs_le g t u) (trialR_abs_le f t u) (trialR_abs_le g t u)
      (trialC_difference_le f g t u) (trialR_difference_le f g t u) (p-1))
  have hpr : 0 ≤ pairLip 2 (p-1)*‖f-g‖ :=
    mul_nonneg (pairLip_nonneg (by norm_num) _) (norm_nonneg _)
  have hi' : |(∫ u in (0 : ℝ)..t, trialC f t u ^ (p-1)*trialR f t u)-
      (∫ u in (0 : ℝ)..t, trialC g t u ^ (p-1)*trialR g t u)| ≤ pairLip 2 (p-1)*‖f-g‖ :=
    hi.trans (by simpa only [sub_zero,one_mul] using mul_le_mul_of_nonneg_right ht.2 hpr)
  have ha : 0 ≤ β ^ 2*(p : ℝ)^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hτa : 0 ≤ τ*(β ^ 2*(p : ℝ)^2) := mul_nonneg hτ.1 ha
  have hτbound : τ*(β ^ 2*(p : ℝ)^2) ≤ β ^ 2*(p : ℝ)^2 :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ.2 ha
  have heq (a b : ℝ) : (1+τ*β ^ 2*(p : ℝ)^2*a)-(1+τ*β ^ 2*(p : ℝ)^2*b) =
      τ*(β ^ 2*(p : ℝ)^2)*(a-b) := by ring
  change |(1+τ*β ^ 2*(p : ℝ)^2*_)-(1+τ*β ^ 2*(p : ℝ)^2*_)| ≤ _
  rw [heq,abs_mul,abs_of_nonneg hτa]
  have hh := mul_le_mul hτbound hi' (abs_nonneg _) ha
  simpa only [mul_assoc] using hh

@[expose] def multiplierLip (p : ℕ) (β : ℝ) : ℝ := β ^ 2*(p : ℝ)^2*pairLip 2 (p-1)
@[expose] def slopeBound (p : ℕ) (β : ℝ) : ℝ :=
  2*fieldBound p β+β ^ 2*((p : ℝ)*((p : ℝ)-1))*((2 : ℝ)^(p-2)*4)+
    β ^ 2*(p : ℝ)*((2 : ℝ)^(p-1)*2)
@[expose] def slopeLip (p : ℕ) (β : ℝ) : ℝ :=
  fieldBound p β+multiplierLip p β*fieldBound p β+
    β ^ 2*((p : ℝ)*((p : ℝ)-1))*tripleLip 2 (p-2)+
    β ^ 2*(p : ℝ)*pairLip 2 (p-1)

theorem multiplierLip_nonneg (p : ℕ) (β : ℝ) : 0 ≤ multiplierLip p β :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (pairLip_nonneg (by norm_num) _)

theorem slope_constants_nonneg {p : ℕ} (hp : 3 ≤ p) (β : ℝ) :
    0 ≤ slopeBound p β ∧ 0 ≤ slopeLip p β := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hM : 0 ≤ fieldBound p β := le_trans (by norm_num) (fieldBound_ge_three p β)
  have hL := multiplierLip_nonneg p β
  have hq : 0 ≤ β ^ 2*((p : ℝ)*((p : ℝ)-1)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  have hr : 0 ≤ β ^ 2*(p : ℝ) := mul_nonneg (sq_nonneg _) hp0
  constructor
  · exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) hM)
      (mul_nonneg hq (mul_nonneg (pow_nonneg (by norm_num) _) (by norm_num))))
      (mul_nonneg hr (mul_nonneg (pow_nonneg (by norm_num) _) (by norm_num)))
  · exact add_nonneg (add_nonneg (add_nonneg hM (mul_nonneg hL hM))
      (mul_nonneg hq (tripleLip_nonneg (by norm_num) _)))
      (mul_nonneg hr (pairLip_nonneg (by norm_num) _))

theorem scaled_mul_abs_le {τ a x P : ℝ} (hτ : τ ∈ Icc 0 1)
    (ha : 0 ≤ a) (hx : |x| ≤ P) : |τ*a*x| ≤ a*P := by
  have hτa : 0 ≤ τ*a := mul_nonneg hτ.1 ha
  have ht : τ*a ≤ a := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ.2 ha
  rw [abs_mul,abs_of_nonneg hτa]
  exact mul_le_mul ht hx (abs_nonneg _) ha

theorem unit_slopes_abs_le {p : ℕ} (hp : 3 ≤ p) (β : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc 0 1) (f : State) {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) :
    |unitCorrelationSlope p β τ f t s| ≤ slopeBound p β ∧
    |unitResponseSlope p β τ f t s| ≤ slopeBound p β := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  let q : ℝ := β ^ 2*((p : ℝ)*((p : ℝ)-1))
  let r : ℝ := β ^ 2*(p : ℝ)
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg _) (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  have hr : 0 ≤ r := mul_nonneg (sq_nonneg _) hp0
  have hM : 0 ≤ fieldBound p β := le_trans (by norm_num) (fieldBound_ge_three p β)
  have hdc : |-(trialData p β τ f).multiplier t*trialC f t s| ≤ 2*fieldBound p β := by
    rw [abs_mul,abs_neg]
    have hh := mul_le_mul (trialMultiplier_abs_le p β hτ f ht) (trialC_abs_le f t s)
      (abs_nonneg _) hM
    simpa only [mul_comm] using hh
  have hdr : |-(trialData p β τ f).multiplier t*trialR f t s| ≤ 2*fieldBound p β := by
    rw [abs_mul,abs_neg]
    have hh := mul_le_mul (trialMultiplier_abs_le p β hτ f ht) (trialR_abs_le f t s)
      (abs_nonneg _) hM
    simpa only [mul_comm] using hh
  have hmem := trialMemory_abs_bounds p β τ f ht hs (p-2)
  have hforce := (trialMemory_abs_bounds p β τ f ht hs (p-1)).2.2
  have hcm := scaled_mul_abs_le hτ hq hmem.2.1
  have hrm := scaled_mul_abs_le hτ hq hmem.1
  have hfm := scaled_mul_abs_le hτ hr hforce
  have hCeq : unitCorrelationSlope p β τ f t s =
      -(trialData p β τ f).multiplier t*trialC f t s+
      τ*q*correlationMemory (p-2) (trialData p β τ f) t s+
      τ*r*forcingMemory (p-1) (trialData p β τ f) t s := by
    unfold unitCorrelationSlope; dsimp only [q,r]; ring
  have hReq : unitResponseSlope p β τ f t s =
      -(trialData p β τ f).multiplier t*trialR f t s+
      τ*q*responseMemory (p-2) (trialData p β τ f) t s := by
    unfold unitResponseSlope; dsimp only [q]; ring
  constructor
  · rw [hCeq]
    calc
      _ ≤ |-(trialData p β τ f).multiplier t*trialC f t s|+
          |τ*q*correlationMemory (p-2) (trialData p β τ f) t s|+
          |τ*r*forcingMemory (p-1) (trialData p β τ f) t s| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ 2*fieldBound p β+q*((2 : ℝ)^(p-2)*4)+r*((2 : ℝ)^(p-1)*2) :=
        add_le_add (add_le_add hdc hcm) hfm
      _ = slopeBound p β := rfl
  · rw [hReq]
    have hh := (abs_add_le _ _).trans (add_le_add hdr hrm)
    have hn : 0 ≤ r*((2 : ℝ)^(p-1)*2) := mul_nonneg hr
      (mul_nonneg (pow_nonneg (by norm_num) _) (by norm_num))
    exact hh.trans (by change _ ≤ 2*fieldBound p β+q*((2 : ℝ)^(p-2)*4)+r*((2 : ℝ)^(p-1)*2); linarith)

theorem unit_slopes_difference_le {p : ℕ} (hp : 3 ≤ p) (β : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc 0 1) (f g : State) {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) :
    |unitCorrelationSlope p β τ f t s-unitCorrelationSlope p β τ g t s| ≤ slopeLip p β*‖f-g‖ ∧
    |unitResponseSlope p β τ f t s-unitResponseSlope p β τ g t s| ≤ slopeLip p β*‖f-g‖ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  let q : ℝ := β ^ 2*((p : ℝ)*((p : ℝ)-1))
  let r : ℝ := β ^ 2*(p : ℝ)
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg _) (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  have hr : 0 ≤ r := mul_nonneg (sq_nonneg _) hp0
  have hM : 0 ≤ fieldBound p β := le_trans (by norm_num) (fieldBound_ge_three p β)
  have h2M : (2 : ℝ) ≤ fieldBound p β := le_trans (by norm_num) (fieldBound_ge_three p β)
  let A : ℝ := fieldBound p β+multiplierLip p β*fieldBound p β
  have hdc := damping_difference_le hM (multiplierLip_nonneg p β) (norm_nonneg (f-g))
    (trialMultiplier_abs_le p β hτ f ht) ((trialC_abs_le g t s).trans h2M)
    (trialC_difference_le f g t s) (trialMultiplier_difference_le p β hτ f g ht)
  have hdr := damping_difference_le hM (multiplierLip_nonneg p β) (norm_nonneg (f-g))
    (trialMultiplier_abs_le p β hτ f ht) ((trialR_abs_le g t s).trans h2M)
    (trialR_difference_le f g t s) (trialMultiplier_difference_le p β hτ f g ht)
  have hmem := trialMemory_difference_bounds p β τ f g ht hs (p-2)
  have hforce := (trialMemory_difference_bounds p β τ f g ht hs (p-1)).2.2
  have hcm := scaled_mul_abs_le hτ hq hmem.2.1
  have hrm := scaled_mul_abs_le hτ hq hmem.1
  have hfm := scaled_mul_abs_le hτ hr hforce
  have hCeq : unitCorrelationSlope p β τ f t s-unitCorrelationSlope p β τ g t s =
      (-(trialData p β τ f).multiplier t*trialC f t s)-
        (-(trialData p β τ g).multiplier t*trialC g t s)+
      τ*q*(correlationMemory (p-2) (trialData p β τ f) t s-correlationMemory (p-2) (trialData p β τ g) t s)+
      τ*r*(forcingMemory (p-1) (trialData p β τ f) t s-forcingMemory (p-1) (trialData p β τ g) t s) := by
    unfold unitCorrelationSlope; dsimp only [q,r]; ring
  have hReq : unitResponseSlope p β τ f t s-unitResponseSlope p β τ g t s =
      (-(trialData p β τ f).multiplier t*trialR f t s)-
        (-(trialData p β τ g).multiplier t*trialR g t s)+
      τ*q*(responseMemory (p-2) (trialData p β τ f) t s-responseMemory (p-2) (trialData p β τ g) t s) := by
    unfold unitResponseSlope; dsimp only [q]; ring
  constructor
  · rw [hCeq]
    calc
      _ ≤ |-(trialData p β τ f).multiplier t*trialC f t s-
          (-(trialData p β τ g).multiplier t*trialC g t s)|+
          |τ*q*(correlationMemory (p-2) (trialData p β τ f) t s-correlationMemory (p-2) (trialData p β τ g) t s)|+
          |τ*r*(forcingMemory (p-1) (trialData p β τ f) t s-forcingMemory (p-1) (trialData p β τ g) t s)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ A*‖f-g‖+q*(tripleLip 2 (p-2)*‖f-g‖)+r*(pairLip 2 (p-1)*‖f-g‖) :=
        add_le_add (add_le_add hdc hcm) hfm
      _ = slopeLip p β*‖f-g‖ := by dsimp only [slopeLip,A,q,r]; ring
  · rw [hReq]
    have hh := (abs_add_le _ _).trans (add_le_add hdr hrm)
    have hn : 0 ≤ r*pairLip 2 (p-1)*‖f-g‖ :=
      mul_nonneg (mul_nonneg hr (pairLip_nonneg (by norm_num) _)) (norm_nonneg _)
    calc
      _ ≤ A*‖f-g‖+q*(tripleLip 2 (p-2)*‖f-g‖) := hh
      _ ≤ slopeLip p β*‖f-g‖ := by
        change _ ≤ (A+q*tripleLip 2 (p-2)+r*pairLip 2 (p-1))*‖f-g‖
        nlinarith only [hn]

@[expose] def initialState : State := ContinuousMap.const Square (1,1)

theorem picardMap_near_initial {p : ℕ} (hp : 3 ≤ p) (β : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc 0 1) (f : State) :
    ‖picardMap p β τ f-initialState‖ ≤ τ*slopeBound p β := by
  have hN := (slope_constants_nonneg hp β).1
  apply (ContinuousMap.norm_le _ (mul_nonneg hτ.1 hN)).mpr
  intro z
  have hlow : min (z.1 : ℝ) (z.2 : ℝ) ∈ Icc 0 1 :=
    ⟨le_min z.1.2.1 z.2.2.1,(min_le_left _ _).trans z.1.2.2⟩
  have hhigh : max (z.1 : ℝ) (z.2 : ℝ) ∈ Icc 0 1 :=
    ⟨z.1.2.1.trans (le_max_left _ _),max_le z.1.2.2 z.2.2.2⟩
  have hlen : max (z.1 : ℝ) (z.2 : ℝ)-min (z.1 : ℝ) (z.2 : ℝ) ≤ 1 := by linarith [hlow.1,hhigh.2]
  have hC : |∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
      unitCorrelationSlope p β τ f u (min z.1 z.2)| ≤ slopeBound p β :=
    interval_integral_abs_le_unit min_le_max hN hlen
      (fun u hu => (unit_slopes_abs_le hp β hτ f ⟨hlow.1.trans hu.1,hu.2.trans hhigh.2⟩
        ⟨hlow.1,hu.1⟩).1)
  have hR : |∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
      unitResponseSlope p β τ f u (min z.1 z.2)| ≤ slopeBound p β :=
    interval_integral_abs_le_unit min_le_max hN hlen
      (fun u hu => (unit_slopes_abs_le hp β hτ f ⟨hlow.1.trans hu.1,hu.2.trans hhigh.2⟩
        ⟨hlow.1,hu.1⟩).2)
  rw [norm_prod_le_iff]
  constructor
  · change |(1+τ*_)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg hτ.1]
    exact mul_le_mul_of_nonneg_left hC hτ.1
  · change |(1+τ*_)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg hτ.1]
    exact mul_le_mul_of_nonneg_left hR hτ.1

theorem picardMap_difference_le {p : ℕ} (hp : 3 ≤ p) (β : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc 0 1) (f g : State) :
    ‖picardMap p β τ f-picardMap p β τ g‖ ≤ (τ*slopeLip p β)*‖f-g‖ := by
  have hK := (slope_constants_nonneg hp β).2
  have hδ := norm_nonneg (f-g)
  have hKd : 0 ≤ slopeLip p β*‖f-g‖ := mul_nonneg hK hδ
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg hτ.1 hK) hδ)).mpr
  intro z
  have hlow : min (z.1 : ℝ) (z.2 : ℝ) ∈ Icc 0 1 :=
    ⟨le_min z.1.2.1 z.2.2.1,(min_le_left _ _).trans z.1.2.2⟩
  have hhigh : max (z.1 : ℝ) (z.2 : ℝ) ∈ Icc 0 1 :=
    ⟨z.1.2.1.trans (le_max_left _ _),max_le z.1.2.2 z.2.2.2⟩
  have hlen : max (z.1 : ℝ) (z.2 : ℝ)-min (z.1 : ℝ) (z.2 : ℝ) ≤ 1 := by linarith [hlow.1,hhigh.2]
  have hci (h : State) : IntervalIntegrable
      (fun u => unitCorrelationSlope p β τ h u (min (z.1 : ℝ) (z.2 : ℝ))) volume
        (min (z.1 : ℝ) (z.2 : ℝ)) (max (z.1 : ℝ) (z.2 : ℝ)) :=
    ((unitCorrelationSlope_continuous p β τ h).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have hri (h : State) : IntervalIntegrable
      (fun u => unitResponseSlope p β τ h u (min (z.1 : ℝ) (z.2 : ℝ))) volume
        (min (z.1 : ℝ) (z.2 : ℝ)) (max (z.1 : ℝ) (z.2 : ℝ)) :=
    ((unitResponseSlope_continuous p β τ h).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have hC := interval_integral_difference_le min_le_max (hci f) (hci g)
    (fun u hu => (unit_slopes_difference_le hp β hτ f g ⟨hlow.1.trans hu.1,hu.2.trans hhigh.2⟩
      ⟨hlow.1,hu.1⟩).1)
  have hR := interval_integral_difference_le min_le_max (hri f) (hri g)
    (fun u hu => (unit_slopes_difference_le hp β hτ f g ⟨hlow.1.trans hu.1,hu.2.trans hhigh.2⟩
      ⟨hlow.1,hu.1⟩).2)
  have hC' := hC.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlen hKd)
  have hR' := hR.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlen hKd)
  rw [norm_prod_le_iff]
  constructor
  · change |(1+τ*_)-(1+τ*_)| ≤ _
    have heq (a b : ℝ) : (1+τ*a)-(1+τ*b)=τ*(a-b) := by ring
    rw [heq,abs_mul,abs_of_nonneg hτ.1,mul_assoc]
    exact mul_le_mul_of_nonneg_left hC' hτ.1
  · change |(1+τ*_)-(1+τ*_)| ≤ _
    have heq (a b : ℝ) : (1+τ*a)-(1+τ*b)=τ*(a-b) := by ring
    rw [heq,abs_mul,abs_of_nonneg hτ.1,mul_assoc]
    exact mul_le_mul_of_nonneg_left hR' hτ.1

@[expose] def localHorizon (p : ℕ) (β : ℝ) : ℝ := 1/(4*(slopeBound p β+slopeLip p β+1))

theorem localHorizon_bounds {p : ℕ} (hp : 3 ≤ p) (β : ℝ) :
    0 < localHorizon p β ∧ localHorizon p β ≤ 1 ∧
      localHorizon p β*slopeBound p β ≤ 1/4 ∧
      localHorizon p β*slopeLip p β ≤ 1/4 := by
  obtain ⟨hN,hK⟩ := slope_constants_nonneg hp β
  have hd : 0 < 4*(slopeBound p β+slopeLip p β+1) := by linarith
  have hτ : 0 < localHorizon p β := one_div_pos.mpr hd
  have heq : localHorizon p β*(4*(slopeBound p β+slopeLip p β+1))=1 :=
    by dsimp only [localHorizon]; field_simp
  refine ⟨hτ,?_,?_,?_⟩ <;> nlinarith [mul_nonneg hτ.le hN,mul_nonneg hτ.le hK]

theorem picardMap_contracting {p : ℕ} (hp : 3 ≤ p) (β : ℝ) :
    ContractingWith ⟨localHorizon p β*slopeLip p β,
      mul_nonneg (localHorizon_bounds hp β).1.le (slope_constants_nonneg hp β).2⟩
      (picardMap p β (localHorizon p β)) := by
  refine ⟨?_,LipschitzWith.of_dist_le_mul ?_⟩
  · change localHorizon p β*slopeLip p β < 1
    linarith [(localHorizon_bounds hp β).2.2.2]
  · intro f g
    change dist (picardMap p β (localHorizon p β) f) (picardMap p β (localHorizon p β) g) ≤
      (localHorizon p β*slopeLip p β)*dist f g
    rw [dist_eq_norm,dist_eq_norm]
    exact picardMap_difference_le hp β
      ⟨(localHorizon_bounds hp β).1.le,(localHorizon_bounds hp β).2.1⟩ f g

/-- The Picard fixed point exists in the actual continuous-function space.
The displacement bound will discharge the truncation in the CK equations. -/
theorem local_picard_fixed_point {p : ℕ} (hp : 3 ≤ p) (β : ℝ) :
    ∃ f : State, picardMap p β (localHorizon p β) f=f ∧ ‖f-initialState‖ ≤ 1/4 := by
  let f := ContractingWith.fixedPoint (picardMap p β (localHorizon p β)) (picardMap_contracting hp β)
  have hfix : picardMap p β (localHorizon p β) f=f :=
    (picardMap_contracting hp β).fixedPoint_isFixedPt.eq
  refine ⟨f,hfix,?_⟩
  rw [← hfix]
  exact (picardMap_near_initial hp β
    ⟨(localHorizon_bounds hp β).1.le,(localHorizon_bounds hp β).2.1⟩ f).trans
      (localHorizon_bounds hp β).2.2.1

theorem state_components_near_one {f : State} (hf : ‖f-initialState‖ ≤ 1/4) (z : Square) :
    |(f z).1-1| ≤ 1/4 ∧ |(f z).2-1| ≤ 1/4 := by
  have hh : ‖f z-(1,1)‖ ≤ 1/4 := ((f-initialState).norm_coe_le_norm z).trans hf
  constructor
  · have hx : |(f z).1-1| ≤ ‖f z-(1,1)‖ := by
      have hx := norm_fst_le (f z-(1,1) : ℝ × ℝ)
      change ‖(f z).1-1‖ ≤ ‖f z-(1,1)‖ at hx
      rwa [Real.norm_eq_abs] at hx
    exact hx.trans hh
  · have hx : |(f z).2-1| ≤ ‖f z-(1,1)‖ := by
      have hx := norm_snd_le (f z-(1,1) : ℝ × ℝ)
      change ‖(f z).2-1‖ ≤ ‖f z-(1,1)‖ at hx
      rwa [Real.norm_eq_abs] at hx
    exact hx.trans hh

theorem trialC_unclipped {f : State} (hf : ‖f-initialState‖ ≤ 1/4) (t s : ℝ) :
    trialC f t s=(sample f t s).1 := by
  have hh := (state_components_near_one hf (clampTime (max t s),clampTime (min t s))).1
  apply clipValue_eq
  have hb := abs_le.mp hh
  constructor <;> dsimp only [sample] <;> linarith [hb.1,hb.2]

theorem trialR_unclipped {f : State} (hf : ‖f-initialState‖ ≤ 1/4) (t s : ℝ) :
    trialR f t s=(sample f t s).2 := by
  have hh := (state_components_near_one hf (clampTime (max t s),clampTime (min t s))).2
  apply clipValue_eq
  have hb := abs_le.mp hh
  constructor <;> dsimp only [sample] <;> linarith [hb.1,hb.2]

theorem trial_positive_bounds {f : State} (hf : ‖f-initialState‖ ≤ 1/4) (t s : ℝ) :
    (3/4 ≤ trialC f t s ∧ trialC f t s ≤ 5/4) ∧
      (3/4 ≤ trialR f t s ∧ trialR f t s ≤ 5/4) := by
  rw [trialC_unclipped hf,trialR_unclipped hf]
  have hh := state_components_near_one hf (clampTime (max t s),clampTime (min t s))
  have hc := abs_le.mp hh.1
  have hr := abs_le.mp hh.2
  dsimp only [sample]
  constructor <;> constructor <;> linarith [hc.1,hc.2,hr.1,hr.2]

theorem fixed_trial_integral_equations {p : ℕ} {β τ : ℝ} {f : State}
    (hfix : picardMap p β τ f=f) (hf : ‖f-initialState‖ ≤ 1/4)
    {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) :
    trialC f t s=1+τ*(∫ u in s..t, unitCorrelationSlope p β τ f u s) ∧
      trialR f t s=1+τ*(∫ u in s..t, unitResponseSlope p β τ f u s) := by
  have hs1 : s ∈ Icc 0 1 := ⟨hs.1,hs.2.trans ht.2⟩
  have hh := congrArg (fun h : State => h (clampTime t,clampTime s)) hfix
  change picardValues p β τ f (clampTime t) (clampTime s)=f (clampTime t,clampTime s) at hh
  rw [clampTime_eq ht,clampTime_eq hs1] at hh
  rw [trialC_unclipped hf,trialR_unclipped hf]
  simp only [sample,max_eq_left hs.2,min_eq_right hs.2]
  constructor
  · have hx := congrArg Prod.fst hh.symm
    simpa only [picardValues,max_eq_left hs.2,min_eq_right hs.2] using hx
  · have hx := congrArg Prod.snd hh.symm
    simpa only [picardValues,max_eq_left hs.2,min_eq_right hs.2] using hx

theorem fixed_trial_derivatives {p : ℕ} {β τ : ℝ} {f : State}
    (hfix : picardMap p β τ f=f) (hf : ‖f-initialState‖ ≤ 1/4)
    {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) :
    HasDerivWithinAt (fun x => trialC f x s) (τ*unitCorrelationSlope p β τ f t s) (Icc s 1) t ∧
    HasDerivWithinAt (fun x => trialR f x s) (τ*unitResponseSlope p β τ f t s) (Icc s 1) t := by
  have hC : Continuous (fun x => unitCorrelationSlope p β τ f x s) :=
    (unitCorrelationSlope_continuous p β τ f).comp (continuous_id.prodMk continuous_const)
  have hR : Continuous (fun x => unitResponseSlope p β τ f x s) :=
    (unitResponseSlope_continuous p β τ f).comp (continuous_id.prodMk continuous_const)
  have hdC := (intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable s t)
    hC.aestronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt).const_mul τ |>.const_add 1
  have hdR := (intervalIntegral.integral_hasDerivAt_right (hR.intervalIntegrable s t)
    hR.aestronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt).const_mul τ |>.const_add 1
  constructor
  · exact hdC.hasDerivWithinAt.congr
      (fun x hx => (fixed_trial_integral_equations hfix hf ⟨hs.1.trans hx.1,hx.2⟩ ⟨hs.1,hx.1⟩).1)
      (fixed_trial_integral_equations hfix hf ht hs).1
  · exact hdR.hasDerivWithinAt.congr
      (fun x hx => (fixed_trial_integral_equations hfix hf ⟨hs.1.trans hx.1,hx.2⟩ ⟨hs.1,hx.1⟩).2)
      (fixed_trial_integral_equations hfix hf ht hs).2

@[expose] def physicalData (p : ℕ) (β τ : ℝ) (f : State) : CKData where
  C := fun t s => trialC f (t/τ) (s/τ)
  R := fun t s => trialR f (t/τ) (s/τ)
  multiplier := fun t => (trialData p β τ f).multiplier (t/τ)

theorem physical_memory_scale (p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ≠ 0) (f : State) (t : ℝ) :
    memoryMass p (physicalData p β τ f) t=τ*memoryMass p (trialData p β τ f) (t/τ) := by
  have hh := intervalIntegral.integral_comp_div
    (fun u => trialC f (t/τ) u ^ (p-1)*trialR f (t/τ) u) (a := 0) (b := t) hτ
  simpa only [memoryMass,physicalData,trialData,zero_div,smul_eq_mul] using hh

theorem physical_responseMemory_scale (n p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ≠ 0)
    (f : State) (t s : ℝ) :
    responseMemory n (physicalData p β τ f) t s=τ*responseMemory n (trialData p β τ f) (t/τ) (s/τ) := by
  have hh := intervalIntegral.integral_comp_div
    (fun u => trialC f (t/τ) u ^ n*trialR f (t/τ) u*trialR f u (s/τ)) (a := s) (b := t) hτ
  simpa only [responseMemory,physicalData,trialData,smul_eq_mul] using hh

theorem physical_correlationMemory_scale (n p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ≠ 0)
    (f : State) (t s : ℝ) :
    correlationMemory n (physicalData p β τ f) t s=τ*correlationMemory n (trialData p β τ f) (t/τ) (s/τ) := by
  have hh := intervalIntegral.integral_comp_div
    (fun u => trialC f (t/τ) u ^ n*trialR f (t/τ) u*trialC f u (s/τ)) (a := 0) (b := t) hτ
  simpa only [correlationMemory,physicalData,trialData,zero_div,smul_eq_mul] using hh

theorem physical_forcingMemory_scale (n p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ≠ 0)
    (f : State) (t s : ℝ) :
    forcingMemory n (physicalData p β τ f) t s=τ*forcingMemory n (trialData p β τ f) (t/τ) (s/τ) := by
  have hh := intervalIntegral.integral_comp_div
    (fun u => trialC f (t/τ) u ^ n*trialR f (s/τ) u) (a := 0) (b := s) hτ
  simpa only [forcingMemory,physicalData,trialData,zero_div,smul_eq_mul] using hh

theorem physical_multiplier_eq (p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ≠ 0)
    (f : State) (t : ℝ) :
    (physicalData p β τ f).multiplier t=1+β ^ 2*(p : ℝ)^2*memoryMass p (physicalData p β τ f) t := by
  rw [physical_memory_scale p β hτ]
  change 1+τ*β ^ 2*(p : ℝ)^2*memoryMass p (trialData p β τ f) (t/τ)=_
  ring

theorem physical_slopes_eq (p : ℕ) (β : ℝ) {τ : ℝ} (hτ : τ ≠ 0)
    (f : State) (t s : ℝ) :
    correlationSlope p β (physicalData p β τ f) t s=unitCorrelationSlope p β τ f (t/τ) (s/τ) ∧
      responseSlope p β (physicalData p β τ f) t s=unitResponseSlope p β τ f (t/τ) (s/τ) := by
  constructor
  · rw [correlationSlope_normalized,physical_correlationMemory_scale _ _ _ hτ,
      physical_forcingMemory_scale _ _ _ hτ]
    unfold unitCorrelationSlope
    dsimp only [physicalData]
    ring
  · rw [responseSlope_normalized,physical_responseMemory_scale _ _ _ hτ]
    unfold unitResponseSlope
    dsimp only [physicalData]
    ring

/-- The actual CK equations on a finite horizon. Derivatives are taken within
the closed horizon; values outside that horizon are continuous extensions. -/
structure CKOnHorizon (p : ℕ) (β T : ℝ) (d : CKData) : Prop where
  spin_ge_three : 3 ≤ p
  beta_pos : 0 < β
  horizon_pos : 0 < T
  correlation_continuous : Continuous (Function.uncurry d.C)
  response_continuous : Continuous (Function.uncurry d.R)
  multiplier_continuous : Continuous d.multiplier
  correlation_symmetric : ∀ t s, d.C t s=d.C s t
  correlation_diagonal : ∀ t ∈ Icc 0 T, d.C t t=1
  response_diagonal : ∀ t ∈ Icc 0 T, d.R t t=1
  multiplier_eq : ∀ t ∈ Icc 0 T,
    d.multiplier t=1+β ^ 2*(p : ℝ)^2*memoryMass p d t
  correlation_derivative : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t,
    HasDerivWithinAt (fun u => d.C u s) (correlationSlope p β d t s) (Icc s T) t
  response_derivative : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t,
    HasDerivWithinAt (fun u => d.R u s) (responseSlope p β d t s) (Icc s T) t
  correlation_slope_continuous : Continuous (Function.uncurry (correlationSlope p β d))
  response_slope_continuous : Continuous (Function.uncurry (responseSlope p β d))

theorem physical_derivatives {p : ℕ} {β τ : ℝ} {f : State}
    (hτ : 0 < τ) (hfix : picardMap p β τ f=f) (hf : ‖f-initialState‖ ≤ 1/4)
    {t s : ℝ} (ht : t ∈ Icc 0 τ) (hs : s ∈ Icc 0 t) :
    HasDerivWithinAt (fun x => (physicalData p β τ f).C x s)
      (correlationSlope p β (physicalData p β τ f) t s) (Icc s τ) t ∧
    HasDerivWithinAt (fun x => (physicalData p β τ f).R x s)
      (responseSlope p β (physicalData p β τ f) t s) (Icc s τ) t := by
  have ht' : t/τ ∈ Icc 0 1 := ⟨div_nonneg ht.1 hτ.le,(div_le_one₀ hτ).mpr ht.2⟩
  have hs' : s/τ ∈ Icc 0 (t/τ) := ⟨div_nonneg hs.1 hτ.le,(div_le_div_iff_of_pos_right hτ).mpr hs.2⟩
  have hmaps : MapsTo (fun x => x/τ) (Icc s τ) (Icc (s/τ) 1) := by
    intro x hx
    exact ⟨(div_le_div_iff_of_pos_right hτ).mpr hx.1,(div_le_one₀ hτ).mpr hx.2⟩
  have hdscalar : HasDerivWithinAt (fun x : ℝ => x/τ) (1/τ) (Icc s τ) t :=
    ((hasDerivAt_id t).div_const τ).hasDerivWithinAt
  have hunit := fixed_trial_derivatives hfix hf ht' hs'
  have hdc := hunit.1.comp t hdscalar hmaps
  have hdr := hunit.2.comp t hdscalar hmaps
  have hcancel (a : ℝ) : (τ*a)*(1/τ)=a := by field_simp [hτ.ne']
  rw [hcancel] at hdc hdr
  rw [(physical_slopes_eq p β hτ.ne' f t s).1,
    (physical_slopes_eq p β hτ.ne' f t s).2]
  exact ⟨hdc,hdr⟩

theorem physicalCK_on_horizon {p : ℕ} (hp : 3 ≤ p) {β τ : ℝ} (hβ : 0 < β)
    (hτ : 0 < τ) {f : State} (hfix : picardMap p β τ f=f) (hf : ‖f-initialState‖ ≤ 1/4) :
    CKOnHorizon p β τ (physicalData p β τ f) := by
  have hC : Continuous (Function.uncurry (physicalData p β τ f).C) :=
    (trialC_continuous f).comp ((continuous_fst.div_const τ).prodMk (continuous_snd.div_const τ))
  have hR : Continuous (Function.uncurry (physicalData p β τ f).R) :=
    (trialR_continuous f).comp ((continuous_fst.div_const τ).prodMk (continuous_snd.div_const τ))
  have hCS : Continuous (Function.uncurry (correlationSlope p β (physicalData p β τ f))) := by
    apply ((unitCorrelationSlope_continuous p β τ f).comp
      ((continuous_fst.div_const τ).prodMk (continuous_snd.div_const τ))).congr
    intro z
    exact (physical_slopes_eq p β hτ.ne' f z.1 z.2).1.symm
  have hRS : Continuous (Function.uncurry (responseSlope p β (physicalData p β τ f))) := by
    apply ((unitResponseSlope_continuous p β τ f).comp
      ((continuous_fst.div_const τ).prodMk (continuous_snd.div_const τ))).congr
    intro z
    exact (physical_slopes_eq p β hτ.ne' f z.1 z.2).2.symm
  refine ⟨hp,hβ,hτ,hC,hR,(trialMultiplier_continuous p β τ f).comp (continuous_id.div_const τ),
    ?_,?_,?_,?_,?_,?_,hCS,hRS⟩
  · intro t s
    exact trialC_symmetric f (t/τ) (s/τ)
  · intro t ht
    have ht' : t/τ ∈ Icc 0 1 := ⟨div_nonneg ht.1 hτ.le,(div_le_one₀ hτ).mpr ht.2⟩
    have hh := (fixed_trial_integral_equations hfix hf ht' ⟨ht'.1,le_refl (t/τ)⟩).1
    simpa only [physicalData,intervalIntegral.integral_same,mul_zero,add_zero] using hh
  · intro t ht
    have ht' : t/τ ∈ Icc 0 1 := ⟨div_nonneg ht.1 hτ.le,(div_le_one₀ hτ).mpr ht.2⟩
    have hh := (fixed_trial_integral_equations hfix hf ht' ⟨ht'.1,le_refl (t/τ)⟩).2
    simpa only [physicalData,intervalIntegral.integral_same,mul_zero,add_zero] using hh
  · intro t _
    exact physical_multiplier_eq p β hτ.ne' f t
  · intro t ht s hs
    exact (physical_derivatives hτ hfix hf ht hs).1
  · intro t ht s hs
    exact (physical_derivatives hτ hfix hf ht hs).2

/-- Unconditional local existence for the manuscript's actual CK equations,
with an explicit positive horizon. The values lie strictly inside the Picard
truncation interval, so all displayed derivatives use the original polynomials. -/
theorem ck_local_existence {p : ℕ} (hp : 3 ≤ p) {β : ℝ} (hβ : 0 < β) :
    ∃ d : CKData, CKOnHorizon p β (localHorizon p β) d ∧
      (∀ t s, (3/4 ≤ d.C t s ∧ d.C t s ≤ 5/4) ∧
        (3/4 ≤ d.R t s ∧ d.R t s ≤ 5/4)) := by
  obtain ⟨f,hfix,hf⟩ := local_picard_fixed_point hp β
  refine ⟨physicalData p β (localHorizon p β) f,
    physicalCK_on_horizon hp hβ (localHorizon_bounds hp β).1 hfix hf,?_⟩
  intro t s
  exact trial_positive_bounds hf (t/localHorizon p β) (s/localHorizon p β)

end SphericalAging.CKLocalExistence
