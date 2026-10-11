module

public import SphericalAging.CKLocalExistence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

/-!
# Picard construction on arbitrary finite horizons

An exponential weight controls the causal Volterra operator on an arbitrary
finite horizon. The truncation is retained during the Banach construction;
its removal requires the physical bounds on the untruncated prefixes.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace SphericalAging.CKContinuation
open CKSpecification CKWellposedness CKLocalExistence

theorem square_memory_difference_bounds (p : ℕ) (γ : ℝ) (f g : State) {t s δ : ℝ}
    (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) (hδ : 0 ≤ δ)
    (hC : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, |trialC f u v-trialC g u v| ≤ δ)
    (hR : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, |trialR f u v-trialR g u v| ≤ δ) (n : ℕ) :
    |responseMemory n (trialData p γ 1 f) t s-responseMemory n (trialData p γ 1 g) t s| ≤
        tripleLip 2 n*δ ∧
    |correlationMemory n (trialData p γ 1 f) t s-correlationMemory n (trialData p γ 1 g) t s| ≤
        tripleLip 2 n*δ ∧
    |forcingMemory n (trialData p γ 1 f) t s-forcingMemory n (trialData p γ 1 g) t s| ≤
        pairLip 2 n*δ := by
  have htt : t ∈ Icc 0 t := ⟨ht.1,le_refl t⟩
  have hRpoint (u : ℝ) (hu : u ∈ Icc s t) := power_triple_difference_le
    (by norm_num : (0 : ℝ) ≤ 2) hδ (trialC_abs_le f t u) (trialC_abs_le g t u)
    (trialR_abs_le f t u) (trialR_abs_le g t u) (trialR_abs_le f u s) (trialR_abs_le g u s)
    (hC t htt u ⟨hs.1.trans hu.1,hu.2⟩) (hR t htt u ⟨hs.1.trans hu.1,hu.2⟩)
    (hR u ⟨hs.1.trans hu.1,hu.2⟩ s hs) n
  have hCpoint (u : ℝ) (hu : u ∈ Icc 0 t) := power_triple_difference_le
    (by norm_num : (0 : ℝ) ≤ 2) hδ (trialC_abs_le f t u) (trialC_abs_le g t u)
    (trialR_abs_le f t u) (trialR_abs_le g t u) (trialC_abs_le f u s) (trialC_abs_le g u s)
    (hC t htt u hu) (hR t htt u hu) (hC u hu s hs) n
  have hFpoint (u : ℝ) (hu : u ∈ Icc 0 s) := power_product_difference_le
    (by norm_num : (0 : ℝ) ≤ 2) hδ (trialC_abs_le f t u) (trialC_abs_le g t u)
    (trialR_abs_le f s u) (trialR_abs_le g s u)
    (hC t htt u ⟨hu.1,hu.2.trans hs.2⟩) (hR s hs u ⟨hu.1,hu.2.trans hs.2⟩) n
  have htr : 0 ≤ tripleLip 2 n*δ := mul_nonneg (tripleLip_nonneg (by norm_num) _) hδ
  have hpr : 0 ≤ pairLip 2 n*δ := mul_nonneg (pairLip_nonneg (by norm_num) _) hδ
  refine ⟨?_,?_,?_⟩
  · have hh := interval_integral_difference_le hs.2
      (trialResponse_integrable f n t s s t) (trialResponse_integrable g n t s s t) hRpoint
    exact hh.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show t-s ≤ 1 by linarith [ht.2,hs.1]) htr)
  · have hh := interval_integral_difference_le ht.1
      (trialCorrelation_integrable f n t s 0 t) (trialCorrelation_integrable g n t s 0 t) hCpoint
    exact hh.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show t-0 ≤ 1 by simpa using ht.2) htr)
  · have hh := interval_integral_difference_le hs.1
      (trialPair_integrable f n t s 0 s) (trialPair_integrable g n t s 0 s) hFpoint
    exact hh.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show s-0 ≤ 1 by simpa using hs.2.trans ht.2) hpr)

theorem square_multiplier_difference_le (p : ℕ) (γ : ℝ) (f g : State) {t δ : ℝ}
    (ht : t ∈ Icc 0 1) (hδ : 0 ≤ δ)
    (hC : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, |trialC f u v-trialC g u v| ≤ δ)
    (hR : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, |trialR f u v-trialR g u v| ≤ δ) :
    |(trialData p γ 1 f).multiplier t-(trialData p γ 1 g).multiplier t| ≤ multiplierLip p γ*δ := by
  have htt : t ∈ Icc 0 t := ⟨ht.1,le_refl t⟩
  have hi := interval_integral_difference_le ht.1
    (trialPair_integrable f (p-1) t t 0 t) (trialPair_integrable g (p-1) t t 0 t)
    (fun u hu => power_product_difference_le (by norm_num : (0 : ℝ) ≤ 2) hδ
      (trialC_abs_le f t u) (trialC_abs_le g t u) (trialR_abs_le f t u) (trialR_abs_le g t u)
      (hC t htt u hu) (hR t htt u hu) (p-1))
  have hi' : |(∫ u in (0 : ℝ)..t, trialC f t u ^ (p-1)*trialR f t u)-
      (∫ u in (0 : ℝ)..t, trialC g t u ^ (p-1)*trialR g t u)| ≤ pairLip 2 (p-1)*δ :=
    hi.trans (by
      have hpr : 0 ≤ pairLip 2 (p-1)*δ := mul_nonneg (pairLip_nonneg (by norm_num) _) hδ
      simpa only [sub_zero,one_mul] using mul_le_mul_of_nonneg_right ht.2 hpr)
  have ha : 0 ≤ γ ^ 2*(p : ℝ)^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have heq (a b : ℝ) : (1+1*γ ^ 2*(p : ℝ)^2*a)-(1+1*γ ^ 2*(p : ℝ)^2*b) =
      (γ ^ 2*(p : ℝ)^2)*(a-b) := by ring
  change |(1+1*γ ^ 2*(p : ℝ)^2*_)-(1+1*γ ^ 2*(p : ℝ)^2*_)| ≤ _
  rw [heq,abs_mul,abs_of_nonneg ha]
  have hh := mul_le_mul_of_nonneg_left hi' ha
  simpa only [multiplierLip,mul_assoc] using hh


theorem square_unit_slopes_difference_le {p : ℕ} (hp : 3 ≤ p) (β : ℝ)
    (f g : State) {t s δ : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) (hδ : 0 ≤ δ)
    (hC : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, |trialC f u v-trialC g u v| ≤ δ)
    (hR : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, |trialR f u v-trialR g u v| ≤ δ) :
    |unitCorrelationSlope p β 1 f t s-unitCorrelationSlope p β 1 g t s| ≤ slopeLip p β*δ ∧
    |unitResponseSlope p β 1 f t s-unitResponseSlope p β 1 g t s| ≤ slopeLip p β*δ := by
  let τ : ℝ := 1
  have hτ : τ ∈ Icc 0 1 := by norm_num [τ]

  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  let q : ℝ := β ^ 2*((p : ℝ)*((p : ℝ)-1))
  let r : ℝ := β ^ 2*(p : ℝ)
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg _) (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  have hr : 0 ≤ r := mul_nonneg (sq_nonneg _) hp0
  have hM : 0 ≤ fieldBound p β := le_trans (by norm_num) (fieldBound_ge_three p β)
  have h2M : (2 : ℝ) ≤ fieldBound p β := le_trans (by norm_num) (fieldBound_ge_three p β)
  let A : ℝ := fieldBound p β+multiplierLip p β*fieldBound p β
  have hdc := damping_difference_le hM (multiplierLip_nonneg p β) hδ
    (trialMultiplier_abs_le p β hτ f ht) ((trialC_abs_le g t s).trans h2M)
    (hC t ⟨ht.1,le_refl t⟩ s hs) (square_multiplier_difference_le p β f g ht hδ hC hR)
  have hdr := damping_difference_le hM (multiplierLip_nonneg p β) hδ
    (trialMultiplier_abs_le p β hτ f ht) ((trialR_abs_le g t s).trans h2M)
    (hR t ⟨ht.1,le_refl t⟩ s hs) (square_multiplier_difference_le p β f g ht hδ hC hR)
  have hmem := square_memory_difference_bounds p β f g ht hs hδ hC hR (p-2)
  have hforce := (square_memory_difference_bounds p β f g ht hs hδ hC hR (p-1)).2.2
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
      _ ≤ A*δ+q*(tripleLip 2 (p-2)*δ)+r*(pairLip 2 (p-1)*δ) :=
        add_le_add (add_le_add hdc hcm) hfm
      _ = slopeLip p β*δ := by dsimp only [slopeLip,A,q,r]; ring
  · rw [hReq]
    have hh := (abs_add_le _ _).trans (add_le_add hdr hrm)
    have hn : 0 ≤ r*pairLip 2 (p-1)*δ :=
      mul_nonneg (mul_nonneg hr (pairLip_nonneg (by norm_num) _)) hδ
    calc
      _ ≤ A*δ+q*(tripleLip 2 (p-2)*δ) := hh
      _ ≤ slopeLip p β*δ := by
        change _ ≤ (A+q*tripleLip 2 (p-2)+r*pairLip 2 (p-1))*δ
        nlinarith only [hn]

@[expose] def weightedState (α : ℝ) (f : State) : State :=
  ⟨fun z => Real.exp (-α*max (z.1 : ℝ) (z.2 : ℝ)) • f z,
    by
      have hw : Continuous (fun z : Square => Real.exp (-α*max (z.1 : ℝ) (z.2 : ℝ))) := by fun_prop
      exact hw.smul f.continuous⟩

@[expose] def unweightedState (α : ℝ) (f : State) : State :=
  ⟨fun z => Real.exp (α*max (z.1 : ℝ) (z.2 : ℝ)) • f z,
    by
      have hw : Continuous (fun z : Square => Real.exp (α*max (z.1 : ℝ) (z.2 : ℝ))) := by fun_prop
      exact hw.smul f.continuous⟩

theorem unweighted_weighted (α : ℝ) (f : State) : unweightedState α (weightedState α f)=f := by
  apply ContinuousMap.ext
  intro z
  change Real.exp (α*max (z.1 : ℝ) (z.2 : ℝ)) •
    (Real.exp (-α*max (z.1 : ℝ) (z.2 : ℝ)) • f z)=f z
  rw [smul_smul,← Real.exp_add]
  have heq : α*max (z.1 : ℝ) (z.2 : ℝ)+(-α*max (z.1 : ℝ) (z.2 : ℝ))=0 := by ring
  simp only [heq,Real.exp_zero,one_smul]

theorem sample_unweighted {α : ℝ} (f : State) {u v : ℝ}
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    sample (unweightedState α f) u v=Real.exp (α*max u v) • sample f u v := by
  have hmax : max u v ∈ Icc 0 1 := ⟨hu.1.trans (le_max_left _ _),max_le hu.2 hv.2⟩
  have hmin : min u v ∈ Icc 0 1 := ⟨le_min hu.1 hv.1,(min_le_left _ _).trans hu.2⟩
  change Real.exp (α*max (clampTime (max u v) : ℝ) (clampTime (min u v) : ℝ)) •
    f (clampTime (max u v),clampTime (min u v))=_
  rw [clampTime_eq hmax,clampTime_eq hmin,max_eq_left min_le_max]
  rfl

theorem weighted_sample_difference_le {α : ℝ} (hα : 0 ≤ α) (f g : State)
    {t u v : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
    ‖sample (unweightedState α f) u v-sample (unweightedState α g) u v‖ ≤
      Real.exp (α*t)*‖f-g‖ := by
  rw [sample_unweighted f ⟨hu.1,hu.2.trans ht.2⟩ ⟨hv.1,hv.2.trans ht.2⟩,
    sample_unweighted g ⟨hu.1,hu.2.trans ht.2⟩ ⟨hv.1,hv.2.trans ht.2⟩,
    ← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (α*max u v) ≤ Real.exp (α*t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (max_le hu.2 hv.2) hα)
  exact mul_le_mul hexp (sample_difference_le f g u v) (norm_nonneg _) (Real.exp_pos _).le

theorem trialC_difference_le_sample (f g : State) (u v : ℝ) :
    |trialC f u v-trialC g u v| ≤ ‖sample f u v-sample g u v‖ := by
  have hclip := clipValue_lipschitz.dist_le_mul (sample f u v).1 (sample g u v).1
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hclip
  have hfst := norm_fst_le (sample f u v-sample g u v : ℝ × ℝ)
  change ‖(sample f u v).1-(sample g u v).1‖ ≤ _ at hfst
  rw [Real.norm_eq_abs] at hfst
  exact hclip.trans hfst

theorem trialR_difference_le_sample (f g : State) (u v : ℝ) :
    |trialR f u v-trialR g u v| ≤ ‖sample f u v-sample g u v‖ := by
  have hclip := clipValue_lipschitz.dist_le_mul (sample f u v).2 (sample g u v).2
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hclip
  have hsnd := norm_snd_le (sample f u v-sample g u v : ℝ × ℝ)
  change ‖(sample f u v).2-(sample g u v).2‖ ≤ _ at hsnd
  rw [Real.norm_eq_abs] at hsnd
  exact hclip.trans hsnd

theorem weighted_slopes_difference_le {p : ℕ} (hp : 3 ≤ p) (γ : ℝ) {α : ℝ}
    (hα : 0 ≤ α) (f g : State) {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) :
    |unitCorrelationSlope p γ 1 (unweightedState α f) t s-
      unitCorrelationSlope p γ 1 (unweightedState α g) t s| ≤ slopeLip p γ*(Real.exp (α*t)*‖f-g‖) ∧
    |unitResponseSlope p γ 1 (unweightedState α f) t s-
      unitResponseSlope p γ 1 (unweightedState α g) t s| ≤ slopeLip p γ*(Real.exp (α*t)*‖f-g‖) :=
  square_unit_slopes_difference_le hp γ _ _ ht hs
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun u hu v hv => (trialC_difference_le_sample _ _ u v).trans
      (weighted_sample_difference_le hα f g ht hu hv))
    (fun u hu v hv => (trialR_difference_le_sample _ _ u v).trans
      (weighted_sample_difference_le hα f g ht hu hv))

theorem exp_weighted_integral_le {α s t : ℝ} (hα : 0 < α) :
    Real.exp (-α*t)*(∫ u in s..t, Real.exp (α*u)) ≤ 1/α := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hα.ne',integral_exp,smul_eq_mul]
  have hcancel : Real.exp (-α*t)*Real.exp (α*t)=1 := by
    rw [← Real.exp_add]
    have heq : -α*t+α*t=0 := by ring
    simp only [heq,Real.exp_zero]
  have hnon : 0 ≤ Real.exp (-α*t)*Real.exp (α*s) :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    _ = α⁻¹*(1-Real.exp (-α*t)*Real.exp (α*s)) := by rw [← hcancel]; ring
    _ ≤ α⁻¹*1 := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hα.le)
    _ = 1/α := by simp only [one_div,mul_one]

theorem exponential_integral_difference_le {F G : ℝ → ℝ} {s t K δ α : ℝ}
    (hst : s ≤ t) (hF : Continuous F) (hG : Continuous G)
    (hpoint : ∀ u ∈ Icc s t, |F u-G u| ≤ K*(Real.exp (α*u)*δ)) :
    |(∫ u in s..t, F u)-(∫ u in s..t, G u)| ≤
      (K*δ)*(∫ u in s..t, Real.exp (α*u)) := by
  rw [← intervalIntegral.integral_sub (hF.intervalIntegrable s t) (hG.intervalIntegrable s t)]
  have hb : Continuous (fun u => (K*δ)*Real.exp (α*u)) := by fun_prop
  have hh := intervalIntegral.norm_integral_le_of_norm_le hst
    (μ := volume)
    (f := fun u => F u-G u) (g := fun u => (K*δ)*Real.exp (α*u))
    (ae_of_all _ (fun u hu => by
      rw [Real.norm_eq_abs]
      have hh := hpoint u ⟨hu.1.le,hu.2⟩
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hh))
    (hb.intervalIntegrable s t)
  simpa only [Real.norm_eq_abs,intervalIntegral.integral_const_mul] using hh

@[expose] def finiteMap (p : ℕ) (γ τ : ℝ) (f : State) : State :=
  initialState+τ • (picardMap p γ 1 f-initialState)

@[expose] def weightedPicardMap (p : ℕ) (γ τ α : ℝ) (f : State) : State :=
  weightedState α (finiteMap p γ τ (unweightedState α f))

theorem finiteMap_fst (p : ℕ) (γ τ : ℝ) (f : State) (z : Square) :
    (finiteMap p γ τ f z).1=1+τ*(∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
      unitCorrelationSlope p γ 1 f u (min z.1 z.2)) := by
  change 1+τ*((1+1*_)-1)=_
  ring

theorem finiteMap_snd (p : ℕ) (γ τ : ℝ) (f : State) (z : Square) :
    (finiteMap p γ τ f z).2=1+τ*(∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
      unitResponseSlope p γ 1 f u (min z.1 z.2)) := by
  change 1+τ*((1+1*_)-1)=_
  ring

theorem weightedPicardMap_difference_le {p : ℕ} (hp : 3 ≤ p) (γ : ℝ) {τ α : ℝ}
    (hτ : 0 ≤ τ) (hα : 0 < α) (f g : State) :
    ‖weightedPicardMap p γ τ α f-weightedPicardMap p γ τ α g‖ ≤
      (τ*slopeLip p γ/α)*‖f-g‖ := by
  have hK := (slope_constants_nonneg hp γ).2
  have hδ := norm_nonneg (f-g)
  have hcoef : 0 ≤ τ*slopeLip p γ/α := div_nonneg (mul_nonneg hτ hK) hα.le
  apply (ContinuousMap.norm_le _ (mul_nonneg hcoef hδ)).mpr
  intro z
  let a : ℝ := min (z.1 : ℝ) (z.2 : ℝ)
  let b : ℝ := max (z.1 : ℝ) (z.2 : ℝ)
  have ha : a ∈ Icc 0 1 := ⟨le_min z.1.2.1 z.2.2.1,(min_le_left _ _).trans z.1.2.2⟩
  have hb : b ∈ Icc 0 1 := ⟨z.1.2.1.trans (le_max_left _ _),max_le z.1.2.2 z.2.2.2⟩
  have hab : a ≤ b := min_le_max
  have hcF (h : State) : Continuous (fun u => unitCorrelationSlope p γ 1 (unweightedState α h) u a) :=
    (unitCorrelationSlope_continuous p γ 1 (unweightedState α h)).comp (continuous_id.prodMk continuous_const)
  have hrF (h : State) : Continuous (fun u => unitResponseSlope p γ 1 (unweightedState α h) u a) :=
    (unitResponseSlope_continuous p γ 1 (unweightedState α h)).comp (continuous_id.prodMk continuous_const)
  have hci := exponential_integral_difference_le hab (hcF f) (hcF g)
    (fun u hu => (weighted_slopes_difference_le hp γ hα.le f g
      ⟨ha.1.trans hu.1,hu.2.trans hb.2⟩ ⟨ha.1,hu.1⟩).1)
  have hri := exponential_integral_difference_le hab (hrF f) (hrF g)
    (fun u hu => (weighted_slopes_difference_le hp γ hα.le f g
      ⟨ha.1.trans hu.1,hu.2.trans hb.2⟩ ⟨ha.1,hu.1⟩).2)
  have houter {Ic Ig : ℝ} (hI : |Ic-Ig| ≤ (slopeLip p γ*‖f-g‖)*(∫ u in a..b, Real.exp (α*u))) :
      |Real.exp (-α*b)*(1+τ*Ic)-Real.exp (-α*b)*(1+τ*Ig)| ≤
        (τ*slopeLip p γ/α)*‖f-g‖ := by
    have heq : Real.exp (-α*b)*(1+τ*Ic)-Real.exp (-α*b)*(1+τ*Ig)=
        Real.exp (-α*b)*τ*(Ic-Ig) := by ring
    rw [heq,abs_mul,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hτ)]
    have hh := mul_le_mul_of_nonneg_left hI (mul_nonneg (Real.exp_pos (-α*b)).le hτ)
    have hw := mul_le_mul_of_nonneg_left (exp_weighted_integral_le (s := a) (t := b) hα)
      (mul_nonneg (mul_nonneg hτ hK) hδ)
    apply hh.trans
    convert hw using 1 <;> ring
  rw [norm_prod_le_iff]
  constructor
  · change |Real.exp (-α*b)*(finiteMap p γ τ (unweightedState α f) z).1-
      Real.exp (-α*b)*(finiteMap p γ τ (unweightedState α g) z).1| ≤ _
    rw [finiteMap_fst,finiteMap_fst]
    exact houter hci
  · change |Real.exp (-α*b)*(finiteMap p γ τ (unweightedState α f) z).2-
      Real.exp (-α*b)*(finiteMap p γ τ (unweightedState α g) z).2| ≤ _
    rw [finiteMap_snd,finiteMap_snd]
    exact houter hri

@[expose] def weightRate (p : ℕ) (γ τ : ℝ) : ℝ := 1+2*τ*slopeLip p γ

theorem weightRate_pos {p : ℕ} (hp : 3 ≤ p) (γ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 < weightRate p γ τ := by
  have hh := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hτ) (slope_constants_nonneg hp γ).2
  dsimp only [weightRate]
  linarith

theorem weightedPicardMap_contracting {p : ℕ} (hp : 3 ≤ p) (γ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ContractingWith ⟨τ*slopeLip p γ/weightRate p γ τ,
      div_nonneg (mul_nonneg hτ (slope_constants_nonneg hp γ).2) (weightRate_pos hp γ hτ).le⟩
      (weightedPicardMap p γ τ (weightRate p γ τ)) := by
  have hα := weightRate_pos hp γ hτ
  refine ⟨?_,LipschitzWith.of_dist_le_mul ?_⟩
  · change τ*slopeLip p γ/weightRate p γ τ < 1
    rw [div_lt_one hα]
    have hh := mul_nonneg hτ (slope_constants_nonneg hp γ).2
    dsimp only [weightRate]
    nlinarith only [hh]
  · intro f g
    change dist (weightedPicardMap p γ τ (weightRate p γ τ) f)
      (weightedPicardMap p γ τ (weightRate p γ τ) g) ≤
      (τ*slopeLip p γ/weightRate p γ τ)*dist f g
    rw [dist_eq_norm,dist_eq_norm]
    exact weightedPicardMap_difference_le hp γ hτ hα f g

theorem finiteMap_fixed_point {p : ℕ} (hp : 3 ≤ p) (γ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ f : State, finiteMap p γ τ f=f := by
  let α := weightRate p γ τ
  let g := ContractingWith.fixedPoint (weightedPicardMap p γ τ α) (weightedPicardMap_contracting hp γ hτ)
  have hfix : weightedPicardMap p γ τ α g=g :=
    (weightedPicardMap_contracting hp γ hτ).fixedPoint_isFixedPt.eq
  let f := unweightedState α g
  refine ⟨f,?_⟩
  have hh := congrArg (unweightedState α) hfix
  simpa only [weightedPicardMap,unweighted_weighted] using hh

theorem unit_slopes_rebase (p : ℕ) (β γ τ : ℝ) (hγ : γ ^ 2=τ*β ^ 2)
    (f : State) (t s : ℝ) :
    unitCorrelationSlope p γ 1 f t s=unitCorrelationSlope p β τ f t s ∧
      unitResponseSlope p γ 1 f t s=unitResponseSlope p β τ f t s := by
  constructor
  · unfold unitCorrelationSlope
    simp only [trialData,correlationMemory,forcingMemory,hγ,one_mul]
  · unfold unitResponseSlope
    simp only [trialData,responseMemory,hγ,one_mul]

theorem finiteMap_equals_picard (p : ℕ) (β γ τ : ℝ) (hγ : γ ^ 2=τ*β ^ 2) (f : State) :
    finiteMap p γ τ f=picardMap p β τ f := by
  apply ContinuousMap.ext
  intro z
  apply Prod.ext
  · rw [finiteMap_fst]
    have hi : (∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
        unitCorrelationSlope p γ 1 f u (min z.1 z.2))=
      ∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
        unitCorrelationSlope p β τ f u (min z.1 z.2) := by
      apply intervalIntegral.integral_congr
      intro u _
      exact (unit_slopes_rebase p β γ τ hγ f u (min z.1 z.2)).1
    rw [hi]
    rfl
  · rw [finiteMap_snd]
    have hi : (∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
        unitResponseSlope p γ 1 f u (min z.1 z.2))=
      ∫ u in min (z.1 : ℝ) (z.2 : ℝ)..max (z.1 : ℝ) (z.2 : ℝ),
        unitResponseSlope p β τ f u (min z.1 z.2) := by
      apply intervalIntegral.integral_congr
      intro u _
      exact (unit_slopes_rebase p β γ τ hγ f u (min z.1 z.2)).2
    rw [hi]
    rfl

/-- A genuine fixed point of the truncated CK equations on every finite horizon;
no smallness restriction on the horizon is imposed. -/
theorem truncated_picard_fixed_point_any_horizon {p : ℕ} (hp : 3 ≤ p) (β : ℝ)
    {τ : ℝ} (hτ : 0 < τ) : ∃ f : State, picardMap p β τ f=f := by
  let γ : ℝ := Real.sqrt τ*β
  have hγ : γ ^ 2=τ*β ^ 2 := by dsimp only [γ]; rw [mul_pow,Real.sq_sqrt hτ.le]
  obtain ⟨f,hfix⟩ := finiteMap_fixed_point hp γ hτ.le
  rw [finiteMap_equals_picard p β γ τ hγ f] at hfix
  exact ⟨f,hfix⟩

end SphericalAging.CKContinuation
