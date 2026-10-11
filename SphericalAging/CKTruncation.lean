module

public import SphericalAging.CKContinuation

public section

/-!
# Recovering the original equations on inactive truncation prefixes

The globally truncated Banach fixed point has genuine continuous raw fields.
On any prefix where both fields remain in [-2,2], they satisfy the manuscript's
untruncated CK equations. No physical bounds or PSD are inserted as axioms.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace SphericalAging.CKTruncation
open CKSpecification CKWellposedness CKLocalExistence CKContinuation

@[expose] def rawC (f : State) (t s : ℝ) : ℝ := (sample f t s).1
@[expose] def rawR (f : State) (t s : ℝ) : ℝ := (sample f t s).2

@[expose] def rawPhysicalData (p : ℕ) (β τ : ℝ) (f : State) : CKData where
  C := fun t s => rawC f (t/τ) (s/τ)
  R := fun t s => rawR f (t/τ) (s/τ)
  multiplier := fun t => (trialData p β τ f).multiplier (t/τ)

@[expose] def InactiveOnHorizon (p : ℕ) (β τ T : ℝ) (f : State) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
    |(rawPhysicalData p β τ f).C t s| ≤ 2 ∧ |(rawPhysicalData p β τ f).R t s| ≤ 2

theorem rawC_continuous (f : State) : Continuous (Function.uncurry (rawC f)) :=
  (sample_continuous f).fst

theorem rawR_continuous (f : State) : Continuous (Function.uncurry (rawR f)) :=
  (sample_continuous f).snd

theorem raw_physical_fields_continuous (p : ℕ) (β τ : ℝ) (f : State) :
    Continuous (Function.uncurry (rawPhysicalData p β τ f).C) ∧
      Continuous (Function.uncurry (rawPhysicalData p β τ f).R) :=
  ⟨(rawC_continuous f).comp ((continuous_fst.div_const τ).prodMk (continuous_snd.div_const τ)),
    (rawR_continuous f).comp ((continuous_fst.div_const τ).prodMk (continuous_snd.div_const τ))⟩

theorem inactive_fields_eq {p : ℕ} {β τ T : ℝ} {f : State}
    (hi : InactiveOnHorizon p β τ T f) {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    (rawPhysicalData p β τ f).C t s=(physicalData p β τ f).C t s ∧
      (rawPhysicalData p β τ f).R t s=(physicalData p β τ f).R t s := by
  have hh := hi t ht s hs
  constructor
  · exact (clipValue_eq (abs_le.mp hh.1)).symm
  · exact (clipValue_eq (abs_le.mp hh.2)).symm

theorem fixed_raw_integral_equations {p : ℕ} {β τ : ℝ} {f : State}
    (hfix : picardMap p β τ f=f) {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) :
    rawC f t s=1+τ*(∫ u in s..t, unitCorrelationSlope p β τ f u s) ∧
      rawR f t s=1+τ*(∫ u in s..t, unitResponseSlope p β τ f u s) := by
  have hs1 : s ∈ Icc 0 1 := ⟨hs.1,hs.2.trans ht.2⟩
  have hh := congrArg (fun h : State => h (clampTime t,clampTime s)) hfix
  change picardValues p β τ f (clampTime t) (clampTime s)=f (clampTime t,clampTime s) at hh
  rw [clampTime_eq ht,clampTime_eq hs1] at hh
  simp only [rawC,rawR,sample,max_eq_left hs.2,min_eq_right hs.2]
  constructor
  · simpa only [picardValues,max_eq_left hs.2,min_eq_right hs.2] using congrArg Prod.fst hh.symm
  · simpa only [picardValues,max_eq_left hs.2,min_eq_right hs.2] using congrArg Prod.snd hh.symm

theorem fixed_raw_derivatives {p : ℕ} {β τ : ℝ} {f : State}
    (hfix : picardMap p β τ f=f) {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 t) :
    HasDerivWithinAt (fun x => rawC f x s) (τ*unitCorrelationSlope p β τ f t s) (Icc s 1) t ∧
      HasDerivWithinAt (fun x => rawR f x s) (τ*unitResponseSlope p β τ f t s) (Icc s 1) t := by
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
      (fun x hx => (fixed_raw_integral_equations hfix ⟨hs.1.trans hx.1,hx.2⟩ ⟨hs.1,hx.1⟩).1)
      (fixed_raw_integral_equations hfix ht hs).1
  · exact hdR.hasDerivWithinAt.congr
      (fun x hx => (fixed_raw_integral_equations hfix ⟨hs.1.trans hx.1,hx.2⟩ ⟨hs.1,hx.1⟩).2)
      (fixed_raw_integral_equations hfix ht hs).2

theorem data_slopes_congr_on_square {p : ℕ} {β T : ℝ} {d e : CKData}
    (hC : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s=e.C t s)
    (hR : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.R t s=e.R t s)
    (hLambda : ∀ t ∈ Icc 0 T, d.multiplier t=e.multiplier t)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
    correlationSlope p β d t s=correlationSlope p β e t s ∧
      responseSlope p β d t s=responseSlope p β e t s := by
  have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
  have hrmem : (∫ u in s..t, xiDoublePrime p (d.C t u)*d.R t u*d.R u s)=
      ∫ u in s..t, xiDoublePrime p (e.C t u)*e.R t u*e.R u s := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs.2] at hu
    have huT : u ∈ Icc 0 T := ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩
    dsimp only
    rw [hC t ht u huT,hR t ht u huT,hR u huT s hsT]
  have hcmem : (∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u)*d.R t u*d.C u s)=
      ∫ u in (0 : ℝ)..t, xiDoublePrime p (e.C t u)*e.R t u*e.C u s := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    have huT : u ∈ Icc 0 T := ⟨hu.1,hu.2.trans ht.2⟩
    dsimp only
    rw [hC t ht u huT,hR t ht u huT,hC u huT s hsT]
  have hfmem : (∫ u in (0 : ℝ)..s, xiPrime p (d.C t u)*d.R s u)=
      ∫ u in (0 : ℝ)..s, xiPrime p (e.C t u)*e.R s u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs.1] at hu
    have huT : u ∈ Icc 0 T := ⟨hu.1,hu.2.trans hsT.2⟩
    dsimp only
    rw [hC t ht u huT,hR s hsT u huT]
  constructor
  · simp only [correlationSlope,hLambda t ht,hC t ht s hsT,hcmem,hfmem]
  · simp only [responseSlope,hLambda t ht,hR t ht s hsT,hrmem]

theorem continuous_data_memories {d : CKData}
    (hC : Continuous (Function.uncurry d.C)) (hR : Continuous (Function.uncurry d.R)) (n : ℕ) :
    Continuous (Function.uncurry (responseMemory n d)) ∧
      Continuous (Function.uncurry (correlationMemory n d)) ∧
      Continuous (Function.uncurry (forcingMemory n d)) := by
  refine ⟨?_,?_,?_⟩
  · apply continuous_moving_integral
    · exact ((hC.comp (continuous_fst.fst.prodMk continuous_snd)).pow n).mul
        (hR.comp (continuous_fst.fst.prodMk continuous_snd)) |>.mul
        (hR.comp (continuous_snd.prodMk continuous_fst.snd))
    · fun_prop
    · fun_prop
  · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact ((hC.comp (continuous_fst.fst.prodMk continuous_snd)).pow n).mul
        (hR.comp (continuous_fst.fst.prodMk continuous_snd)) |>.mul
        (hC.comp (continuous_snd.prodMk continuous_fst.snd))
    · fun_prop
  · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact ((hC.comp (continuous_fst.fst.prodMk continuous_snd)).pow n).mul
        (hR.comp (continuous_fst.snd.prodMk continuous_snd))
    · fun_prop

theorem continuous_data_slopes (p : ℕ) (β : ℝ) {d : CKData}
    (hC : Continuous (Function.uncurry d.C)) (hR : Continuous (Function.uncurry d.R))
    (hLambda : Continuous d.multiplier) :
    Continuous (Function.uncurry (correlationSlope p β d)) ∧
      Continuous (Function.uncurry (responseSlope p β d)) := by
  have hn := continuous_data_memories hC hR (p-2)
  have hf := (continuous_data_memories hC hR (p-1)).2.2
  constructor
  · apply ((((hLambda.comp continuous_fst).neg.mul hC).add
      (continuous_const.mul hn.2.1)).add (continuous_const.mul hf)).congr
    intro z
    exact (correlationSlope_normalized p β d z.1 z.2).symm
  · apply (((hLambda.comp continuous_fst).neg.mul hR).add
      (continuous_const.mul hn.1)).congr
    intro z
    exact (responseSlope_normalized p β d z.1 z.2).symm

theorem inactive_multiplier_eq {p : ℕ} {β τ T : ℝ} {f : State}
    (hτ : τ ≠ 0) (hi : InactiveOnHorizon p β τ T f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (rawPhysicalData p β τ f).multiplier t=
      1+β ^ 2*(p : ℝ)^2*memoryMass p (rawPhysicalData p β τ f) t := by
  have hmem : memoryMass p (rawPhysicalData p β τ f) t=memoryMass p (physicalData p β τ f) t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp only [memoryMass]
    have heq := inactive_fields_eq hi ht ⟨hu.1,hu.2.trans ht.2⟩
    rw [heq.1,heq.2]
  rw [hmem]
  exact physical_multiplier_eq p β hτ f t

theorem raw_physical_derivatives {p : ℕ} {β τ T : ℝ} {f : State}
    (hτ : 0 < τ) (hTτ : T ≤ τ) (hfix : picardMap p β τ f=f)
    (hi : InactiveOnHorizon p β τ T f) {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
    HasDerivWithinAt (fun x => (rawPhysicalData p β τ f).C x s)
      (correlationSlope p β (rawPhysicalData p β τ f) t s) (Icc s T) t ∧
      HasDerivWithinAt (fun x => (rawPhysicalData p β τ f).R x s)
        (responseSlope p β (rawPhysicalData p β τ f) t s) (Icc s T) t := by
  have ht' : t/τ ∈ Icc 0 1 :=
    ⟨div_nonneg ht.1 hτ.le,(div_le_one₀ hτ).mpr (ht.2.trans hTτ)⟩
  have hs' : s/τ ∈ Icc 0 (t/τ) :=
    ⟨div_nonneg hs.1 hτ.le,(div_le_div_iff_of_pos_right hτ).mpr hs.2⟩
  have hmaps : MapsTo (fun x => x/τ) (Icc s T) (Icc (s/τ) 1) := by
    intro x hx
    exact ⟨(div_le_div_iff_of_pos_right hτ).mpr hx.1,(div_le_one₀ hτ).mpr (hx.2.trans hTτ)⟩
  have hdscalar : HasDerivWithinAt (fun x : ℝ => x/τ) (1/τ) (Icc s T) t :=
    ((hasDerivAt_id t).div_const τ).hasDerivWithinAt
  have hunit := fixed_raw_derivatives hfix ht' hs'
  have hdc := hunit.1.comp t hdscalar hmaps
  have hdr := hunit.2.comp t hdscalar hmaps
  have hcancel (a : ℝ) : (τ*a)*(1/τ)=a := by field_simp [hτ.ne']
  rw [hcancel] at hdc hdr
  have hslope := data_slopes_congr_on_square (p := p) (β := β)
    (fun t ht s hs => (inactive_fields_eq hi ht hs).1)
    (fun t ht s hs => (inactive_fields_eq hi ht hs).2) (fun _ _ => rfl) ht hs
  rw [hslope.1,hslope.2,(physical_slopes_eq p β hτ.ne' f t s).1,
    (physical_slopes_eq p β hτ.ne' f t s).2]
  exact ⟨hdc,hdr⟩

/-- A true original CK solution on every prefix where the construction's
truncation is inactive, with no presumed physical or covariance bounds. -/
theorem rawCK_on_inactive_prefix {p : ℕ} (hp : 3 ≤ p) {β τ T : ℝ} (hβ : 0 < β)
    (hτ : 0 < τ) (hT : 0 < T) (hTτ : T ≤ τ) {f : State}
    (hfix : picardMap p β τ f=f) (hi : InactiveOnHorizon p β τ T f) :
    CKOnHorizon p β T (rawPhysicalData p β τ f) := by
  have hc := (raw_physical_fields_continuous p β τ f).1
  have hr := (raw_physical_fields_continuous p β τ f).2
  have hLambda : Continuous (rawPhysicalData p β τ f).multiplier :=
    (trialMultiplier_continuous p β τ f).comp (continuous_id.div_const τ)
  have hslopes := continuous_data_slopes p β hc hr hLambda
  refine ⟨hp,hβ,hT,hc,hr,hLambda,?_,?_,?_,?_,?_,?_,hslopes.1,hslopes.2⟩
  · intro t s
    exact congrArg Prod.fst (sample_symmetric f (t/τ) (s/τ))
  · intro t ht
    have ht' : t/τ ∈ Icc 0 1 :=
      ⟨div_nonneg ht.1 hτ.le,(div_le_one₀ hτ).mpr (ht.2.trans hTτ)⟩
    have hh := (fixed_raw_integral_equations hfix ht' ⟨ht'.1,le_refl (t/τ)⟩).1
    simpa only [rawPhysicalData,intervalIntegral.integral_same,mul_zero,add_zero] using hh
  · intro t ht
    have ht' : t/τ ∈ Icc 0 1 :=
      ⟨div_nonneg ht.1 hτ.le,(div_le_one₀ hτ).mpr (ht.2.trans hTτ)⟩
    have hh := (fixed_raw_integral_equations hfix ht' ⟨ht'.1,le_refl (t/τ)⟩).2
    simpa only [rawPhysicalData,intervalIntegral.integral_same,mul_zero,add_zero] using hh
  · intro t ht
    exact inactive_multiplier_eq hτ.ne' hi ht
  · intro t ht s hs
    exact (raw_physical_derivatives hτ hTτ hfix hi ht hs).1
  · intro t ht s hs
    exact (raw_physical_derivatives hτ hTτ hfix hi ht hs).2

end SphericalAging.CKTruncation
