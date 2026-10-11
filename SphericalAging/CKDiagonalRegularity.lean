module

public import SphericalAging.CKPhysicalConsequences
public import SphericalAging.UniformMultiplier
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

public section

/-!
# Deterministic diagonal increment and uniform covariance continuity

These assertions use the actual CK equations, their proved physical properties,
the sharp uniform multiplier bound and the actual Moore feature construction.
The separate finite-N energy Lipschitz estimate in Proposition 4.4 is not asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped InnerProductSpace NNReal

namespace SphericalAging.CKDiagonalRegularity
open CKSpecification CKPhysicalConsequences UniformMultiplier ScalarHilbertKernel

theorem correlation_slope_lower_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    -multiplierCeiling p β ≤ correlationSlope p β d t s := by
  have hb := physical_bounds_of_equations h
  have ht := hs.trans hst
  have hlam := multiplier_uniform_bound h hb (correlation_psd_of_equations h) ht
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by have hp := h.spin_ge_three; omega)
  have hi : 0 ≤ ∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u)*d.R t u*d.C u s := by
    apply intervalIntegral.integral_nonneg ht
    intro u hu
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.mpr hp1))
        (pow_nonneg (hb.1 t u ht hu.1).1 _)) (hb.2 t u hu.1 hu.2))
      (hb.1 u s hu.1 hs).1
  have hf : 0 ≤ ∫ u in (0 : ℝ)..s, xiPrime p (d.C t u)*d.R s u := by
    apply intervalIntegral.integral_nonneg hs
    intro u hu
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (pow_nonneg (hb.1 t u ht hu.1).1 _))
      (hb.2 s u hu.1 hu.2)
  have hdamp : d.multiplier t*d.C t s ≤ multiplierCeiling p β :=
    (mul_le_mul_of_nonneg_left (hb.1 t s ht hs).2 (by linarith [hlam.1])).trans
      (by simpa only [mul_one] using hlam.2)
  unfold correlationSlope
  nlinarith [mul_nonneg (sq_nonneg β) hi,mul_nonneg (sq_nonneg β) hf]

/-- The exact diagonal-increment assertion in Proposition 4.4. -/
theorem diagonal_increment {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ 1-d.C t s ∧ 1-d.C t s ≤ multiplierCeiling p β*(t-s) := by
  let L := multiplierCeiling p β
  let g : ℝ → ℝ := fun x => d.C x s+L*x
  have hcont : ContinuousOn g (Icc s t) := by
    have hc : Continuous (fun x : ℝ => GreenCovariance.clampedCorrelation d x s) :=
      (GreenCovariance.clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
    have hlin : Continuous (fun x : ℝ => L*x) := continuous_const.mul continuous_id
    apply (hc.add hlin).continuousOn.congr
    intro x hx
    change d.C x s+L*x=GreenCovariance.clampedCorrelation d x s+L*x
    rw [GreenCovariance.clampedCorrelation_eq (hs.trans hx.1) hs]
  have hd {x : ℝ} (hx : x ∈ Ioo s t) :
      HasDerivAt g (correlationSlope p β d x s+L) x := by
    convert ((h.correlation_derivative x s hs hx.1.le).hasDerivAt (Ici_mem_nhds hx.1)).add
      ((hasDerivAt_id x).const_mul L) using 1
    · funext y
      rfl
    · simp only [mul_one]
  have hm : MonotoneOn g (Icc s t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s t) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd hx).deriv]
      have hh := correlation_slope_lower_bound h hs hx.1.le
      dsimp only [L]
      linarith
  have hh := hm (show s ∈ Icc s t from ⟨le_refl s,hst⟩)
    (show t ∈ Icc s t from ⟨hst,le_refl t⟩) hst
  dsimp only [g] at hh
  rw [h.correlation_diagonal s hs] at hh
  exact ⟨sub_nonneg.mpr ((physical_bounds_of_equations h).1 t s (hs.trans hst) hs).2,by
    dsimp only [L] at hh ⊢
    linarith⟩

theorem covariance_feature_increment {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ≥0) :
    ‖feature (ckKernel h (correlation_psd_of_equations h)) t-
      feature (ckKernel h (correlation_psd_of_equations h)) s‖ ^ 2 ≤
      2*multiplierCeiling p β*|(t : ℝ)-(s : ℝ)| := by
  rw [feature_norm_sub_sq]
  change d.C t t-2*d.C t s+d.C s s ≤ _
  rw [h.correlation_diagonal t t.coe_nonneg,h.correlation_diagonal s s.coe_nonneg]
  by_cases hst : (s : ℝ) ≤ t
  · have hh := (diagonal_increment h s.coe_nonneg hst).2
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    nlinarith
  · have hts := le_of_not_ge hst
    have hh := (diagonal_increment h t.coe_nonneg hts).2
    rw [h.correlation_symmetric t s t.coe_nonneg s.coe_nonneg,abs_of_nonpos (sub_nonpos.mpr hts)]
    nlinarith

/-- A uniform coordinate modulus sufficient for equicontinuity of all late-time
windows. It follows from the stronger diagonal estimate and Gram positivity. -/
theorem correlation_coordinate_modulus {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {u v a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) :
    |d.C (u+a) v-d.C u v| ≤ Real.sqrt (2*multiplierCeiling p β*a) := by
  let K := ckKernel h (correlation_psd_of_equations h)
  let tu : ℝ≥0 := ⟨u,hu⟩
  let th : ℝ≥0 := ⟨u+a,add_nonneg hu ha⟩
  let tv : ℝ≥0 := ⟨v,hv⟩
  have hi : inner ℝ (feature K th-feature K tu) (feature K tv)=d.C (u+a) v-d.C u v := by
    rw [inner_sub_left,feature_inner,feature_inner]
    rfl
  have hcs := abs_real_inner_le_norm (feature K th-feature K tu) (feature K tv)
  rw [hi,ckFeature_norm h (correlation_psd_of_equations h) tv,mul_one] at hcs
  have hs := covariance_feature_increment h th tu
  have habs : |(th : ℝ)-(tu : ℝ)|=a := by change |(u+a)-u|=a; rw [add_sub_cancel_left,abs_of_nonneg ha]
  rw [habs] at hs
  have hn : ‖feature K th-feature K tu‖ ≤ Real.sqrt (2*multiplierCeiling p β*a) := by
    exact (Real.le_sqrt (norm_nonneg _) (by
      have hh := (multiplier_uniform_bound h (physical_bounds_of_equations h)
        (correlation_psd_of_equations h) (t := 0) le_rfl).2
      rw [multiplier_zero h] at hh
      positivity)).mpr hs
  exact hcs.trans hn

theorem correlation_coordinate_modulus_right {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {u v a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) :
    |d.C u (v+a)-d.C u v| ≤ Real.sqrt (2*multiplierCeiling p β*a) := by
  rw [h.correlation_symmetric u (v+a) hu (add_nonneg hv ha),h.correlation_symmetric u v hu hv]
  exact correlation_coordinate_modulus h hv hu ha

end SphericalAging.CKDiagonalRegularity
