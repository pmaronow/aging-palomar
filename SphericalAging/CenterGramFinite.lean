module

public import SphericalAging.WindowCovarianceVariation
public import SphericalAging.CenterAverageDecay
public import SphericalAging.ProductTransfer

public section

/-! Actual finite center-Gram comparison. The only errors are actual
center/average distances and actual covariance derivative bounds. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.CenterGramFinite
open CKSpecification GreenCovariance CKPhysicalConsequences CausalTreeRealization
  CausalCenterAverage WindowAverages PrefixReflection WindowCovarianceVariation EarlierCovariance

/-- A genuine bounded double-average estimate. No average-error conclusion is an input. -/
theorem double_average_error {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    {D c B : ℝ} (hD : 0 < D)
    (hB : ∀ u ∈ Icc 0 D, ∀ v ∈ Icc 0 D, |F u v-c| ≤ B) :
    |(D⁻¹)^2*(∫ u in (0 : ℝ)..D, ∫ v in (0 : ℝ)..D, F u v)-c| ≤ B := by
  have hrow (u : ℝ) : Continuous (F u) := hF.comp (continuous_const.prodMk continuous_id)
  have hout : Continuous (fun u => ∫ v in (0 : ℝ)..D, F u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 D
  have hdiff (u : ℝ) : (∫ v in (0 : ℝ)..D, F u v-c) =
      (∫ v in (0 : ℝ)..D, F u v)-D*c := by
    rw [intervalIntegral.integral_sub ((hrow u).intervalIntegrable 0 D) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
  have hid : (D⁻¹)^2*(∫ u in (0 : ℝ)..D, ∫ v in (0 : ℝ)..D, F u v)-c =
      (D⁻¹)^2*(∫ u in (0 : ℝ)..D, ∫ v in (0 : ℝ)..D, F u v-c) := by
    simp_rw [hdiff]
    rw [intervalIntegral.integral_sub (hout.intervalIntegrable 0 D) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
    field_simp [hD.ne']
  have hn1 (u : ℝ) (hu : u ∈ Icc 0 D) :
      |∫ v in (0 : ℝ)..D, F u v-c| ≤ B*D := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun v => F u v-c) (a := 0) (b := D)
      (fun v hv => by
        rw [uIoc_of_le hD.le] at hv
        simpa only [Real.norm_eq_abs] using hB u hu v ⟨hv.1.le,hv.2⟩)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos hD] using hh
  have hn2 := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u => ∫ v in (0 : ℝ)..D, F u v-c) (a := 0) (b := D)
    (fun u hu => by
      rw [uIoc_of_le hD.le] at hu
      simpa only [Real.norm_eq_abs] using hn1 u ⟨hu.1.le,hu.2⟩)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_pos hD] at hn2
  rw [hid,abs_mul,abs_of_nonneg (sq_nonneg _)]
  calc
    (D⁻¹)^2*|∫ u in (0 : ℝ)..D, ∫ v in (0 : ℝ)..D, F u v-c| ≤
      (D⁻¹)^2*((B*D)*D) := mul_le_mul_of_nonneg_left hn2 (sq_nonneg _)
    _ = B := by field_simp [hD.ne']

/-- The exact actual cross-average Gram formula on two nonnegative windows. -/
theorem localAverage_cross_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T S D : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    inner ℝ (localAverage h T D) (localAverage h S D) =
      (D⁻¹)^2*(∫ u in (0 : ℝ)..D, ∫ v in (0 : ℝ)..D, d.C (T+u) (S+v)) := by
  unfold localAverage
  rw [average_inner _ _ (ckTreeState_clamped_continuous h (physical_bounds_of_equations h))
    (ckTreeState_clamped_continuous h (physical_bounds_of_equations h))]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hD] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hD] at hv
  dsimp only
  rw [max_eq_right (add_nonneg hT hu.1),max_eq_right (add_nonneg hS hv.1),
    ckTreeState_gram h (physical_bounds_of_equations h) (add_nonneg hT hu.1) (add_nonneg hS hv.1)]

/-- The average overlap is close to the actual endpoint correlation on a remote pair
of windows, from actual derivative bounds and the proved finite variation formula. -/
theorem localAverage_overlap_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {D s t M : ℝ}
    (hD : 0 < D) (hs : D ≤ s) (ht : s+2*D ≤ t) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (t-D) t, ∀ y ∈ Icc (s-D) s,
      |correlationSlope p β d x y| ≤ M) :
    |inner ℝ (localAverage h (t-D) D) (localAverage h (s-D) D)-d.C t s| ≤
      D*M+(∫ y in s-D..s, |earlierSlope p β d t y|) := by
  have hsD : 0 ≤ s-D := sub_nonneg.mpr hs
  have htD : 0 ≤ t-D := by linarith
  let F : ℝ → ℝ → ℝ := fun u v => clampedCorrelation d (t-D+u) (s-D+v)
  have hF : Continuous (Function.uncurry F) :=
    (clampedCorrelation_continuous h).comp
      ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd))
  have hB := double_average_error (c := d.C t s)
    (B := D*M+(∫ y in s-D..s, |earlierSlope p β d t y|)) hF hD
    (fun u hu v hv => ?_)
  · rw [localAverage_cross_inner h htD hsD hD.le]
    have he : (∫ u in (0 : ℝ)..D, ∫ v in (0 : ℝ)..D, d.C (t-D+u) (s-D+v)) =
        ∫ u in (0 : ℝ)..D, ∫ v in (0 : ℝ)..D, F u v := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hD.le] at hu
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hD.le] at hv
      dsimp only [F]
      rw [clampedCorrelation_eq (add_nonneg htD hu.1) (add_nonneg hsD hv.1)]
    rw [he]
    exact hB
  · dsimp only [F]
    rw [clampedCorrelation_eq (add_nonneg htD hu.1) (add_nonneg hsD hv.1)]
    exact remote_rectangle_variation h hD hs ht hM0
      ⟨by linarith [hu.1],by linarith [hu.2]⟩ ⟨by linarith [hv.1],by linarith [hv.2]⟩ hM

/-- Exact source center/average Gram perturbation on the actual causal tree. -/
theorem center_average_overlap_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {D s t : ℝ} (hD : 0 < D) (hs : D ≤ s) (ht : D ≤ t) :
    |inner ℝ (localCenter h (t-D) D) (localCenter h (s-D) D)-
      inner ℝ (localAverage h (t-D) D) (localAverage h (s-D) D)| ≤
      ‖localCenter h (t-D) D-localAverage h (t-D) D‖+
      ‖localCenter h (s-D) D-localAverage h (s-D) D‖ := by
  apply ProductTransfer.inner_perturbation
    (e₁ := ‖localCenter h (t-D) D-localAverage h (t-D) D‖)
    (e₂ := ‖localCenter h (s-D) D-localAverage h (s-D) D‖)
  · exact prefixVector_norm_le_one h (physical_bounds_of_equations h) (s-D)
      (by have hs0 := hD.le.trans hs; simpa only [sub_add_cancel] using hs0)
  · exact localAverage_norm_le_one h hD
  · exact le_rfl
  · exact le_rfl

/-- Full finite unnormalized center-Gram comparison from genuine tree centers,
Bochner averages and actual covariance derivatives. -/
theorem center_endpoint_overlap_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {D s t M : ℝ}
    (hD : 0 < D) (hs : D ≤ s) (ht : s+2*D ≤ t) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (t-D) t, ∀ y ∈ Icc (s-D) s,
      |correlationSlope p β d x y| ≤ M) :
    |inner ℝ (localCenter h (t-D) D) (localCenter h (s-D) D)-d.C t s| ≤
      ‖localCenter h (t-D) D-localAverage h (t-D) D‖+
      ‖localCenter h (s-D) D-localAverage h (s-D) D‖+
      D*M+(∫ y in s-D..s, |earlierSlope p β d t y|) := by
  have h1 := center_average_overlap_bound (D := D) (s := s) (t := t) h hD hs (by linarith)
  have h2 := localAverage_overlap_bound h hD hs ht hM0 hM
  exact (abs_sub_le _ (inner ℝ (localAverage h (t-D) D) (localAverage h (s-D) D)) _).trans
    (by simpa only [add_assoc] using add_le_add h1 h2)

end SphericalAging.CenterGramFinite
