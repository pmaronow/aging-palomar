module

public import SphericalAging.EarlierSmoothing

public section

/-! Genuine finite covariance variation in both coordinates, including
the causal right endpoint. These estimates supply the center-Gram bridge. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.WindowCovarianceVariation
open CKSpecification GreenCovariance EarlierCovariance

theorem earlier_integral_eq_covariance_difference {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b < t) :
    (∫ u in a..b, earlierSlope p β d t u) = d.C t b-d.C t a := by
  have hcont := h.correlation_continuous.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun u (hu : u ∈ Icc a b) => ⟨ha.trans (hab.trans hbt.le),ha.trans hu.1⟩)
  have hc : Continuous (fun u => clampedEarlierSlope p β d t u) :=
    (clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  have hi : IntervalIntegrable (earlierSlope p β d t) volume a b := by
    apply (hc.intervalIntegrable a b).congr
    intro u hu
    rw [uIoc_of_le hab] at hu
    exact clampedEarlierSlope_eq (ha.trans hu.1.le) (hu.2.trans hbt.le)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun u hu => correlation_earlier_hasDerivAt h (ha.trans_lt hu.1) (hu.2.trans hbt)) hi

theorem earlier_window_variation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b < t) :
    |d.C t b-d.C t a| ≤ ∫ u in a..b, |earlierSlope p β d t u| := by
  rw [← earlier_integral_eq_covariance_difference h ha hab hbt]
  exact intervalIntegral.abs_integral_le_integral_abs hab

theorem later_integral_eq_covariance_difference {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b s : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a ≤ b) :
    (∫ u in a..b, correlationSlope p β d u s) = d.C b s-d.C a s := by
  have hcont := h.correlation_continuous.comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun u (hu : u ∈ Icc a b) => ⟨hs.trans (hsa.trans hu.1),hs⟩)
  have hslope : ContinuousOn (fun u => correlationSlope p β d u s) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact h.correlation_slope_continuous.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun u hu => ⟨hs,hsa.trans hu.1⟩)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun u hu => (h.correlation_derivative u s hs (hsa.trans hu.1.le)).hasDerivAt
      (Ici_mem_nhds (hsa.trans_lt hu.1))) hslope.intervalIntegrable

theorem later_window_variation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b s M : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a ≤ b)
    (hM : ∀ u ∈ Icc a b, |correlationSlope p β d u s| ≤ M) :
    |d.C b s-d.C a s| ≤ (b-a)*M := by
  rw [← later_integral_eq_covariance_difference h hs hsa hab]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u => correlationSlope p β d u s) (a := a) (b := b)
    (fun u hu => by
      rw [uIoc_of_le hab] at hu
      simpa only [Real.norm_eq_abs] using hM u ⟨hu.1.le,hu.2⟩)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hi

/-- The actual remote covariance is nearly constant on a pair of preceding
windows. The bound separates genuine later slopes and the earlier integral. -/
theorem remote_rectangle_variation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {D s t u w M : ℝ}
    (hD : 0 < D) (hs : D ≤ s) (ht : s+2*D ≤ t) (hM0 : 0 ≤ M)
    (hu : u ∈ Icc (t-D) t) (hw : w ∈ Icc (s-D) s)
    (hM : ∀ x ∈ Icc (t-D) t, ∀ y ∈ Icc (s-D) s,
      |correlationSlope p β d x y| ≤ M) :
    |d.C u w-d.C t s| ≤ D*M+(∫ y in s-D..s, |earlierSlope p β d t y|) := by
  have hws : 0 ≤ w := (sub_nonneg.mpr hs).trans hw.1
  have hwu : w ≤ u := by linarith [hw.2,hu.1]
  have h1 := later_window_variation h hws hwu hu.2
    (fun x hx => hM x ⟨hu.1.trans hx.1,hx.2⟩ w hw)
  have h1' : |d.C u w-d.C t w| ≤ D*M := by
    rw [abs_sub_comm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (by linarith [hu.1]) hM0)
  have h2 := earlier_window_variation h hws hw.2 (by linarith : s < t)
  have hc : Continuous (fun y => |clampedEarlierSlope p β d t y|) :=
    ((clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)).abs
  have hi : (∫ y in w..s, |earlierSlope p β d t y|) ≤
      ∫ y in s-D..s, |earlierSlope p β d t y| := by
    have hid {a : ℝ} (ha : 0 ≤ a) (has : a ≤ s) :
        (∫ y in a..s, |earlierSlope p β d t y|) = ∫ y in a..s, |clampedEarlierSlope p β d t y| := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le has] at hy
      dsimp only
      rw [clampedEarlierSlope_eq (ha.trans hy.1) (by linarith [hy.2] : y ≤ t)]
    rw [hid hws hw.2,hid (sub_nonneg.mpr hs) (by linarith)]
    exact intervalIntegral.integral_mono_interval hw.1 hw.2 le_rfl
      (ae_of_all _ (fun y => abs_nonneg _)) (hc.intervalIntegrable (s-D) s)
  have h2' : |d.C t w-d.C t s| ≤ ∫ y in s-D..s, |earlierSlope p β d t y| := by
    rw [abs_sub_comm]
    exact h2.trans hi
  exact (abs_sub_le (d.C u w) (d.C t w) (d.C t s)).trans (add_le_add h1' h2')

end SphericalAging.WindowCovarianceVariation
