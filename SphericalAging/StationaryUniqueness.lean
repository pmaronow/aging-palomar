module

public import SphericalAging.VolterraUniqueness
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

public section

/-!
# Uniqueness of the integrated stationary system

The solution class is the locally bounded measurable class specified before
Lemma 6.2. Functions are represented on the real line; equations and uniqueness
only concern the nonnegative ray, so their values at negative times are irrelevant.
-/

open MeasureTheory Set
open scoped Topology NNReal

namespace SphericalAging.StationaryUniqueness

noncomputable section

/-- One-sided memory; for nonnegative time this is the usual interval convolution. -/
@[expose] def memory (n : ℕ) (c r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Ioc 0 t, c (t - u) ^ n * r (t - u) * r u

theorem memory_eq_interval (n : ℕ) (c r : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    memory n c r t = ∫ u in 0..t, c (t - u) ^ n * r (t - u) * r u := by
  exact (intervalIntegral.integral_of_le ht).symm

theorem memory_measurable (n : ℕ) (c r : ℝ → ℝ)
    (hc : Measurable c) (hr : Measurable r) : Measurable (memory n c r) := by
  let A : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ z.2 ≤ z.1}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hF : Measurable (fun z : ℝ × ℝ =>
      c (z.1 - z.2) ^ n * r (z.1 - z.2) * r z.2) :=
    ((hc.comp (measurable_fst.sub measurable_snd)).pow_const n).mul
      (hr.comp (measurable_fst.sub measurable_snd)) |>.mul (hr.comp measurable_snd)
  have hG := (hF.indicator hA).stronglyMeasurable.integral_prod_right'
    (ν := volume)
  convert hG.measurable using 1
  ext t
  unfold memory
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by simp [A, Set.indicator])

/-- A solution is specified by its two integrated equations, with no differentiability assumed. -/
structure IntegratedSolution (n : ℕ) (ell B : ℝ) (c r : ℝ → ℝ) : Prop where
  measurable_c : Measurable c
  measurable_r : Measurable r
  locally_bounded : ∀ T : ℝ, 0 ≤ T → ∃ M : ℝ, 1 ≤ M ∧
    ∀ t ∈ Icc 0 T, |c t| ≤ M ∧ |r t| ≤ M
  correlation : ∀ t : ℝ, 0 ≤ t → c t = 1 - ∫ u in 0..t, r u
  response : ∀ t : ℝ, 0 ≤ t → r t = 1 +
    ∫ v in 0..t, -ell * r v + B * memory n c r v

theorem bounded_measurable_integrableOn {f : ℝ → ℝ} {T M : ℝ}
    (hf : Measurable f) (hbound : ∀ t ∈ Icc 0 T, |f t| ≤ M) :
    IntegrableOn f (Icc 0 T) volume := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simpa only [Real.norm_eq_abs] using hbound t ht

theorem memory_bound (n : ℕ) (c r : ℝ → ℝ) (T M t : ℝ)
    (hM : 0 ≤ M) (hc : Measurable c) (hr : Measurable r)
    (hbound : ∀ v ∈ Icc 0 T, |c v| ≤ M ∧ |r v| ≤ M)
    (ht : t ∈ Icc 0 T) : |memory n c r t| ≤ T * M ^ (n + 2) := by
  have hb (u : ℝ) (hu : u ∈ Icc 0 t) :
      |c (t - u) ^ n * r (t - u) * r u| ≤ M ^ (n + 2) := by
    have hau : t - u ∈ Icc 0 T := ⟨sub_nonneg.mpr hu.2, by linarith [ht.2, hu.1]⟩
    have hub : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
    rw [abs_mul, abs_mul, abs_pow, show M ^ (n + 2) = M ^ n * M * M by ring]
    gcongr
    · exact (hbound _ hau).1
    · exact (hbound _ hau).2
    · exact (hbound _ hub).2
  have hm : Measurable (fun u : ℝ => c (t - u) ^ n * r (t - u) * r u) :=
    ((hc.comp (measurable_const.sub measurable_id)).pow_const n).mul
      (hr.comp (measurable_const.sub measurable_id)) |>.mul hr
  have hi : IntervalIntegrable (fun u : ℝ => c (t - u) ^ n * r (t - u) * r u)
      volume 0 t := (show IntegrableOn (fun u : ℝ => c (t - u) ^ n * r (t - u) * r u)
        (uIcc 0 t) volume by simpa only [uIcc_of_le ht.1] using
          bounded_measurable_integrableOn hm hb).intervalIntegrable
  rw [memory_eq_interval n c r t ht.1]
  calc
    |∫ u in 0..t, c (t - u) ^ n * r (t - u) * r u| ≤
        ∫ u in 0..t, |c (t - u) ^ n * r (t - u) * r u| :=
      intervalIntegral.abs_integral_le_integral_abs ht.1
    _ ≤ ∫ _u in 0..t, M ^ (n + 2) :=
      intervalIntegral.integral_mono_on ht.1 hi.abs intervalIntegrable_const hb
    _ = t * M ^ (n + 2) := by simp
    _ ≤ T * M ^ (n + 2) := mul_le_mul_of_nonneg_right ht.2 (pow_nonneg hM _)

theorem IntegratedSolution.continuousOn (n : ℕ) (ell B : ℝ) (c r : ℝ → ℝ)
    (h : IntegratedSolution n ell B c r) (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn c (Icc 0 T) ∧ ContinuousOn r (Icc 0 T) := by
  obtain ⟨M, hM, hbound⟩ := h.locally_bounded T hT
  have hri := bounded_measurable_integrableOn h.measurable_r
    (fun t ht => (hbound t ht).2)
  have hccont : ContinuousOn (fun t => 1 - ∫ u in 0..t, r u) (Icc 0 T) := by
    rw [← uIcc_of_le hT]
    exact continuousOn_const.sub (intervalIntegral.continuousOn_primitive_interval
      (by simpa only [uIcc_of_le hT] using hri))
  have hfm : Measurable (fun t => -ell * r t + B * memory n c r t) :=
    (measurable_const.mul h.measurable_r).add
      (measurable_const.mul (memory_measurable n c r h.measurable_c h.measurable_r))
  have hfb (t : ℝ) (ht : t ∈ Icc 0 T) :
      |-ell * r t + B * memory n c r t| ≤ |ell| * M + |B| * (T * M ^ (n + 2)) := by
    calc
      _ ≤ |-ell * r t| + |B * memory n c r t| := abs_add_le _ _
      _ = |ell| * |r t| + |B| * |memory n c r t| := by simp [abs_mul]
      _ ≤ _ := by
        gcongr
        · exact (hbound t ht).2
        · exact memory_bound n c r T M t
            (by linarith) h.measurable_c h.measurable_r hbound ht
  have hfi := bounded_measurable_integrableOn hfm hfb
  have hrcont : ContinuousOn (fun t => 1 + ∫ v in 0..t,
      -ell * r v + B * memory n c r v) (Icc 0 T) := by
    rw [← uIcc_of_le hT]
    exact continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval
      (by simpa only [uIcc_of_le hT] using hfi))
  constructor
  · exact hccont.congr (fun t ht => h.correlation t ht.1)
  · exact hrcont.congr (fun t ht => h.response t ht.1)

theorem power_product_lipschitz (n : ℕ) (M a A b B d D : ℝ)
    (hM : 1 ≤ M) (ha : |a| ≤ M) (hA : |A| ≤ M)
    (hb : |b| ≤ M) (hB : |B| ≤ M) (hd : |d| ≤ M) (_hD : |D| ≤ M) :
    |a ^ n * b * d - A ^ n * B * D| ≤
      ((n : ℝ) + 1) * M ^ (n + 2) * (|a - A| + |b - B| + |d - D|) := by
  have hM0 : 0 ≤ M := by linarith
  have hpow : |a ^ n - A ^ n| ≤ (n : ℝ) * M ^ n * |a - A| := by
    calc
      |a ^ n - A ^ n| ≤ |a - A| * (n : ℝ) * max |a| |A| ^ (n - 1) :=
        abs_pow_sub_pow_le a A n
      _ ≤ |a - A| * (n : ℝ) * M ^ n := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
        exact (pow_le_pow_left₀ (by positivity) (max_le ha hA) _).trans
          (pow_le_pow_right₀ hM (Nat.sub_le n 1))
      _ = (n : ℝ) * M ^ n * |a - A| := by ring
  have hfirst : |(a ^ n - A ^ n) * b * d| ≤
      (n : ℝ) * M ^ (n + 2) * |a - A| := by
    rw [abs_mul, abs_mul]
    calc
      |a ^ n - A ^ n| * |b| * |d| ≤
          ((n : ℝ) * M ^ n * |a - A|) * M * M := by gcongr
      _ = (n : ℝ) * M ^ (n + 2) * |a - A| := by ring
  have hsecond : |A ^ n * (b - B) * d| ≤ M ^ (n + 2) * |b - B| := by
    rw [abs_mul, abs_mul, abs_pow]
    calc
      |A| ^ n * |b - B| * |d| ≤ M ^ n * |b - B| * M := by gcongr
      _ = M ^ (n + 1) * |b - B| := by ring
      _ ≤ M ^ (n + 2) * |b - B| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM (by omega)) (abs_nonneg _)
  have hthird : |A ^ n * B * (d - D)| ≤ M ^ (n + 2) * |d - D| := by
    rw [abs_mul, abs_mul, abs_pow]
    calc
      |A| ^ n * |B| * |d - D| ≤ M ^ n * M * |d - D| := by gcongr
      _ = M ^ (n + 1) * |d - D| := by ring
      _ ≤ M ^ (n + 2) * |d - D| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM (by omega)) (abs_nonneg _)
  calc
    _ = |(a ^ n - A ^ n) * b * d + A ^ n * (b - B) * d + A ^ n * B * (d - D)| := by
      congr 1
      ring
    _ ≤ |(a ^ n - A ^ n) * b * d| + |A ^ n * (b - B) * d| + |A ^ n * B * (d - D)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (n : ℝ) * M ^ (n + 2) * |a - A| +
        M ^ (n + 2) * |b - B| + M ^ (n + 2) * |d - D| :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ ≤ _ := by
      have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hpower : 0 ≤ M ^ (n + 2) := pow_nonneg hM0 _
      nlinarith [mul_nonneg hpower (abs_nonneg (a - A)),
        mul_nonneg (mul_nonneg hnn hpower) (abs_nonneg (b - B)),
        mul_nonneg (mul_nonneg hnn hpower) (abs_nonneg (d - D))]

/-- Integral Gronwall for a continuous nonnegative function on its actual domain. -/
theorem integral_gronwall_zero (f : ℝ → ℝ) (T K : ℝ) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hn : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hle : ∀ t ∈ Icc 0 T, f t ≤ K * ∫ u in 0..t, f u) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  let clamp : ℝ → ℝ := fun t => max 0 (min T t)
  let g : ℝ → ℝ := fun t => f (clamp t)
  have hgcont : Continuous g := hf.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id))
    (fun t => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩)
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) : g t = f t := by
    dsimp [g, clamp]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  let F : ℝ → ℝ := fun t => ∫ u in 0..t, g u
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) : F t = ∫ u in 0..t, f u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact hg u ⟨hu.1, hu.2.trans ht.2⟩
  have hd (t : ℝ) : HasDerivAt F (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable 0 t)
      hgcont.aestronglyMeasurable.stronglyMeasurableAtFilter hgcont.continuousAt
  have hbound := le_gronwallBound_of_liminf_deriv_right_le
    (δ := 0) (K := K) (ε := 0)
    (show ContinuousOn F (Icc 0 T) from
      (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn)
    (fun t ht r hr => (hd t).hasDerivWithinAt.liminf_right_slope_le hr)
    (show F 0 ≤ 0 by simp [F])
    (fun t ht => by
      rw [hg t ⟨ht.1, ht.2.le⟩, hi t ⟨ht.1, ht.2.le⟩]
      simpa using hle t ⟨ht.1, ht.2.le⟩)
  intro t ht
  have hFt : F t ≤ 0 := by simpa only [gronwallBound_ε0_δ0] using hbound t ht
  have hFpos : 0 ≤ F t := by
    rw [hi t ht]
    exact intervalIntegral.integral_nonneg ht.1
      (fun u hu => hn u ⟨hu.1, hu.2.trans ht.2⟩)
  have hFzero : F t = 0 := le_antisymm hFt hFpos
  have hft := hle t ht
  rw [← hi t ht, hFzero, mul_zero] at hft
  exact le_antisymm hft (hn t ht)

@[expose] def difference (c₁ r₁ c₂ r₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  |c₁ t - c₂ t| + |r₁ t - r₂ t|

theorem difference_nonneg (c₁ r₁ c₂ r₂ : ℝ → ℝ) (t : ℝ) :
    0 ≤ difference c₁ r₁ c₂ r₂ t := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem memory_row_continuousOn (n : ℕ) (c r : ℝ → ℝ) (T t : ℝ)
    (hc : ContinuousOn c (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (ht : t ∈ Icc 0 T) :
    ContinuousOn (fun u => c (t - u) ^ n * r (t - u) * r u) (Icc 0 t) := by
  have hmaps : MapsTo (fun u : ℝ => t - u) (Icc 0 t) (Icc 0 T) :=
    fun u hu => ⟨sub_nonneg.mpr hu.2, by linarith [ht.2, hu.1]⟩
  exact ((hc.comp (continuous_const.sub continuous_id).continuousOn hmaps).pow n).mul
    (hr.comp (continuous_const.sub continuous_id).continuousOn hmaps) |>.mul
      (hr.mono (Icc_subset_Icc le_rfl ht.2))

theorem memory_difference_bound (n : ℕ) (c₁ r₁ c₂ r₂ : ℝ → ℝ) (T M t : ℝ)
    (hM : 1 ≤ M)
    (hc₁ : ContinuousOn c₁ (Icc 0 T)) (hr₁ : ContinuousOn r₁ (Icc 0 T))
    (hc₂ : ContinuousOn c₂ (Icc 0 T)) (hr₂ : ContinuousOn r₂ (Icc 0 T))
    (hb : ∀ u ∈ Icc 0 T,
      |c₁ u| ≤ M ∧ |r₁ u| ≤ M ∧ |c₂ u| ≤ M ∧ |r₂ u| ≤ M)
    (ht : t ∈ Icc 0 T) :
    |memory n c₁ r₁ t - memory n c₂ r₂ t| ≤
      2 * (((n : ℝ) + 1) * M ^ (n + 2)) * ∫ u in 0..t, difference c₁ r₁ c₂ r₂ u := by
  let A : ℝ := ((n : ℝ) + 1) * M ^ (n + 2)
  let d : ℝ → ℝ := difference c₁ r₁ c₂ r₂
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : ContinuousOn d (Icc 0 T) := (hc₁.sub hc₂).abs.add (hr₁.sub hr₂).abs
  have hmaps : MapsTo (fun u : ℝ => t - u) (Icc 0 t) (Icc 0 T) :=
    fun u hu => ⟨sub_nonneg.mpr hu.2, by linarith [ht.2, hu.1]⟩
  have hdr : ContinuousOn (fun u => d (t - u)) (Icc 0 t) :=
    hd.comp (continuous_const.sub continuous_id).continuousOn hmaps
  have hdu : ContinuousOn d (Icc 0 t) := hd.mono (Icc_subset_Icc le_rfl ht.2)
  have hf₁ := memory_row_continuousOn n c₁ r₁ T t hc₁ hr₁ ht
  have hf₂ := memory_row_continuousOn n c₂ r₂ T t hc₂ hr₂ ht
  have hfi₁ := (show ContinuousOn (fun u => c₁ (t-u)^n*r₁ (t-u)*r₁ u)
    (uIcc 0 t) by simpa only [uIcc_of_le ht.1] using hf₁).intervalIntegrable (μ := volume)
  have hfi₂ := (show ContinuousOn (fun u => c₂ (t-u)^n*r₂ (t-u)*r₂ u)
    (uIcc 0 t) by simpa only [uIcc_of_le ht.1] using hf₂).intervalIntegrable (μ := volume)
  have hdri := (show ContinuousOn (fun u => d (t-u)) (uIcc 0 t) by
    simpa only [uIcc_of_le ht.1] using hdr).intervalIntegrable (μ := volume)
  have hdui := (show ContinuousOn d (uIcc 0 t) by
    simpa only [uIcc_of_le ht.1] using hdu).intervalIntegrable (μ := volume)
  have hpoint (u : ℝ) (hu : u ∈ Icc 0 t) :
      |c₁ (t-u)^n*r₁ (t-u)*r₁ u - c₂ (t-u)^n*r₂ (t-u)*r₂ u| ≤ A * (d (t-u) + d u) := by
    have hau := hmaps hu
    have hub : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
    have h := power_product_lipschitz n M (c₁ (t-u)) (c₂ (t-u))
      (r₁ (t-u)) (r₂ (t-u)) (r₁ u) (r₂ u) hM
      (hb _ hau).1 (hb _ hau).2.2.1 (hb _ hau).2.1 (hb _ hau).2.2.2
      (hb _ hub).2.1 (hb _ hub).2.2.2
    apply h.trans
    dsimp only [A, d, difference]
    exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (c₁ u-c₂ u)]) hA
  rw [memory_eq_interval n c₁ r₁ t ht.1, memory_eq_interval n c₂ r₂ t ht.1,
    ← intervalIntegral.integral_sub hfi₁ hfi₂]
  calc
    _ ≤ ∫ u in 0..t, |c₁ (t-u)^n*r₁ (t-u)*r₁ u - c₂ (t-u)^n*r₂ (t-u)*r₂ u| :=
      intervalIntegral.abs_integral_le_integral_abs ht.1
    _ ≤ ∫ u in 0..t, A * (d (t-u)+d u) :=
      intervalIntegral.integral_mono_on ht.1 (hfi₁.sub hfi₂).abs
        ((hdri.add hdui).const_mul A) hpoint
    _ = 2 * A * ∫ u in 0..t, d u := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hdri hdui,
        intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
      ring

theorem IntegratedSolution.rhs_integrableOn (n : ℕ) (ell B : ℝ) (c r : ℝ → ℝ)
    (h : IntegratedSolution n ell B c r) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun t => -ell * r t + B * memory n c r t) (Icc 0 T) volume := by
  obtain ⟨M, hM, hb⟩ := h.locally_bounded T hT
  apply bounded_measurable_integrableOn
    ((measurable_const.mul h.measurable_r).add
      (measurable_const.mul (memory_measurable n c r h.measurable_c h.measurable_r)))
    (M := |ell| * M + |B| * (T * M ^ (n + 2)))
  intro t ht
  calc
    _ ≤ |-ell * r t| + |B * memory n c r t| := abs_add_le _ _
    _ = |ell| * |r t| + |B| * |memory n c r t| := by simp [abs_mul]
    _ ≤ _ := by
      gcongr
      · exact (hb t ht).2
      · exact memory_bound n c r T M t (by linarith)
          h.measurable_c h.measurable_r hb ht

/-- Full finite-horizon uniqueness of the locally bounded integrated system. -/
theorem integrated_stationary_unique_on (n : ℕ) (ell B : ℝ) (c₁ r₁ c₂ r₂ : ℝ → ℝ)
    (h₁ : IntegratedSolution n ell B c₁ r₁) (h₂ : IntegratedSolution n ell B c₂ r₂)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, c₁ t = c₂ t ∧ r₁ t = r₂ t := by
  obtain ⟨M₁, hM₁, hb₁⟩ := h₁.locally_bounded T hT
  obtain ⟨M₂, hM₂, hb₂⟩ := h₂.locally_bounded T hT
  let M : ℝ := max M₁ M₂
  have hM : 1 ≤ M := hM₁.trans (le_max_left _ _)
  have hb (u : ℝ) (hu : u ∈ Icc 0 T) :
      |c₁ u| ≤ M ∧ |r₁ u| ≤ M ∧ |c₂ u| ≤ M ∧ |r₂ u| ≤ M :=
    ⟨(hb₁ u hu).1.trans (le_max_left _ _), (hb₁ u hu).2.trans (le_max_left _ _),
      (hb₂ u hu).1.trans (le_max_right _ _), (hb₂ u hu).2.trans (le_max_right _ _)⟩
  obtain ⟨hc₁, hr₁⟩ := h₁.continuousOn n ell B c₁ r₁ T hT
  obtain ⟨hc₂, hr₂⟩ := h₂.continuousOn n ell B c₂ r₂ T hT
  let d : ℝ → ℝ := difference c₁ r₁ c₂ r₂
  let A : ℝ := ((n : ℝ) + 1) * M ^ (n + 2)
  let K : ℝ := 1 + |ell| + 2 * |B| * A * T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : ContinuousOn d (Icc 0 T) := (hc₁.sub hc₂).abs.add (hr₁.sub hr₂).abs
  have hdnonneg (t : ℝ) : 0 ≤ d t := difference_nonneg c₁ r₁ c₂ r₂ t
  have hdi (t : ℝ) (ht : t ∈ Icc 0 T) : IntervalIntegrable d volume 0 t :=
    (show ContinuousOn d (uIcc 0 t) by
      rw [uIcc_of_le ht.1]
      exact hd.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
  have hle (t : ℝ) (ht : t ∈ Icc 0 T) : d t ≤ K * ∫ u in 0..t, d u := by
    have hr₁i : IntervalIntegrable r₁ volume 0 t :=
      (show ContinuousOn r₁ (uIcc 0 t) by
        rw [uIcc_of_le ht.1]
        exact hr₁.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
    have hr₂i : IntervalIntegrable r₂ volume 0 t :=
      (show ContinuousOn r₂ (uIcc 0 t) by
        rw [uIcc_of_le ht.1]
        exact hr₂.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
    have hdc : |c₁ t-c₂ t| ≤ ∫ u in 0..t, d u := by
      have heq : c₁ t-c₂ t = -(∫ u in 0..t, r₁ u-r₂ u) := by
        rw [h₁.correlation t ht.1, h₂.correlation t ht.1,
          intervalIntegral.integral_sub hr₁i hr₂i]
        ring
      rw [heq, abs_neg]
      exact (intervalIntegral.abs_integral_le_integral_abs ht.1).trans
        (intervalIntegral.integral_mono_on ht.1 (hr₁i.sub hr₂i).abs (hdi t ht)
          (fun u _ => by dsimp [d, difference]; exact le_add_of_nonneg_left (abs_nonneg _)))
    let f₁ : ℝ → ℝ := fun v => -ell*r₁ v + B*memory n c₁ r₁ v
    let f₂ : ℝ → ℝ := fun v => -ell*r₂ v + B*memory n c₂ r₂ v
    have hi₁ : IntervalIntegrable f₁ volume 0 t :=
      (show IntegrableOn f₁ (uIcc 0 t) volume by
        rw [uIcc_of_le ht.1]
        exact (h₁.rhs_integrableOn n ell B c₁ r₁ T hT).mono_set
          (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
    have hi₂ : IntervalIntegrable f₂ volume 0 t :=
      (show IntegrableOn f₂ (uIcc 0 t) volume by
        rw [uIcc_of_le ht.1]
        exact (h₂.rhs_integrableOn n ell B c₂ r₂ T hT).mono_set
          (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
    have hFpos : 0 ≤ ∫ u in 0..t, d u :=
      intervalIntegral.integral_nonneg ht.1 (fun u _ => hdnonneg u)
    have hpoint (v : ℝ) (hv : v ∈ Icc 0 t) :
        |f₁ v-f₂ v| ≤ |ell| * d v + 2 * |B| * A * ∫ u in 0..t, d u := by
      have hvT : v ∈ Icc 0 T := ⟨hv.1, hv.2.trans ht.2⟩
      have hmemory := memory_difference_bound n c₁ r₁ c₂ r₂ T M v hM hc₁ hr₁ hc₂ hr₂ hb hvT
      have hFmono : (∫ u in 0..v, d u) ≤ ∫ u in 0..t, d u :=
        intervalIntegral.integral_mono_interval le_rfl hv.1 hv.2
          (Filter.Eventually.of_forall hdnonneg) (hdi t ht)
      have hdrv : |r₁ v-r₂ v| ≤ d v := by
        dsimp [d, difference]
        exact le_add_of_nonneg_left (abs_nonneg _)
      have heq : f₁ v-f₂ v = -ell*(r₁ v-r₂ v)+B*(memory n c₁ r₁ v-memory n c₂ r₂ v) := by
        dsimp [f₁, f₂]; ring
      rw [heq]
      calc
        _ ≤ |-ell*(r₁ v-r₂ v)| +|B*(memory n c₁ r₁ v-memory n c₂ r₂ v)| := abs_add_le _ _
        _ = |ell| *|r₁ v-r₂ v| +|B| *|memory n c₁ r₁ v-memory n c₂ r₂ v| := by simp [abs_mul]
        _ ≤ |ell| *d v+|B| *(2*A*(∫ u in 0..v, d u)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hdrv (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hmemory (abs_nonneg _))
        _ ≤ |ell| *d v+|B| *(2*A*(∫ u in 0..t, d u)) := by gcongr
        _ = _ := by ring
    have hdr : |r₁ t-r₂ t| ≤ (|ell| +2*|B| *A*T) * ∫ u in 0..t, d u := by
      have heq : r₁ t-r₂ t = ∫ v in 0..t, f₁ v-f₂ v := by
        rw [intervalIntegral.integral_sub hi₁ hi₂, h₁.response t ht.1, h₂.response t ht.1]
        dsimp only [f₁, f₂]
        ring
      rw [heq]
      calc
        _ ≤ ∫ v in 0..t, |f₁ v-f₂ v| := intervalIntegral.abs_integral_le_integral_abs ht.1
        _ ≤ ∫ v in 0..t, |ell| *d v+2*|B| *A*(∫ u in 0..t, d u) :=
          intervalIntegral.integral_mono_on ht.1 (hi₁.sub hi₂).abs
            ((hdi t ht).const_mul |ell| |>.add intervalIntegrable_const) hpoint
        _ = |ell| *(∫ u in 0..t, d u)+t*(2*|B| *A*(∫ u in 0..t, d u)) := by
          rw [intervalIntegral.integral_add ((hdi t ht).const_mul |ell|) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          simp
        _ ≤ |ell| *(∫ u in 0..t, d u)+T*(2*|B| *A*(∫ u in 0..t, d u)) := by
          gcongr
          exact ht.2
        _ = _ := by ring
    change |c₁ t-c₂ t| + |r₁ t-r₂ t| ≤ K * ∫ u in 0..t, d u
    dsimp only [K]
    nlinarith only [hdc, hdr]
  have hzero := integral_gronwall_zero d T K hT hd (fun t _ => hdnonneg t) hle
  intro t ht
  have hd0 := hzero t ht
  dsimp [d, difference] at hd0
  have hc0 : |c₁ t-c₂ t| = 0 := by linarith [abs_nonneg (c₁ t-c₂ t), abs_nonneg (r₁ t-r₂ t)]
  have hr0 : |r₁ t-r₂ t| = 0 := by linarith [abs_nonneg (c₁ t-c₂ t), abs_nonneg (r₁ t-r₂ t)]
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp hc0), sub_eq_zero.mp (abs_eq_zero.mp hr0)⟩

/-- Lemma 6.2: fixed finite multiplier gives at most one locally bounded solution.
The proof works for every natural memory power and every real coefficient. -/
theorem integrated_stationary_unique (n : ℕ) (ell B : ℝ) (c₁ r₁ c₂ r₂ : ℝ → ℝ)
    (h₁ : IntegratedSolution n ell B c₁ r₁) (h₂ : IntegratedSolution n ell B c₂ r₂) :
    ∀ t : ℝ, 0 ≤ t → c₁ t = c₂ t ∧ r₁ t = r₂ t := by
  intro t ht
  exact integrated_stationary_unique_on n ell B c₁ r₁ c₂ r₂ h₁ h₂ t ht t ⟨ht, le_rfl⟩

/-- The same integrated solution class with domain exactly `[0,infinity)`.
Real interval integrals use the canonical nonnegative representative. -/
structure RayIntegratedSolution (n : ℕ) (ell B : ℝ) (c r : ℝ≥0 → ℝ) : Prop where
  measurable_c : Measurable c
  measurable_r : Measurable r
  locally_bounded : ∀ T : ℝ, 0 ≤ T → ∃ M : ℝ, 1 ≤ M ∧
    ∀ t : ℝ≥0, (t:ℝ) ≤ T → |c t| ≤ M ∧ |r t| ≤ M
  correlation : ∀ t : ℝ≥0,
    c t = 1-∫ u in 0..(t:ℝ), r (Real.toNNReal u)
  response : ∀ t : ℝ≥0, r t = 1+∫ v in 0..(t:ℝ),
    -ell*r (Real.toNNReal v)+B*memory n (fun u => c (Real.toNNReal u))
      (fun u => r (Real.toNNReal u)) v

theorem RayIntegratedSolution.real_representative (n : ℕ) (ell B : ℝ) (c r : ℝ≥0 → ℝ)
    (h : RayIntegratedSolution n ell B c r) :
    IntegratedSolution n ell B (fun t => c (Real.toNNReal t)) (fun t => r (Real.toNNReal t)) := by
  refine ⟨h.measurable_c.comp measurable_id.real_toNNReal,
    h.measurable_r.comp measurable_id.real_toNNReal,?_,?_,?_⟩
  · intro T hT
    obtain ⟨M,hM,hb⟩ := h.locally_bounded T hT
    refine ⟨M,hM,?_⟩
    intro t ht
    exact hb (Real.toNNReal t) (by simpa only [Real.coe_toNNReal t ht.1] using ht.2)
  · intro t ht
    simpa only [Real.coe_toNNReal t ht] using h.correlation (Real.toNNReal t)
  · intro t ht
    simpa only [Real.coe_toNNReal t ht] using h.response (Real.toNNReal t)

/-- Exact-domain version of Lemma 6.2. No regularity on negative times is required. -/
theorem ray_integrated_stationary_unique (n : ℕ) (ell B : ℝ) (c₁ r₁ c₂ r₂ : ℝ≥0 → ℝ)
    (h₁ : RayIntegratedSolution n ell B c₁ r₁) (h₂ : RayIntegratedSolution n ell B c₂ r₂) :
    c₁ = c₂ ∧ r₁ = r₂ := by
  have heq := integrated_stationary_unique n ell B
    (fun t => c₁ (Real.toNNReal t)) (fun t => r₁ (Real.toNNReal t))
    (fun t => c₂ (Real.toNNReal t)) (fun t => r₂ (Real.toNNReal t))
    (h₁.real_representative n ell B c₁ r₁) (h₂.real_representative n ell B c₂ r₂)
  constructor
  · funext t
    simpa only [Real.toNNReal_coe] using (heq (t:ℝ) t.coe_nonneg).1
  · funext t
    simpa only [Real.toNNReal_coe] using (heq (t:ℝ) t.coe_nonneg).2

end

end SphericalAging.StationaryUniqueness
