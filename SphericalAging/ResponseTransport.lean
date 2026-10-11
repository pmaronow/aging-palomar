module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

public section

/-!
# Response-budget transport (Lemma 12.3, `resp:transport`)

The primitive is defined as an actual integral of the continuous clipped
power weight. Its endpoint formulas, absolute continuity after composition,
and almost-everywhere chain rule are proved below from mathlib's calculus.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace SphericalAging.ResponseTransport

@[expose] def clippedWeight (p : ℕ) (a y : ℝ) : ℝ := min (y ^ (p - 1) / a ^ (p - 1)) 1

@[expose] def clippedPrimitive (p : ℕ) (a y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..y, clippedWeight p a x

@[expose] def positiveDefect (z r : ℝ → ℝ) (s : ℝ) : ℝ := max (deriv z s - r s) 0

@[expose] def weightedBudget (p : ℕ) (z r : ℝ → ℝ) (u v : ℝ) : ℝ :=
  ∫ s in u..v, z s ^ (p - 1) * r s

lemma clippedWeight_continuous (p : ℕ) (a : ℝ) : Continuous (clippedWeight p a) := by
  unfold clippedWeight
  fun_prop

lemma clippedWeight_nonneg (p : ℕ) {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    0 ≤ clippedWeight p a y := by
  exact le_min (div_nonneg (pow_nonneg hy _) (le_of_lt (pow_pos ha _))) (by norm_num)

lemma clippedWeight_le_one (p : ℕ) (a y : ℝ) : clippedWeight p a y ≤ 1 :=
  min_le_right _ _

lemma clippedWeight_le_power (p : ℕ) (a y : ℝ) :
    clippedWeight p a y ≤ y ^ (p - 1) / a ^ (p - 1) := min_le_left _ _

lemma clippedWeight_of_le (p : ℕ) {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y)
    (hya : y ≤ a) : clippedWeight p a y = y ^ (p - 1) / a ^ (p - 1) := by
  unfold clippedWeight
  apply min_eq_left
  apply (div_le_one₀ (pow_pos ha _)).2
  exact pow_le_pow_left₀ hy hya _

lemma clippedWeight_of_ge (p : ℕ) {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) :
    clippedWeight p a y = 1 := by
  unfold clippedWeight
  apply min_eq_right
  apply (one_le_div₀ (pow_pos ha _)).2
  exact pow_le_pow_left₀ ha.le hay _

lemma clippedPrimitive_hasDerivAt (p : ℕ) (a y : ℝ) :
    HasDerivAt (clippedPrimitive p a) (clippedWeight p a y) y := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((clippedWeight_continuous p a).intervalIntegrable 0 y)
    ((clippedWeight_continuous p a).stronglyMeasurable.stronglyMeasurableAtFilter)
    (clippedWeight_continuous p a).continuousAt

lemma clippedPrimitive_lipschitz (p : ℕ) {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith 1 (clippedPrimitive p a) (Ici 0) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun y _ => (clippedPrimitive_hasDerivAt p a y).differentiableAt) ?_ (convex_Ici 0)
  intro y hy
  rw [(clippedPrimitive_hasDerivAt p a y).deriv]
  change ‖clippedWeight p a y‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (clippedWeight_nonneg p ha hy)]
  exact clippedWeight_le_one p a y

lemma clippedPrimitive_comp_ac {p : ℕ} {a u v : ℝ} {z : ℝ → ℝ}
    (ha : 0 < a) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) :
    AbsolutelyContinuousOnInterval (fun s => clippedPrimitive p a (z s)) u v := by
  exact (clippedPrimitive_lipschitz p ha).comp_absolutelyContinuousOnInterval hz0 hz

lemma clippedPrimitive_comp_deriv_ae {p : ℕ} {a u v : ℝ} {z : ℝ → ℝ}
    (hz : AbsolutelyContinuousOnInterval z u v) :
    ∀ᵐ s, s ∈ uIcc u v →
      deriv (fun t => clippedPrimitive p a (z t)) s = clippedWeight p a (z s) * deriv z s := by
  filter_upwards [hz.ae_differentiableAt] with s hs hmem
  exact ((clippedPrimitive_hasDerivAt p a (z s)).comp s (hs hmem).hasDerivAt).deriv

lemma clippedPrimitive_comp_integral {p : ℕ} {a u v : ℝ} {z : ℝ → ℝ}
    (ha : 0 < a) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) :
    ∫ s in u..v, clippedWeight p a (z s) * deriv z s =
      clippedPrimitive p a (z v) - clippedPrimitive p a (z u) := by
  rw [← (clippedPrimitive_comp_ac ha hz hz0).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [clippedPrimitive_comp_deriv_ae hz] with s hs hmem
  exact (hs (uIoc_subset_uIcc hmem)).symm

lemma clippedPrimitive_lower_formula {p : ℕ} {a y : ℝ} (hp : 3 ≤ p)
    (ha : 0 < a) (hy : 0 ≤ y) (hya : y ≤ a) :
    clippedPrimitive p a y = y ^ p / ((p : ℝ) * a ^ (p - 1)) := by
  have hexp : p - 1 + 1 = p := by omega
  unfold clippedPrimitive
  calc
    _ = ∫ x in (0 : ℝ)..y, x ^ (p - 1) / a ^ (p - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hy] at hx
      exact clippedWeight_of_le p ha hx.1 (le_trans hx.2 hya)
    _ = (∫ x in (0 : ℝ)..y, x ^ (p - 1)) / a ^ (p - 1) :=
      intervalIntegral.integral_div _ _
    _ = y ^ p / ((p : ℝ) * a ^ (p - 1)) := by
      rw [integral_pow]
      have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by exact_mod_cast hexp
      rw [hexp, hcast]
      simp only [show p ≠ 0 by omega, ne_eq, not_false_eq_true, zero_pow, sub_zero]
      ring

lemma clippedPrimitive_upper_formula {p : ℕ} {a y : ℝ} (hp : 3 ≤ p)
    (ha : 0 < a) (hay : a ≤ y) :
    clippedPrimitive p a y = y - ((p : ℝ) - 1) / (p : ℝ) * a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have ha0 := ne_of_gt ha
  have hexp : p = (p - 1) + 1 := by omega
  have hat : clippedPrimitive p a a = a / p := by
    rw [clippedPrimitive_lower_formula hp ha ha.le le_rfl]
    nth_rw 1 [hexp]
    rw [pow_succ]
    field_simp
  have hseg : (∫ x in a..y, clippedWeight p a x) = y - a := by
    calc
      _ = ∫ _x in a..y, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hay] at hx
        exact clippedWeight_of_ge p ha hx.1
      _ = y - a := by simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    ((clippedWeight_continuous p a).intervalIntegrable 0 a)
    ((clippedWeight_continuous p a).intervalIntegrable a y)
  change clippedPrimitive p a a + (∫ x in a..y, clippedWeight p a x) =
    clippedPrimitive p a y at hsum
  rw [hat, hseg] at hsum
  rw [← hsum]
  field_simp
  ring

lemma positiveDefect_nonneg (z r : ℝ → ℝ) (s : ℝ) :
    0 ≤ positiveDefect z r s := le_max_right _ _

lemma positiveDefect_intervalIntegrable {u v : ℝ} {z r : ℝ → ℝ}
    (hz : AbsolutelyContinuousOnInterval z u v) (hr : IntervalIntegrable r volume u v) :
    IntervalIntegrable (positiveDefect z r) volume u v := by
  rw [intervalIntegrable_iff] at hr ⊢
  have hd := intervalIntegrable_iff.mp hz.intervalIntegrable_deriv
  exact (hd.sub hr).sup (intervalIntegrable_iff.mp (intervalIntegrable_const (μ := volume) (c := (0 : ℝ))))

lemma weightedBudget_intervalIntegrable {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hz : AbsolutelyContinuousOnInterval z u v) (hr : IntervalIntegrable r volume u v) :
    IntervalIntegrable (fun s => z s ^ (p - 1) * r s) volume u v := by
  exact hr.continuousOn_mul (hz.continuousOn.pow _)

lemma weightedBudget_nonneg {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (huv : u ≤ v) (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) : 0 ≤ weightedBudget p z r u v := by
  apply intervalIntegral.integral_nonneg huv
  intro s hs
  rw [← uIcc_of_le huv] at hs
  exact mul_nonneg (pow_nonneg (hz0 s hs) _) (hr0 s hs)

lemma clipped_defect_bound {p : ℕ} {a x d r : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) (hr : 0 ≤ r) :
    clippedWeight p a x * d - x ^ (p - 1) * r / a ^ (p - 1) ≤ max (d - r) 0 := by
  have hw0 := clippedWeight_nonneg p ha hx
  have hw1 := clippedWeight_le_one p a x
  have he : clippedWeight p a x * (d - r) ≤ max (d - r) 0 := by
    rcases le_total (d - r) 0 with h | h
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hw0 h) (le_max_right _ _)
    · calc
        _ ≤ 1 * (d - r) := mul_le_mul_of_nonneg_right hw1 h
        _ ≤ max (d - r) 0 := by simp only [one_mul]; exact le_max_left _ _
  have hb := mul_le_mul_of_nonneg_right (clippedWeight_le_power p a x) hr
  rw [div_mul_eq_mul_div] at hb
  nlinarith

lemma clipped_transport_lower_bound {p : ℕ} {a u v : ℝ} {z r : ℝ → ℝ}
    (ha : 0 < a) (huv : u ≤ v) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) (hr : IntervalIntegrable r volume u v)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) :
    clippedPrimitive p a (z v) - clippedPrimitive p a (z u) -
      weightedBudget p z r u v / a ^ (p - 1) ≤
        ∫ s in u..v, positiveDefect z r s := by
  have hwc : ContinuousOn (fun s => clippedWeight p a (z s)) (uIcc u v) :=
    (clippedWeight_continuous p a).comp_continuousOn hz.continuousOn
  have hwz := hz.intervalIntegrable_deriv.continuousOn_mul hwc
  have hbudget := weightedBudget_intervalIntegrable hz hr (p := p)
  have hdiv := hbudget.div_const (a ^ (p - 1))
  have hcomp := clippedPrimitive_comp_integral ha hz hz0 (p := p)
  have hm := intervalIntegral.integral_mono_on huv (hwz.sub hdiv)
    (positiveDefect_intervalIntegrable hz hr) (fun s hs => by
      rw [← uIcc_of_le huv] at hs
      exact clipped_defect_bound ha (hz0 s hs) (hr0 s hs))
  rw [intervalIntegral.integral_sub hwz hdiv, hcomp, intervalIntegral.integral_div] at hm
  exact hm

/-- The manuscript's `bar z`, with the real positive p-th root. -/
@[expose] def budgetRoot (p : ℕ) (z r : ℝ → ℝ) (u v : ℝ) : ℝ :=
  (z u ^ p + (p : ℝ) * weightedBudget p z r u v) ^ (1 / (p : ℝ))

@[expose] def transportDeficit (p : ℕ) (z r : ℝ → ℝ) (u v : ℝ) : ℝ :=
  max (z v - budgetRoot p z r u v) 0

lemma budgetRoot_nonneg {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (huv : u ≤ v) (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) : 0 ≤ budgetRoot p z r u v := by
  exact Real.rpow_nonneg (add_nonneg (pow_nonneg (hz0 u (left_mem_uIcc)) _)
    (mul_nonneg (Nat.cast_nonneg _) (weightedBudget_nonneg huv hz0 hr0))) _

lemma budgetRoot_pow {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hp : 3 ≤ p) (huv : u ≤ v) (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) :
    budgetRoot p z r u v ^ p = z u ^ p + (p : ℝ) * weightedBudget p z r u v := by
  unfold budgetRoot
  rw [one_div]
  exact Real.rpow_inv_natCast_pow
    (add_nonneg (pow_nonneg (hz0 u left_mem_uIcc) _)
      (mul_nonneg (Nat.cast_nonneg _) (weightedBudget_nonneg huv hz0 hr0))) (by omega)

lemma initial_le_budgetRoot {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hp : 3 ≤ p) (huv : u ≤ v) (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) : z u ≤ budgetRoot p z r u v := by
  apply le_of_pow_le_pow_left₀ (show p ≠ 0 by omega)
    (budgetRoot_nonneg huv hz0 hr0)
  rw [budgetRoot_pow hp huv hz0 hr0]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (weightedBudget_nonneg huv hz0 hr0))

/-- Lemma `resp:transport`, first inequality, including the zero-budget case. -/
theorem response_transport_L1 {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hp : 3 ≤ p) (huv : u < v) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) (hr : IntervalIntegrable r volume u v)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) :
    transportDeficit p z r u v ≤ ∫ s in u..v, positiveDefect z r s := by
  have hA0 : 0 ≤ ∫ s in u..v, positiveDefect z r s :=
    intervalIntegral.integral_nonneg_of_forall huv.le (positiveDefect_nonneg z r)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hJ0 := weightedBudget_nonneg (p := p) huv.le hz0 hr0
  have hz_u0 := hz0 u left_mem_uIcc
  have hz_v0 := hz0 v right_mem_uIcc
  have hb0 := budgetRoot_nonneg (p := p) huv.le hz0 hr0
  have hbp := budgetRoot_pow hp huv.le hz0 hr0
  have hzu := initial_le_budgetRoot hp huv.le hz0 hr0
  by_cases hlarge : z v ≤ budgetRoot p z r u v
  · unfold transportDeficit
    rw [max_eq_right (sub_nonpos.mpr hlarge)]
    exact hA0
  have hbv : budgetRoot p z r u v < z v := lt_of_not_ge hlarge
  unfold transportDeficit
  rw [max_eq_left (sub_nonneg.mpr hbv.le)]
  by_cases hbpos : 0 < budgetRoot p z r u v
  · have hbound := clipped_transport_lower_bound hbpos huv.le hz hz0 hr hr0 (p := p)
    rw [clippedPrimitive_upper_formula hp hbpos hbv.le,
      clippedPrimitive_lower_formula hp hbpos hz_u0 hzu] at hbound
    have hpow : budgetRoot p z r u v ^ p =
        budgetRoot p z r u v ^ (p - 1) * budgetRoot p z r u v := by
      simpa only [Nat.sub_add_cancel (show 1 ≤ p by omega)] using
        (pow_succ (budgetRoot p z r u v) (p - 1))
    have hid : z v - ((p : ℝ) - 1) / p * budgetRoot p z r u v -
        z u ^ p / ((p : ℝ) * budgetRoot p z r u v ^ (p - 1)) -
        weightedBudget p z r u v / budgetRoot p z r u v ^ (p - 1) =
        z v - budgetRoot p z r u v := by
      have heq : z u ^ p + (p : ℝ) * weightedBudget p z r u v =
          budgetRoot p z r u v ^ (p - 1) * budgetRoot p z r u v := hbp.symm.trans hpow
      field_simp
      nlinarith [heq]
    rwa [hid] at hbound
  · have hbzero : budgetRoot p z r u v = 0 := le_antisymm (le_of_not_gt hbpos) hb0
    have hzzero : z u = 0 := le_antisymm (by simpa [hbzero] using hzu) hz_u0
    have hJzero : weightedBudget p z r u v = 0 := by
      rw [hbzero, hzzero, zero_pow (show p ≠ 0 by omega),
        zero_add] at hbp
      exact (mul_eq_zero.mp hbp.symm).resolve_left (ne_of_gt hp0)
    rw [hbzero, sub_zero]
    by_contra hfail
    have hAv : (∫ s in u..v, positiveDefect z r s) < z v := lt_of_not_ge hfail
    let a : ℝ := (z v - ∫ s in u..v, positiveDefect z r s) / 2
    have ha : 0 < a := by dsimp [a]; linarith
    have hav : a ≤ z v := by dsimp [a]; linarith
    have hc : ((p : ℝ) - 1) / (p : ℝ) ≤ 1 := (div_le_one₀ hp0).2 (by linarith)
    have hbound := clipped_transport_lower_bound ha huv.le hz hz0 hr hr0 (p := p)
    rw [clippedPrimitive_upper_formula hp ha hav,
      hzzero, clippedPrimitive_lower_formula hp ha le_rfl ha.le, hJzero] at hbound
    simp only [zero_pow (show p ≠ 0 by omega), zero_div, sub_zero] at hbound
    have hca := mul_le_mul_of_nonneg_right hc ha.le
    dsimp [a] at hca hbound
    nlinarith

/-- Cauchy--Schwarz on a finite real interval, proved by integrating a square. -/
lemma interval_square_bound {u v : ℝ} {f : ℝ → ℝ} (huv : u < v)
    (hf : IntervalIntegrable f volume u v)
    (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume u v) :
    (∫ s in u..v, f s) ^ 2 ≤ (v - u) * ∫ s in u..v, f s ^ 2 := by
  let A : ℝ := ∫ s in u..v, f s
  let L : ℝ := v - u
  have hL : 0 < L := sub_pos.mpr huv
  have hc : IntervalIntegrable (fun _ : ℝ => A ^ 2) volume u v := intervalIntegrable_const
  have hl := hf.const_mul (2 * A * L)
  have hq := hf2.const_mul (L ^ 2)
  have hexpand : (∫ s in u..v, (A - L * f s) ^ 2) = L ^ 2 *
      (∫ s in u..v, f s ^ 2) - L * A ^ 2 := by
    calc
      _ = ∫ s in u..v, A ^ 2 - 2 * A * L * f s + L ^ 2 * f s ^ 2 := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hc.sub hl) hq,
          intervalIntegral.integral_sub hc hl, intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        change L * A ^ 2 - 2 * A * L * A + L ^ 2 * (∫ s in u..v, f s ^ 2) = _
        ring
  have hnn : 0 ≤ ∫ s in u..v, (A - L * f s) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall huv.le (fun _ => sq_nonneg _)
  rw [hexpand] at hnn
  have hh : 0 ≤ L * (L * (∫ s in u..v, f s ^ 2) - A ^ 2) := by nlinarith only [hnn]
  have := nonneg_of_mul_nonneg_right hh hL
  dsimp [A, L] at this
  linarith

/-- Extended-valued square cost. It is infinite for a nonsquare-integrable defect. -/
@[expose] def defectSquareCost (z r : ℝ → ℝ) (u v : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc u v, ENNReal.ofReal (positiveDefect z r s ^ 2)

lemma defectSquareCost_eq_top_iff {u v : ℝ} {z r : ℝ → ℝ}
    (huv : u ≤ v) (hz : AbsolutelyContinuousOnInterval z u v)
    (hr : IntervalIntegrable r volume u v) :
    defectSquareCost z r u v = ∞ ↔
      ¬ IntervalIntegrable (fun s => positiveDefect z r s ^ 2) volume u v := by
  have hf := (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mp
    (positiveDefect_intervalIntegrable hz hr)
  have hmeas : AEStronglyMeasurable (fun s => positiveDefect z r s ^ 2)
      (volume.restrict (Ioc u v)) := hf.aestronglyMeasurable.pow 2
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc u v)] fun s => positiveDefect z r s ^ 2 :=
    Eventually.of_forall (fun _ => sq_nonneg _)
  unfold defectSquareCost
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
  simpa only [not_not, IntegrableOn] using
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnn).not

/-- Lemma `resp:transport`, second inequality, in `ENNReal` including infinite cost. -/
theorem response_transport_L2 {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hp : 3 ≤ p) (huv : u < v) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) (hr : IntervalIntegrable r volume u v)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) :
    ENNReal.ofReal (transportDeficit p z r u v ^ 2) ≤
      ENNReal.ofReal (v - u) * defectSquareCost z r u v := by
  by_cases hsq : IntervalIntegrable (fun s => positiveDefect z r s ^ 2) volume u v
  · have hD := response_transport_L1 hp huv hz hz0 hr hr0
    have hD0 : 0 ≤ transportDeficit p z r u v := le_max_right _ _
    have hA0 : 0 ≤ ∫ s in u..v, positiveDefect z r s :=
      intervalIntegral.integral_nonneg_of_forall huv.le (positiveDefect_nonneg z r)
    have hAA := interval_square_bound huv (positiveDefect_intervalIntegrable hz hr) hsq
    have hreal : transportDeficit p z r u v ^ 2 ≤
        (v - u) * ∫ s in u..v, positiveDefect z r s ^ 2 := by
      exact le_trans (pow_le_pow_left₀ hD0 hD 2) hAA
    have hfi := (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le).mp hsq
    have heq := ofReal_integral_eq_lintegral_ofReal hfi
      (Eventually.of_forall (fun s => sq_nonneg (positiveDefect z r s)))
    rw [← intervalIntegral.integral_of_le huv.le] at heq
    unfold defectSquareCost
    rw [← heq, ← ENNReal.ofReal_mul (sub_nonneg.mpr huv.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  · rw [(defectSquareCost_eq_top_iff huv.le hz hr).2 hsq,
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr huv))]
    exact le_top

/-- Both conclusions of standalone manuscript Lemma 12.3 (`resp:transport`). -/
theorem response_budget_transport {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hp : 3 ≤ p) (huv : u < v) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) (hr : IntervalIntegrable r volume u v)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) :
    transportDeficit p z r u v ≤ (∫ s in u..v, positiveDefect z r s) ∧
    ENNReal.ofReal (transportDeficit p z r u v ^ 2) ≤
      ENNReal.ofReal (v - u) * defectSquareCost z r u v :=
  ⟨response_transport_L1 hp huv hz hz0 hr hr0, response_transport_L2 hp huv hz hz0 hr hr0⟩

/-- The clipped weight is exactly the displayed weight in the manuscript. -/
lemma clippedWeight_eq_display (p : ℕ) (a y : ℝ) :
    clippedWeight p a y = min ((y / a) ^ (p - 1)) 1 := by
  simp only [clippedWeight, div_pow]

/-- The ordinary real-valued square inequality when the square is integrable. -/
theorem response_transport_L2_finite {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hp : 3 ≤ p) (huv : u < v) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) (hr : IntervalIntegrable r volume u v)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s)
    (hsq : IntervalIntegrable (fun s => positiveDefect z r s ^ 2) volume u v) :
    transportDeficit p z r u v ^ 2 ≤ (v - u) *
      ∫ s in u..v, positiveDefect z r s ^ 2 := by
  exact le_trans (pow_le_pow_left₀ (le_max_right _ _)
    (response_transport_L1 hp huv hz hz0 hr hr0) 2)
    (interval_square_bound huv (positiveDefect_intervalIntegrable hz hr) hsq)

/-- Lemma 12.3 in expanded manuscript notation, with no extra endpoint or
chain-rule hypotheses. The Lebesgue integral on the right permits `∞`. -/
theorem response_budget_transport_expanded {p : ℕ} {u v : ℝ} {z r : ℝ → ℝ}
    (hp : 3 ≤ p) (huv : u < v) (hz : AbsolutelyContinuousOnInterval z u v)
    (hz0 : ∀ s ∈ uIcc u v, 0 ≤ z s) (hr : IntervalIntegrable r volume u v)
    (hr0 : ∀ s ∈ uIcc u v, 0 ≤ r s) :
    let J := ∫ s in u..v, z s ^ (p - 1) * r s
    let D := max (z v - (z u ^ p + (p : ℝ) * J) ^ (1 / (p : ℝ))) 0
    D ≤ (∫ s in u..v, max (deriv z s - r s) 0) ∧
    ENNReal.ofReal (D ^ 2) ≤ ENNReal.ofReal (v - u) *
      ∫⁻ s in Ioc u v, ENNReal.ofReal ((max (deriv z s - r s) 0) ^ 2) := by
  exact response_budget_transport hp huv hz hz0 hr hr0

end SphericalAging.ResponseTransport
