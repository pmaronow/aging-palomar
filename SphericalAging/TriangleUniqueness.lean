module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

public section

/-!
# Uniqueness on a symmetric causal triangle

The diagonal is an unknown and satisfies its own evolution equation. Only its
initial value is zero. A continuous running square supremum and a Gronwall
argument control both variables together; no prior rows are assumed zero.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.TriangleUniqueness

@[expose] def unitSquare : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1

@[expose] def runningNorm (D : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup ((fun z : ℝ × ℝ => |D (t * z.1) (t * z.2)|) '' unitSquare)

theorem unitSquare_compact : IsCompact unitSquare := isCompact_Icc.prod isCompact_Icc

theorem unitSquare_nonempty : unitSquare.Nonempty := ⟨(0,0), by norm_num [unitSquare]⟩

theorem runningNorm_continuous {D : ℝ → ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) : Continuous (runningNorm D) := by
  exact unitSquare_compact.continuous_sSup
    ((hD.comp ((continuous_fst.mul continuous_snd.fst).prodMk
      (continuous_fst.mul continuous_snd.snd))).abs)

theorem runningNorm_bddAbove {D : ℝ → ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) (t : ℝ) :
    BddAbove ((fun z : ℝ × ℝ => |D (t * z.1) (t * z.2)|) '' unitSquare) :=
  unitSquare_compact.bddAbove_image
    ((hD.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).abs.continuousOn)

theorem runningNorm_dominate {D : ℝ → ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
    |D u v| ≤ runningNorm D t := by
  unfold runningNorm
  apply le_csSup (runningNorm_bddAbove hD t)
  by_cases hzero : t = 0
  · have hu0 : u = 0 := by linarith [hu.1, hu.2]
    have hv0 : v = 0 := by linarith [hv.1, hv.2]
    exact ⟨(0,0), by norm_num [unitSquare], by simp [hzero, hu0, hv0]⟩
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    refine ⟨(u/t,v/t), ?_, ?_⟩
    · exact ⟨⟨div_nonneg hu.1 ht, (div_le_one₀ htpos).2 hu.2⟩,
        ⟨div_nonneg hv.1 ht, (div_le_one₀ htpos).2 hv.2⟩⟩
    · have hu' : t * (u / t) = u := by field_simp
      have hv' : t * (v / t) = v := by field_simp
      simp only [hu', hv']

theorem runningNorm_nonneg {D : ℝ → ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ runningNorm D t :=
  (abs_nonneg _).trans (runningNorm_dominate hD ht ⟨le_refl 0,ht⟩ ⟨le_refl 0,ht⟩)

/-- Integral Gronwall with zero source, proved by differentiating the primitive. -/
theorem continuous_integral_bound_eq_zero
    {d : ℝ → ℝ} {T A : ℝ} (_hT : 0 ≤ T) (hd : Continuous d)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ d t)
    (hbound : ∀ t ∈ Icc 0 T, d t ≤ A * ∫ u in (0 : ℝ)..t, d u) :
    ∀ t ∈ Icc 0 T, d t = 0 := by
  let F : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, d u
  have hderiv (t : ℝ) : HasDerivAt F (d t) t :=
    intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 t)
      hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt
  have hc : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hderiv t).continuousAt)
  have hg := le_gronwallBound_of_liminf_deriv_right_le
    (f := F) (f' := d) (δ := 0) (K := A) (ε := 0)
    hc.continuousOn
    (fun t _ r hr => (hderiv t).hasDerivWithinAt.liminf_right_slope_le hr)
    (show F 0 ≤ 0 by simp [F])
    (fun t ht => by simpa [F] using hbound t ⟨ht.1,ht.2.le⟩)
  intro t ht
  have hF : F t ≤ 0 := by simpa only [gronwallBound_ε0_δ0] using hg t ht
  have hd0 := hbound t ht
  have hFn : 0 ≤ F t := intervalIntegral.integral_nonneg ht.1
    (fun u hu => hnonneg u ⟨hu.1,hu.2.trans ht.2⟩)
  have hFzero : F t = 0 := le_antisymm hF hFn
  change d t ≤ A * F t at hd0
  rw [hFzero, mul_zero] at hd0
  exact le_antisymm hd0 (hnonneg t ht)

theorem memory_norm_le {D K : ℝ → ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {t s S : ℝ}
    (ht : 0 ≤ t) (hs : s ∈ Icc 0 t) (hS : 0 ≤ S)
    (hK : ∀ u ∈ Icc 0 t, |K t u| ≤ S) :
    ‖∫ u in (0 : ℝ)..t, K t u * D u s‖ ≤ S * t * runningNorm D t := by
  have hb : ∀ u ∈ uIoc 0 t, ‖K t u * D u s‖ ≤ S * runningNorm D t := by
    intro u hu
    rw [uIoc_of_le ht] at hu
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hK u ⟨hu.1.le,hu.2⟩)
      (runningNorm_dominate hD ht ⟨hu.1.le,hu.2⟩ hs) (abs_nonneg _) hS
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero, abs_of_nonneg ht, mul_assoc, mul_left_comm, mul_comm] using hi

@[expose] def offdiagSlope (D : ℝ → ℝ → ℝ) (ell : ℝ → ℝ) (K : ℝ → ℝ → ℝ)
    (t s : ℝ) : ℝ := -ell t * D t s + ∫ u in (0 : ℝ)..t, K t u * D u s

@[expose] def diagonalSlope (D : ℝ → ℝ → ℝ) (ell : ℝ → ℝ) (K : ℝ → ℝ → ℝ)
    (t : ℝ) : ℝ := -2 * ell t * D t t + 2 * ∫ u in (0 : ℝ)..t, K t u * D u t

theorem offdiagSlope_norm_le {D K : ℝ → ℝ → ℝ} {ell : ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {T L S t s : ℝ}
    (hL : 0 ≤ L) (hS : 0 ≤ S) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t)
    (hell : |ell t| ≤ L) (hK : ∀ u ∈ Icc 0 t, |K t u| ≤ S) :
    ‖offdiagSlope D ell K t s‖ ≤ (L + S * T) * runningNorm D t := by
  have hmem := memory_norm_le hD ht.1 hs hS hK
  have hnorm := runningNorm_dominate hD ht.1 ⟨ht.1,le_refl t⟩ hs
  have hdnonneg := runningNorm_nonneg hD ht.1
  have htime : S * t * runningNorm D t ≤ S * T * runningNorm D t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 hS) hdnonneg
  unfold offdiagSlope
  calc
    ‖-ell t * D t s + ∫ u in (0 : ℝ)..t, K t u * D u s‖ ≤
        ‖-ell t * D t s‖ + ‖∫ u in (0 : ℝ)..t, K t u * D u s‖ := norm_add_le _ _
    _ ≤ L * runningNorm D t + S * t * runningNorm D t := by
      have hp := mul_le_mul hell hnorm (abs_nonneg (D t s)) hL
      have hp' : ‖-ell t * D t s‖ ≤ L * runningNorm D t := by
        simpa only [norm_mul, norm_neg, Real.norm_eq_abs] using hp
      exact add_le_add hp' hmem
    _ ≤ (L + S * T) * runningNorm D t := by nlinarith only [htime]

theorem diagonalSlope_norm_le {D K : ℝ → ℝ → ℝ} {ell : ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {T L S t : ℝ}
    (hL : 0 ≤ L) (hS : 0 ≤ S) (ht : t ∈ Icc 0 T)
    (hell : |ell t| ≤ L) (hK : ∀ u ∈ Icc 0 t, |K t u| ≤ S) :
    ‖diagonalSlope D ell K t‖ ≤ (2 * (L + S * T)) * runningNorm D t := by
  have heq : diagonalSlope D ell K t = 2 * offdiagSlope D ell K t t := by
    unfold diagonalSlope offdiagSlope
    ring
  rw [heq, norm_mul]
  have hb := mul_le_mul_of_nonneg_left
    (offdiagSlope_norm_le hD hL hS ht ⟨ht.1,le_refl t⟩ hell hK)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    mul_assoc] using hb

theorem diagonal_integral_bound {D K : ℝ → ℝ → ℝ} {ell : ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {T L S : ℝ}
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hzero : D 0 0 = 0)
    (hell : ∀ t ∈ Icc 0 T, |ell t| ≤ L)
    (hK : ∀ t ∈ Icc 0 T, ∀ u ∈ Icc 0 t, |K t u| ≤ S)
    (hdiag : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun x => D x x) (diagonalSlope D ell K t) (Ici 0) t)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    |D s s| ≤ (2 * (L + S * T)) * ∫ u in (0 : ℝ)..s, runningNorm D u := by
  have hd (x : ℝ) (hx : x ∈ Ioo 0 s) :
      HasDerivAt (fun y => D y y) (diagonalSlope D ell K x) x :=
    (hdiag x ⟨hx.1.le,hx.2.le.trans hs.2⟩).hasDerivAt (Ici_mem_nhds hx.1)
  have hi := norm_sub_le_integral_of_norm_deriv_le_of_le
    (f := fun x => D x x) hs.1
    ((hD.comp (continuous_id.prodMk continuous_id)).continuousOn)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (ae_of_all _ (fun x hx => by
      rw [(hd x hx).deriv]
      exact diagonalSlope_norm_le hD hL hS ⟨hx.1.le,hx.2.le.trans hs.2⟩
        (hell x ⟨hx.1.le,hx.2.le.trans hs.2⟩)
        (hK x ⟨hx.1.le,hx.2.le.trans hs.2⟩)))
    (((runningNorm_continuous hD).const_mul (2 * (L + S * T))).intervalIntegrable 0 s)
  simpa only [hzero, sub_zero, Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hi

theorem offdiag_integral_bound {D K : ℝ → ℝ → ℝ} {ell : ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {T L S : ℝ}
    (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hell : ∀ t ∈ Icc 0 T, |ell t| ≤ L)
    (hK : ∀ t ∈ Icc 0 T, ∀ u ∈ Icc 0 t, |K t u| ≤ S)
    (hrow : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, s < t →
      HasDerivAt (fun x => D x s) (offdiagSlope D ell K t s) t)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
    |D t s - D s s| ≤ (L + S * T) * ∫ u in s..t, runningNorm D u := by
  have hd (x : ℝ) (hx : x ∈ Ioo s t) :
      HasDerivAt (fun y => D y s) (offdiagSlope D ell K x s) x :=
    hrow x ⟨hs.1.trans hx.1.le,hx.2.le.trans ht.2⟩ s ⟨hs.1,hx.1.le⟩ hx.1
  have hi := norm_sub_le_integral_of_norm_deriv_le_of_le
    (f := fun x => D x s) hs.2
    ((hD.comp (continuous_id.prodMk continuous_const)).continuousOn)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (ae_of_all _ (fun x hx => by
      rw [(hd x hx).deriv]
      exact offdiagSlope_norm_le hD hL hS
        ⟨hs.1.trans hx.1.le,hx.2.le.trans ht.2⟩ ⟨hs.1,hx.1.le⟩
        (hell x ⟨hs.1.trans hx.1.le,hx.2.le.trans ht.2⟩)
        (hK x ⟨hs.1.trans hx.1.le,hx.2.le.trans ht.2⟩)))
    (((runningNorm_continuous hD).const_mul (L + S * T)).intervalIntegrable s t)
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hi

/-- The homogeneous two-time system is uniquely zero. In particular, the
diagonal is proved zero by its equation, rather than assumed zero. -/
theorem homogeneous_triangle_eq_zero
    {D K : ℝ → ℝ → ℝ} {ell : ℝ → ℝ} {T L S : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hD : Continuous (Function.uncurry D))
    (hsym : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, D t s = D s t)
    (hzero : D 0 0 = 0)
    (hell : ∀ t ∈ Icc 0 T, |ell t| ≤ L)
    (hK : ∀ t ∈ Icc 0 T, ∀ u ∈ Icc 0 t, |K t u| ≤ S)
    (hrow : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, s < t →
      HasDerivAt (fun x => D x s) (offdiagSlope D ell K t s) t)
    (hdiag : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun x => D x x) (diagonalSlope D ell K t) (Ici 0) t) :
    ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, D t s = 0 := by
  let B : ℝ := L + S * T
  let A : ℝ := 2 * B
  have hB : 0 ≤ B := add_nonneg hL (mul_nonneg hS hT)
  have hA : 0 ≤ A := mul_nonneg (by norm_num) hB
  have hcd := runningNorm_continuous hD
  have hpair {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |D t s| ≤ A * ∫ u in (0 : ℝ)..t, runningNorm D u := by
    have hd := diagonal_integral_bound hD hL hS hzero hell hK hdiag
      (show s ∈ Icc 0 T from ⟨hs.1,hs.2.trans ht.2⟩)
    have ho := offdiag_integral_bound hD hL hS hell hK hrow ht hs
    have hnon : 0 ≤ ∫ u in s..t, runningNorm D u :=
      intervalIntegral.integral_nonneg hs.2
        (fun u hu => runningNorm_nonneg hD (hs.1.trans hu.1))
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcd.intervalIntegrable (μ := volume) 0 s) (hcd.intervalIntegrable s t)
    have ha : |D t s| ≤ |D s s| + |D t s - D s s| := by
      have hh := abs_add_le (D s s) (D t s - D s s)
      have heq : D s s + (D t s - D s s) = D t s := by ring
      rw [heq] at hh
      exact hh
    change |D s s| ≤ A * ∫ u in (0 : ℝ)..s, runningNorm D u at hd
    change |D t s - D s s| ≤ B * ∫ u in s..t, runningNorm D u at ho
    have hm : B * (∫ u in s..t, runningNorm D u) ≤
        A * (∫ u in s..t, runningNorm D u) :=
      mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hnon
    calc
      |D t s| ≤ |D s s| + |D t s - D s s| := ha
      _ ≤ A * (∫ u in (0 : ℝ)..s, runningNorm D u) +
          A * (∫ u in s..t, runningNorm D u) := add_le_add hd (ho.trans hm)
      _ = A * (∫ u in (0 : ℝ)..t, runningNorm D u) := by rw [← mul_add, hsplit]
  have hmono {t u : ℝ} (_ht : 0 ≤ t) (hu : u ∈ Icc 0 t) :
      (∫ v in (0 : ℝ)..u, runningNorm D v) ≤ ∫ v in (0 : ℝ)..t, runningNorm D v := by
    apply intervalIntegral.integral_mono_interval (le_refl 0) hu.1 hu.2
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ (fun v hv => runningNorm_nonneg hD hv.1.le))
    · exact hcd.intervalIntegrable 0 t
  have hsquare {t u v : ℝ} (ht : t ∈ Icc 0 T)
      (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
      |D u v| ≤ A * ∫ w in (0 : ℝ)..t, runningNorm D w := by
    rcases le_total v u with hvu | huv
    · exact (hpair ⟨hu.1,hu.2.trans ht.2⟩ ⟨hv.1,hvu⟩).trans
        (mul_le_mul_of_nonneg_left (hmono ht.1 hu) hA)
    · rw [hsym u ⟨hu.1,hu.2.trans ht.2⟩ v ⟨hv.1,hv.2.trans ht.2⟩]
      exact (hpair ⟨hv.1,hv.2.trans ht.2⟩ ⟨hu.1,huv⟩).trans
        (mul_le_mul_of_nonneg_left (hmono ht.1 hv) hA)
  have hrunbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      runningNorm D t ≤ A * ∫ w in (0 : ℝ)..t, runningNorm D w := by
    apply csSup_le (unitSquare_nonempty.image _)
    rintro _ ⟨z,hz,rfl⟩
    have hu' : t * z.1 ∈ Icc 0 t := by
      refine ⟨mul_nonneg ht.1 hz.1.1, ?_⟩
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hz.1.2 ht.1)
    have hv' : t * z.2 ∈ Icc 0 t := by
      refine ⟨mul_nonneg ht.1 hz.2.1, ?_⟩
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hz.2.2 ht.1)
    exact hsquare ht hu' hv'
  have hz := continuous_integral_bound_eq_zero hT hcd
    (fun t ht => runningNorm_nonneg hD ht.1) hrunbound
  intro t ht s hs
  have hh := runningNorm_dominate hD hT ht hs
  rw [hz T ⟨hT,le_refl T⟩] at hh
  exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))

theorem integral_strict_above {f : ℝ → ℝ} {u t : ℝ}
    (hu : 0 ≤ u) (hut : u ≤ t) :
    (∫ z in (0 : ℝ)..t, if u < z then f z else 0) = ∫ z in u..t, f z := by
  have ht : 0 ≤ t := hu.trans hut
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hut]
  change (∫ z, (Ioi u).indicator f z ∂volume.restrict (Ioc 0 t)) = _
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have heq : Ioi u ∩ Ioc 0 t = Ioc u t := by
    ext z
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · intro hz
      exact ⟨hz.1,hz.2.2⟩
    · intro hz
      exact ⟨hz.1,⟨hu.trans_lt hz.1,hz.2⟩⟩
  rw [heq]

theorem integral_strict_below {f : ℝ → ℝ} {z s : ℝ}
    (hz : 0 ≤ z) (hs : 0 ≤ s) :
    (∫ u in (0 : ℝ)..s, if u < z then f u else 0) = ∫ u in (0 : ℝ)..min z s, f u := by
  calc
    (∫ u in (0 : ℝ)..s, if u < z then f u else 0) =
        ∫ u in (0 : ℝ)..s, ({u : ℝ | u ≤ min z s}).indicator f u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne z] with u hne hu
      rw [uIoc_of_le hs] at hu
      have heq : (u < z) ↔ u ≤ min z s := by
        constructor
        · intro h
          exact le_min h.le hu.2
        · intro h
          exact lt_of_le_of_ne (h.trans (min_le_left _ _)) hne
      simp only [Set.indicator, Set.mem_ofPred_eq, heq]
    _ = _ := intervalIntegral.integral_indicator ⟨le_min hz hs,min_le_right _ _⟩

/-- Causal triangular Fubini, derived from measurable indicators and actual
compact integrability of the continuous rectangle integrand. -/
theorem triangular_integral_swap {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ u in (0 : ℝ)..s, ∫ z in u..t, F u z) =
      ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..min z s, F u z := by
  let G : ℝ → ℝ → ℝ := fun u z => if u < z then F u z else 0
  have ht : 0 ≤ t := hs.trans hst
  have hGi : IntegrableOn (Function.uncurry G) (uIoc 0 s ×ˢ uIoc 0 t) := by
    have hFi : IntegrableOn (Function.uncurry F) (Icc 0 s ×ˢ Icc 0 t) :=
      hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hi := hFi.indicator (measurableSet_lt measurable_fst measurable_snd)
    rw [uIoc_of_le hs,uIoc_of_le ht]
    exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap := intervalIntegral_intervalIntegral_swap hGi
  calc
    (∫ u in (0 : ℝ)..s, ∫ z in u..t, F u z) =
        ∫ u in (0 : ℝ)..s, ∫ z in (0 : ℝ)..t, G u z := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hs] at hu
      exact (integral_strict_above hu.1 (hu.2.trans hst)).symm
    _ = ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..s, G u z := hswap
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le ht] at hz
      exact integral_strict_below hz.1 hs

theorem weighted_triangle_memory_swap {R Sigma : ℝ → ℝ → ℝ} {A : ℝ → ℝ}
    (hR : Continuous (Function.uncurry R)) (hSigma : Continuous (Function.uncurry Sigma))
    (hA : Continuous A) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ u in (0 : ℝ)..s, A u * (∫ z in u..t, Sigma t z * R z u)) =
      ∫ z in (0 : ℝ)..t, Sigma t z * (∫ u in (0 : ℝ)..min z s, R z u * A u) := by
  have hF : Continuous (Function.uncurry (fun u z => Sigma t z * R z u * A u)) :=
    (((hSigma.comp (continuous_const.prodMk continuous_snd)).mul
      (hR.comp (continuous_snd.prodMk continuous_fst))).mul (hA.comp continuous_fst))
  calc
    (∫ u in (0 : ℝ)..s, A u * (∫ z in u..t, Sigma t z * R z u)) =
        ∫ u in (0 : ℝ)..s, ∫ z in u..t, Sigma t z * R z u * A u := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [intervalIntegral.integral_mul_const]
      ring
    _ = ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..min z s, Sigma t z * R z u * A u :=
      triangular_integral_swap hF hs hst
    _ = _ := by simp only [mul_assoc, intervalIntegral.integral_const_mul]

theorem weighted_triangle_memory_diagonal {R Sigma : ℝ → ℝ → ℝ} {A : ℝ → ℝ}
    (hR : Continuous (Function.uncurry R)) (hSigma : Continuous (Function.uncurry Sigma))
    (hA : Continuous A) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, A u * (∫ z in u..t, Sigma t z * R z u)) =
      ∫ z in (0 : ℝ)..t, Sigma t z * (∫ u in (0 : ℝ)..z, R z u * A u) := by
  rw [weighted_triangle_memory_swap hR hSigma hA ht (le_refl t)]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le ht] at hz
  dsimp only
  rw [min_eq_left hz.2]

/-- The standard triangular Fubini identity, also obtained without an assumed
swap or an assumed integrability obligation. -/
theorem standard_triangle_integral_swap {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ v in (0 : ℝ)..t, ∫ u in (0 : ℝ)..v, F v u) =
      ∫ u in (0 : ℝ)..t, ∫ v in u..t, F v u := by
  have hswap := triangular_integral_swap (F := fun u v => F v u)
    (hF.comp continuous_swap) ht (le_refl t)
  calc
    (∫ v in (0 : ℝ)..t, ∫ u in (0 : ℝ)..v, F v u) =
        ∫ v in (0 : ℝ)..t, ∫ u in (0 : ℝ)..min v t, F v u := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le ht] at hv
      dsimp only
      rw [min_eq_left hv.2]
    _ = ∫ u in (0 : ℝ)..t, ∫ v in u..t, F v u := hswap.symm

end SphericalAging.TriangleUniqueness
