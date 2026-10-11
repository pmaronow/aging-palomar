module

public import SphericalAging.CKSpecification
public import SphericalAging.TriangleUniqueness

public section

/-!
# Uniqueness of the nonlinear hard-spherical CK equations

The comparison below controls the multipliers through their actual nonlinear
memory formula. No agreement of the multipliers, no agreement of earlier rows,
and no existence of a physical solution are presumed.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace SphericalAging.CKWellposedness
open CKSpecification TriangleUniqueness

@[expose] def symmetricCorrelation (d : CKData) (t s : ℝ) : ℝ :=
  d.C (max 0 t) (max 0 s)

@[expose] def symmetricResponse (d : CKData) (t s : ℝ) : ℝ :=
  d.R (max (max 0 t) (max 0 s)) (min (max 0 t) (max 0 s))

theorem symmetricCorrelation_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (symmetricCorrelation d)) :=
  h.correlation_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ => (max 0 z.1,max 0 z.2)) by fun_prop)
    (fun z => ⟨le_max_left 0 z.1,le_max_left 0 z.2⟩)

theorem symmetricResponse_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (symmetricResponse d)) :=
  h.response_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ =>
      (max (max 0 z.1) (max 0 z.2), min (max 0 z.1) (max 0 z.2))) by fun_prop)
    (fun z => ⟨le_min (le_max_left 0 z.1) (le_max_left 0 z.2),min_le_max⟩)

theorem symmetricCorrelation_eq {d : CKData} {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    symmetricCorrelation d t s = d.C t s := by
  simp [symmetricCorrelation,max_eq_right ht,max_eq_right hs]

theorem symmetricResponse_eq {d : CKData} {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    symmetricResponse d t s = d.R t s := by
  simp [symmetricResponse,max_eq_right (hs.trans hst),max_eq_right hs,
    max_eq_left hst,min_eq_right hst]

theorem symmetricResponse_symmetric (d : CKData) (t s : ℝ) :
    symmetricResponse d t s = symmetricResponse d s t := by
  simp only [symmetricResponse,max_comm,min_comm]

@[expose] def comparisonSize (d e : CKData) (t s : ℝ) : ℝ :=
  max |symmetricCorrelation d t s - symmetricCorrelation e t s|
    |symmetricResponse d t s - symmetricResponse e t s|

@[expose] def comparisonNorm (d e : CKData) (t : ℝ) : ℝ := runningNorm (comparisonSize d e) t

theorem comparisonSize_continuous {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) :
    Continuous (Function.uncurry (comparisonSize d e)) :=
  ((symmetricCorrelation_continuous hd).sub (symmetricCorrelation_continuous he)).abs.max
    (((symmetricResponse_continuous hd).sub (symmetricResponse_continuous he)).abs)

theorem comparisonSize_nonneg (d e : CKData) (t s : ℝ) : 0 ≤ comparisonSize d e t s :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem comparisonNorm_continuous {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) : Continuous (comparisonNorm d e) :=
  runningNorm_continuous (comparisonSize_continuous hd he)

theorem comparisonNorm_nonneg {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ comparisonNorm d e t := runningNorm_nonneg (comparisonSize_continuous hd he) ht

theorem correlation_difference_le {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
    |d.C u v - e.C u v| ≤ comparisonNorm d e t := by
  have hh := runningNorm_dominate (comparisonSize_continuous hd he) ht hu hv
  rw [abs_of_nonneg (comparisonSize_nonneg d e u v)] at hh
  have hleft := (le_max_left _ _).trans hh
  simpa only [comparisonNorm,comparisonSize,symmetricCorrelation,max_eq_right hu.1,max_eq_right hv.1]
    using hleft

theorem response_difference_le {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 u) :
    |d.R u v - e.R u v| ≤ comparisonNorm d e t := by
  have hh := runningNorm_dominate (comparisonSize_continuous hd he) ht hu
    (show v ∈ Icc 0 t from ⟨hv.1,hv.2.trans hu.2⟩)
  rw [abs_of_nonneg (comparisonSize_nonneg d e u v)] at hh
  have hright := (le_max_right _ _).trans hh
  simpa only [comparisonNorm,comparisonSize,symmetricResponse,max_eq_right hu.1,max_eq_right hv.1,
    max_eq_left hv.2,min_eq_right hv.2] using hright

@[expose] def powerLip (M : ℝ) (n : ℕ) : ℝ := (n : ℝ) * M ^ (n - 1)
@[expose] def pairLip (M : ℝ) (n : ℕ) : ℝ := powerLip M n * M + M ^ n
@[expose] def tripleLip (M : ℝ) (n : ℕ) : ℝ := powerLip M n * M ^ 2 + 2 * M ^ (n + 1)

theorem powerLip_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : 0 ≤ powerLip M n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)

theorem pairLip_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : 0 ≤ pairLip M n :=
  add_nonneg (mul_nonneg (powerLip_nonneg hM n) hM) (pow_nonneg hM n)

theorem tripleLip_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : 0 ≤ tripleLip M n :=
  add_nonneg (mul_nonneg (powerLip_nonneg hM n) (sq_nonneg M))
    (mul_nonneg (by norm_num) (pow_nonneg hM _))

theorem power_difference_le {M δ a b : ℝ} (_hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hab : |a-b| ≤ δ) (n : ℕ) :
    |a ^ n - b ^ n| ≤ powerLip M n * δ := by
  have h := abs_pow_sub_pow_le (a := a) (b := b) (n := n)
  calc
    |a ^ n - b ^ n| ≤ |a-b| * n * max |a| |b| ^ (n-1) := h
    _ ≤ δ * n * M ^ (n-1) := by gcongr; exact max_le ha hb
    _ = powerLip M n * δ := by unfold powerLip; ring

theorem power_product_difference_le {M δ a b c d : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) (_hd : |d| ≤ M)
    (hab : |a-b| ≤ δ) (hcd : |c-d| ≤ δ) (n : ℕ) :
    |a ^ n * c - b ^ n * d| ≤ pairLip M n * δ := by
  have hpow := power_difference_le hM hδ ha hb hab n
  have hbpow : |b ^ n| ≤ M ^ n := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hb n
  have heq : a ^ n * c - b ^ n * d = (a ^ n-b ^ n)*c + b ^ n*(c-d) := by ring
  rw [heq]
  calc
    |(a ^ n-b ^ n)*c+b ^ n*(c-d)| ≤ |(a ^ n-b ^ n)*c|+|b ^ n*(c-d)| := abs_add_le _ _
    _ ≤ (powerLip M n*δ)*M+M ^ n*δ := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hpow hc (abs_nonneg _) (mul_nonneg (powerLip_nonneg hM n) hδ))
        (mul_le_mul hbpow hcd (abs_nonneg _) (pow_nonneg hM n))
    _ = pairLip M n*δ := by unfold pairLip; ring

theorem power_triple_difference_le {M δ a b c d e f : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) (hd : |d| ≤ M)
    (he : |e| ≤ M) (_hf : |f| ≤ M)
    (hab : |a-b| ≤ δ) (hcd : |c-d| ≤ δ) (hef : |e-f| ≤ δ) (n : ℕ) :
    |a ^ n*c*e-b ^ n*d*f| ≤ tripleLip M n*δ := by
  have hpair := power_product_difference_le hM hδ ha hb hc hd hab hcd n
  have hbpow : |b ^ n| ≤ M ^ n := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hb n
  have heq : a ^ n*c*e-b ^ n*d*f = (a ^ n*c-b ^ n*d)*e+b ^ n*d*(e-f) := by ring
  rw [heq]
  calc
    |(a ^ n*c-b ^ n*d)*e+b ^ n*d*(e-f)| ≤
        |(a ^ n*c-b ^ n*d)*e|+|b ^ n*d*(e-f)| := abs_add_le _ _
    _ ≤ (pairLip M n*δ)*M+(M ^ n*M)*δ := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hpair he (abs_nonneg _) (mul_nonneg (pairLip_nonneg hM n) hδ))
        (mul_le_mul (mul_le_mul hbpow hd (abs_nonneg _) (pow_nonneg hM n)) hef
          (abs_nonneg _) (mul_nonneg (pow_nonneg hM n) hM))
    _ = tripleLip M n*δ := by unfold tripleLip pairLip; rw [pow_succ]; ring

@[expose] def solutionMagnitude (d : CKData) (t s : ℝ) : ℝ :=
  max |symmetricCorrelation d t s|
    (max |symmetricResponse d t s| |d.multiplier (max 0 t)|)

theorem solutionMagnitude_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (solutionMagnitude d)) := by
  have hLambda : Continuous (fun z : ℝ × ℝ => d.multiplier (max 0 z.1)) :=
    h.multiplier_continuous.comp_continuous
      (show Continuous (fun z : ℝ × ℝ => max 0 z.1) by fun_prop)
      (fun z => le_max_left 0 z.1)
  exact (symmetricCorrelation_continuous h).abs.max
    ((symmetricResponse_continuous h).abs.max hLambda.abs)

structure CompactBounds (d e : CKData) (T M : ℝ) : Prop where
  one_le : 1 ≤ M
  correlation_d : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, |d.C t s| ≤ M
  correlation_e : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, |e.C t s| ≤ M
  response_d : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, |d.R t s| ≤ M
  response_e : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, |e.R t s| ≤ M
  multiplier_d : ∀ t ∈ Icc 0 T, |d.multiplier t| ≤ M
  multiplier_e : ∀ t ∈ Icc 0 T, |e.multiplier t| ≤ M

theorem compact_bounds_exist {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T : ℝ} (hT : 0 ≤ T) :
    ∃ M, CompactBounds d e T M := by
  let f : ℝ × ℝ → ℝ := fun z => max 1 (max (solutionMagnitude d z.1 z.2)
    (solutionMagnitude e z.1 z.2))
  have hf : Continuous f := continuous_const.max
    ((solutionMagnitude_continuous hd).max (solutionMagnitude_continuous he))
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hf.continuousOn
  have hp (t s : ℝ) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) : f (t,s) ≤ M :=
    hM ⟨(t,s),⟨ht,hs⟩,rfl⟩
  have hdmag (t s : ℝ) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
      solutionMagnitude d t s ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hp t s ht hs))
  have hemag (t s : ℝ) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
      solutionMagnitude e t s ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hp t s ht hs))
  refine ⟨M,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (le_max_left _ _).trans (hp 0 0 ⟨le_refl 0,hT⟩ ⟨le_refl 0,hT⟩)
  · intro t ht s hs
    have hh := (le_max_left _ _).trans (hdmag t s ht hs)
    simpa only [solutionMagnitude,symmetricCorrelation,max_eq_right ht.1,
      max_eq_right hs.1] using hh
  · intro t ht s hs
    have hh := (le_max_left _ _).trans (hemag t s ht hs)
    simpa only [solutionMagnitude,symmetricCorrelation,max_eq_right ht.1,
      max_eq_right hs.1] using hh
  · intro t ht s hs
    have hh := (le_max_left _ _).trans ((le_max_right _ _).trans
      (hdmag t s ht ⟨hs.1,hs.2.trans ht.2⟩))
    simpa only [solutionMagnitude,symmetricResponse,max_eq_right ht.1,
      max_eq_right hs.1,max_eq_left hs.2,min_eq_right hs.2] using hh
  · intro t ht s hs
    have hh := (le_max_left _ _).trans ((le_max_right _ _).trans
      (hemag t s ht ⟨hs.1,hs.2.trans ht.2⟩))
    simpa only [solutionMagnitude,symmetricResponse,max_eq_right ht.1,
      max_eq_right hs.1,max_eq_left hs.2,min_eq_right hs.2] using hh
  · intro t ht
    have hh := (le_max_right _ _).trans ((le_max_right _ _).trans
      (hdmag t 0 ht ⟨le_refl 0,hT⟩))
    simpa only [solutionMagnitude,max_eq_right ht.1] using hh
  · intro t ht
    have hh := (le_max_right _ _).trans ((le_max_right _ _).trans
      (hemag t 0 ht ⟨le_refl 0,hT⟩))
    simpa only [solutionMagnitude,max_eq_right ht.1] using hh

theorem interval_integral_difference_le {f g : ℝ → ℝ} {a b A : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ u ∈ Icc a b, |f u-g u| ≤ A) :
    |(∫ u in a..b, f u)-(∫ u in a..b, g u)| ≤ (b-a)*A := by
  rw [← intervalIntegral.integral_sub hf hg]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u => f u-g u) (a := a) (b := b) (C := A)
    (fun u (hu : u ∈ uIoc a b) => by
      rw [uIoc_of_le hab] at hu
      simpa only [Real.norm_eq_abs] using hbound u ⟨hu.1.le,hu.2⟩)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hh

theorem zero_diagonal_row_bound {F : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {T B : ℝ}
    (hF : Continuous (Function.uncurry F)) (hw : Continuous w)
    (hwn : ∀ u, 0 ≤ u → 0 ≤ w u) (hB : 0 ≤ B)
    (hzero : ∀ s ∈ Icc 0 T, F s s = 0)
    (hderiv : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, s < t →
      DifferentiableAt ℝ (fun x => F x s) t)
    (hbound : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, s < t →
      ‖deriv (fun x => F x s) t‖ ≤ B*w t)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
    |F t s| ≤ B*(∫ u in (0 : ℝ)..t, w u) := by
  have hi := norm_sub_le_integral_of_norm_deriv_le_of_le (f := fun x => F x s) hs.2
    ((hF.comp (continuous_id.prodMk continuous_const)).continuousOn)
    (fun x hx => (hderiv x ⟨hs.1.trans hx.1.le,hx.2.le.trans ht.2⟩
      s ⟨hs.1,hx.1.le⟩ hx.1).differentiableWithinAt)
    (ae_of_all _ (fun x hx => hbound x ⟨hs.1.trans hx.1.le,hx.2.le.trans ht.2⟩
      s ⟨hs.1,hx.1.le⟩ hx.1))
    ((hw.const_mul B).intervalIntegrable s t)
  have hrow : |F t s| ≤ B*∫ u in s..t, w u := by
    simpa only [hzero s ⟨hs.1,hs.2.trans ht.2⟩,sub_zero,Real.norm_eq_abs,
      intervalIntegral.integral_const_mul] using hi
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) 0 s) (hw.intervalIntegrable s t)
  have hn : 0 ≤ ∫ u in (0 : ℝ)..s, w u :=
    intervalIntegral.integral_nonneg hs.1 (fun u hu => hwn u hu.1)
  have hh : (∫ u in s..t, w u) ≤ ∫ u in (0 : ℝ)..t, w u := by linarith
  exact hrow.trans (mul_le_mul_of_nonneg_left hh hB)

theorem correlation_difference_hasDerivAt {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s < t) :
    HasDerivAt (fun x => symmetricCorrelation d x s-symmetricCorrelation e x s)
      (correlationSlope p β d t s-correlationSlope p β e t s) t := by
  have hh := (hd.correlation_derivative t s hs hst.le).sub
    (he.correlation_derivative t s hs hst.le)
  have hc := hh.congr (f₁ := fun x => symmetricCorrelation d x s-symmetricCorrelation e x s)
    (fun x (hx : x ∈ Ici s) => by
      rw [symmetricCorrelation_eq (hs.trans hx) hs,symmetricCorrelation_eq (hs.trans hx) hs]
      rfl)
    (by
      rw [symmetricCorrelation_eq (hs.trans hst.le) hs,
        symmetricCorrelation_eq (hs.trans hst.le) hs]
      rfl)
  exact hc.hasDerivAt (Ici_mem_nhds hst)

theorem response_difference_hasDerivAt {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s < t) :
    HasDerivAt (fun x => symmetricResponse d x s-symmetricResponse e x s)
      (responseSlope p β d t s-responseSlope p β e t s) t := by
  have hh := (hd.response_derivative t s hs hst.le).sub
    (he.response_derivative t s hs hst.le)
  have hc := hh.congr (f₁ := fun x => symmetricResponse d x s-symmetricResponse e x s)
    (fun x (hx : x ∈ Ici s) => by
      rw [symmetricResponse_eq hs hx,symmetricResponse_eq hs hx]
      rfl)
    (by rw [symmetricResponse_eq hs hst.le,symmetricResponse_eq hs hst.le]
        rfl)
  exact hc.hasDerivAt (Ici_mem_nhds hst)

/-- A coupled Gronwall comparison. The bounds on the actual CK slopes will
be supplied by the polynomial and multiplier estimates below. -/
theorem domain_equivalent_on_compact_of_slope_bounds {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hC : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t,
      |correlationSlope p β d t s-correlationSlope p β e t s| ≤ B*comparisonNorm d e t)
    (hR : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t,
      |responseSlope p β d t s-responseSlope p β e t s| ≤ B*comparisonNorm d e t) :
    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s=e.C t s) ∧
    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, d.R t s=e.R t s) := by
  let FC : ℝ → ℝ → ℝ := fun t s => symmetricCorrelation d t s-symmetricCorrelation e t s
  let FR : ℝ → ℝ → ℝ := fun t s => symmetricResponse d t s-symmetricResponse e t s
  have hc : Continuous (Function.uncurry FC) :=
    (symmetricCorrelation_continuous hd).sub (symmetricCorrelation_continuous he)
  have hr : Continuous (Function.uncurry FR) :=
    (symmetricResponse_continuous hd).sub (symmetricResponse_continuous he)
  have hc0 (s : ℝ) (hs : s ∈ Icc 0 T) : FC s s=0 := by
    simp only [FC,symmetricCorrelation_eq hs.1 hs.1,hd.correlation_diagonal s hs.1,
      he.correlation_diagonal s hs.1,sub_self]
  have hr0 (s : ℝ) (hs : s ∈ Icc 0 T) : FR s s=0 := by
    simp only [FR,symmetricResponse_eq hs.1 (le_refl s),hd.response_diagonal s hs.1,
      he.response_diagonal s hs.1,sub_self]
  have hbC {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |FC t s| ≤ B*∫ u in (0 : ℝ)..t, comparisonNorm d e u :=
    zero_diagonal_row_bound hc (comparisonNorm_continuous hd he)
      (fun u hu => comparisonNorm_nonneg hd he hu) hB hc0
      (fun t _ s hs hst => (correlation_difference_hasDerivAt hd he hs.1 hst).differentiableAt)
      (fun t ht s hs hst => by
        rw [(correlation_difference_hasDerivAt hd he hs.1 hst).deriv,Real.norm_eq_abs]
        exact hC t ht s hs) ht hs
  have hbR {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |FR t s| ≤ B*∫ u in (0 : ℝ)..t, comparisonNorm d e u :=
    zero_diagonal_row_bound hr (comparisonNorm_continuous hd he)
      (fun u hu => comparisonNorm_nonneg hd he hu) hB hr0
      (fun t _ s hs hst => (response_difference_hasDerivAt hd he hs.1 hst).differentiableAt)
      (fun t ht s hs hst => by
        rw [(response_difference_hasDerivAt hd he hs.1 hst).deriv,Real.norm_eq_abs]
        exact hR t ht s hs) ht hs
  have hsC (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) : FC t s=FC s t := by
    dsimp [FC]
    rw [symmetricCorrelation_eq ht hs,symmetricCorrelation_eq ht hs,
      symmetricCorrelation_eq hs ht,symmetricCorrelation_eq hs ht,
      hd.correlation_symmetric t s ht hs,he.correlation_symmetric t s ht hs]
  have hsR (t s : ℝ) : FR t s=FR s t := by
    simp only [FR,symmetricResponse_symmetric d t s,symmetricResponse_symmetric e t s]
  have hpair {t : ℝ} (ht : t ∈ Icc 0 T) {u v : ℝ}
      (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
      comparisonSize d e u v ≤ B*∫ x in (0 : ℝ)..t, comparisonNorm d e x := by
    have hw := comparisonNorm_continuous hd he
    have hinc {r : ℝ} (hr : r ∈ Icc 0 t) :
        B*(∫ x in (0 : ℝ)..r, comparisonNorm d e x) ≤
          B*∫ x in (0 : ℝ)..t, comparisonNorm d e x := by
      apply mul_le_mul_of_nonneg_left _ hB
      have hspl := intervalIntegral.integral_add_adjacent_intervals
        (hw.intervalIntegrable (μ := volume) 0 r) (hw.intervalIntegrable r t)
      have hn := intervalIntegral.integral_nonneg (μ := volume) hr.2
        (fun x hx => comparisonNorm_nonneg hd he (hr.1.trans hx.1))
      linarith
    change max |FC u v| |FR u v| ≤ _
    by_cases huv : v ≤ u
    · exact max_le ((hbC ⟨hu.1,hu.2.trans ht.2⟩ ⟨hv.1,huv⟩).trans (hinc hu))
        ((hbR ⟨hu.1,hu.2.trans ht.2⟩ ⟨hv.1,huv⟩).trans (hinc hu))
    · have huv' : u ≤ v := le_of_not_ge huv
      rw [hsC u v hu.1 hv.1,hsR u v]
      exact max_le ((hbC ⟨hv.1,hv.2.trans ht.2⟩ ⟨hu.1,huv'⟩).trans (hinc hv))
        ((hbR ⟨hv.1,hv.2.trans ht.2⟩ ⟨hu.1,huv'⟩).trans (hinc hv))
  have hnorm (t : ℝ) (ht : t ∈ Icc 0 T) :
      comparisonNorm d e t ≤ B*∫ x in (0 : ℝ)..t, comparisonNorm d e x := by
    apply csSup_le (unitSquare_nonempty.image _)
    rintro _ ⟨z,hz,rfl⟩
    dsimp only
    rw [abs_of_nonneg (comparisonSize_nonneg d e _ _)]
    exact hpair ht ⟨mul_nonneg ht.1 hz.1.1,
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.1.2 ht.1⟩
      ⟨mul_nonneg ht.1 hz.2.1,
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2.2 ht.1⟩
  have hzero := continuous_integral_bound_eq_zero hT (comparisonNorm_continuous hd he)
    (fun t ht => comparisonNorm_nonneg hd he ht.1) hnorm
  constructor
  · intro t ht s hs
    have hh := correlation_difference_le hd he hT ht hs
    rw [hzero T ⟨hT,le_refl T⟩] at hh
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  · intro t ht s hs
    have hh := response_difference_le hd he hT ht hs
    rw [hzero T ⟨hT,le_refl T⟩] at hh
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

@[expose] def responseMemory (n : ℕ) (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in s..t, d.C t u ^ n*d.R t u*d.R u s

@[expose] def correlationMemory (n : ℕ) (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, d.C t u ^ n*d.R t u*d.C u s

@[expose] def forcingMemory (n : ℕ) (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, d.C t u ^ n*d.R s u

theorem power_response_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (n : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) :
    IntervalIntegrable (fun u => d.C t u ^ n*d.R t u) volume a t := by
  have hc : Continuous (fun u => symmetricCorrelation d t u) :=
    (symmetricCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)
  have hr : Continuous (fun u => symmetricResponse d t u) :=
    (symmetricResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  apply (((hc.pow n).mul hr).intervalIntegrable a t).congr
  intro u hu
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [uIoc_of_le hat] at hu
  rw [symmetricCorrelation_eq (ha.trans hat) (ha.trans hu.1.le),
    symmetricResponse_eq (ha.trans hu.1.le) hu.2]

theorem response_memory_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (n : ℕ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    IntervalIntegrable (fun u => d.C t u ^ n*d.R t u*d.R u s) volume s t := by
  have hc : Continuous (fun u => symmetricCorrelation d t u) :=
    (symmetricCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)
  have hr : Continuous (fun u => symmetricResponse d t u) :=
    (symmetricResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hy : Continuous (fun u => symmetricResponse d u s) :=
    (symmetricResponse_continuous h).comp (continuous_id.prodMk continuous_const)
  apply ((((hc.pow n).mul hr).mul hy).intervalIntegrable s t).congr
  intro u hu
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [uIoc_of_le hst] at hu
  rw [symmetricCorrelation_eq (hs.trans hst) (hs.trans hu.1.le),
    symmetricResponse_eq (hs.trans hu.1.le) hu.2,symmetricResponse_eq hs hu.1.le]

theorem correlation_memory_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (n : ℕ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => d.C t u ^ n*d.R t u*d.C u s) volume 0 t := by
  have hc : Continuous (fun u => symmetricCorrelation d t u) :=
    (symmetricCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)
  have hr : Continuous (fun u => symmetricResponse d t u) :=
    (symmetricResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hy : Continuous (fun u => symmetricCorrelation d u s) :=
    (symmetricCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
  apply ((((hc.pow n).mul hr).mul hy).intervalIntegrable 0 t).congr
  intro u hu
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [uIoc_of_le ht] at hu
  rw [symmetricCorrelation_eq ht hu.1.le,symmetricResponse_eq hu.1.le hu.2,
    symmetricCorrelation_eq hu.1.le hs]

theorem forcing_memory_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (n : ℕ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => d.C t u ^ n*d.R s u) volume 0 s := by
  have hc : Continuous (fun u => symmetricCorrelation d t u) :=
    (symmetricCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)
  have hr : Continuous (fun u => symmetricResponse d s u) :=
    (symmetricResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  apply (((hc.pow n).mul hr).intervalIntegrable 0 s).congr
  intro u hu
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [uIoc_of_le hs] at hu
  rw [symmetricCorrelation_eq ht hu.1.le,symmetricResponse_eq hu.1.le hu.2]

theorem responseSlope_normalized (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) :
    responseSlope p β d t s = -d.multiplier t*d.R t s+
      β ^ 2*((p : ℝ)*((p : ℝ)-1))*responseMemory (p-2) d t s := by
  simp only [responseSlope,responseMemory,xiDoublePrime,mul_assoc,
    intervalIntegral.integral_const_mul]

theorem correlationSlope_normalized (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) :
    correlationSlope p β d t s = -d.multiplier t*d.C t s+
      β ^ 2*((p : ℝ)*((p : ℝ)-1))*correlationMemory (p-2) d t s+
      β ^ 2*(p : ℝ)*forcingMemory (p-1) d t s := by
  simp only [correlationSlope,correlationMemory,forcingMemory,xiDoublePrime,xiPrime,
    mul_assoc,intervalIntegral.integral_const_mul]

theorem memoryMass_difference_le {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T M t : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) :
    |memoryMass p d t-memoryMass p e t| ≤
      T*pairLip M (p-1)*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le ht.1
    (power_response_integrable hd (p-1) (le_refl 0) ht.1)
    (power_response_integrable he (p-1) (le_refl 0) ht.1)
    (fun u hu => power_product_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.correlation_e t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.response_d t ht u hu) (hM.response_e t ht u hu)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu) (p-1))
  change |memoryMass p d t-memoryMass p e t| ≤ (t-0)*(pairLip M (p-1)*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [sub_zero,mul_assoc]
    exact mul_le_mul_of_nonneg_right ht.2
      (mul_nonneg (pairLip_nonneg hM0 _) hδ))

theorem multiplier_difference_le {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T M t : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) :
    |d.multiplier t-e.multiplier t| ≤
      (β ^ 2*(p : ℝ)^2*T*pairLip M (p-1))*comparisonNorm d e t := by
  rw [hd.multiplier_eq t ht.1,he.multiplier_eq t ht.1]
  have heq (a b : ℝ) : (1+β^2*(p : ℝ)^2*a)-(1+β^2*(p : ℝ)^2*b) =
      (β^2*(p : ℝ)^2)*(a-b) := by ring
  rw [heq,abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ)))]
  have hh := mul_le_mul_of_nonneg_left (memoryMass_difference_le hd he hM ht)
    (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ)))
  simpa only [mul_assoc] using hh

theorem responseMemory_difference_le {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T M t s : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |responseMemory n d t s-responseMemory n e t s| ≤
      T*tripleLip M n*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le hs.2
    (response_memory_integrable hd n hs.1 hs.2) (response_memory_integrable he n hs.1 hs.2)
    (fun u hu => power_triple_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩)
      (hM.correlation_e t ht u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩)
      (hM.response_d t ht u ⟨hs.1.trans hu.1,hu.2⟩)
      (hM.response_e t ht u ⟨hs.1.trans hu.1,hu.2⟩)
      (hM.response_d u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hu.1⟩)
      (hM.response_e u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hu.1⟩)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ ⟨hs.1.trans hu.1,hu.2⟩)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ ⟨hs.1.trans hu.1,hu.2⟩)
      (response_difference_le hd he ht.1 ⟨hs.1.trans hu.1,hu.2⟩ ⟨hs.1,hu.1⟩) n)
  change |responseMemory n d t s-responseMemory n e t s| ≤
    (t-s)*(tripleLip M n*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2,hs.1])
      (mul_nonneg (tripleLip_nonneg hM0 _) hδ))

theorem correlationMemory_difference_le {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T M t s : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |correlationMemory n d t s-correlationMemory n e t s| ≤
      T*tripleLip M n*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le ht.1
    (correlation_memory_integrable hd n hs.1 ht.1) (correlation_memory_integrable he n hs.1 ht.1)
    (fun u hu => power_triple_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.correlation_e t ht u ⟨hu.1,hu.2.trans ht.2⟩)
      (hM.response_d t ht u hu) (hM.response_e t ht u hu)
      (hM.correlation_d u ⟨hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hs.2.trans ht.2⟩)
      (hM.correlation_e u ⟨hu.1,hu.2.trans ht.2⟩ s ⟨hs.1,hs.2.trans ht.2⟩)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hu)
      (correlation_difference_le hd he ht.1 hu hs) n)
  change |correlationMemory n d t s-correlationMemory n e t s| ≤
    (t-0)*(tripleLip M n*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [sub_zero,mul_assoc]
    exact mul_le_mul_of_nonneg_right ht.2 (mul_nonneg (tripleLip_nonneg hM0 _) hδ))

theorem forcingMemory_difference_le {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T M t s : ℝ}
    (hM : CompactBounds d e T M) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) (n : ℕ) :
    |forcingMemory n d t s-forcingMemory n e t s| ≤
      T*pairLip M n*comparisonNorm d e t := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hδ := comparisonNorm_nonneg hd he ht.1
  have hi := interval_integral_difference_le hs.1
    (forcing_memory_integrable hd n hs.1 ht.1) (forcing_memory_integrable he n hs.1 ht.1)
    (fun u hu => power_product_difference_le hM0 hδ
      (hM.correlation_d t ht u ⟨hu.1,hu.2.trans (hs.2.trans ht.2)⟩)
      (hM.correlation_e t ht u ⟨hu.1,hu.2.trans (hs.2.trans ht.2)⟩)
      (hM.response_d s ⟨hs.1,hs.2.trans ht.2⟩ u hu)
      (hM.response_e s ⟨hs.1,hs.2.trans ht.2⟩ u hu)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ ⟨hu.1,hu.2.trans hs.2⟩)
      (response_difference_le hd he ht.1 hs hu) n)
  change |forcingMemory n d t s-forcingMemory n e t s| ≤
    (s-0)*(pairLip M n*comparisonNorm d e t) at hi
  exact hi.trans (by
    rw [sub_zero,mul_assoc]
    exact mul_le_mul_of_nonneg_right (hs.2.trans ht.2) (mul_nonneg (pairLip_nonneg hM0 _) hδ))

theorem damping_difference_le {M L δ lam mu a b : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hlam : |lam| ≤ M) (hb : |b| ≤ M)
    (hab : |a-b| ≤ δ) (hlammu : |lam-mu| ≤ L*δ) :
    |(-lam*a)-(-mu*b)| ≤ (M+L*M)*δ := by
  have heq : (-lam*a)-(-mu*b) = -lam*(a-b)-(lam-mu)*b := by ring
  rw [heq]
  calc
    |-lam*(a-b)-(lam-mu)*b| ≤ |-lam*(a-b)|+|(lam-mu)*b| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (-lam*(a-b)) ((lam-mu)*b)
    _ ≤ M*δ+(L*δ)*M := by
      simp only [abs_mul,abs_neg]
      exact add_le_add (mul_le_mul hlam hab (abs_nonneg _) hM)
        (mul_le_mul hlammu hb (abs_nonneg _) (mul_nonneg hL hδ))
    _ = (M+L*M)*δ := by ring

theorem slope_difference_bounds {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) {T : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t,
        |correlationSlope p β d t s-correlationSlope p β e t s| ≤ B*comparisonNorm d e t) ∧
      (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t,
        |responseSlope p β d t s-responseSlope p β e t s| ≤ B*comparisonNorm d e t) := by
  obtain ⟨M,hM⟩ := compact_bounds_exist hd he hT
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM.one_le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hp1 : (1 : ℝ) ≤ p := by
    have hp := hd.spin_ge_three
    exact_mod_cast (show 1 ≤ p by omega)
  let L : ℝ := β ^ 2*(p : ℝ)^2*T*pairLip M (p-1)
  let A : ℝ := M+L*M
  let c : ℝ := β ^ 2*((p : ℝ)*((p : ℝ)-1))
  let k : ℝ := β ^ 2*(p : ℝ)
  let U : ℝ := c*T*tripleLip M (p-2)
  let V : ℝ := k*T*pairLip M (p-1)
  let B : ℝ := A+U+V
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg
    (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ))) hT) (pairLip_nonneg hM0 _)
  have hA : 0 ≤ A := add_nonneg hM0 (mul_nonneg hL hM0)
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg β) (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  have hk : 0 ≤ k := mul_nonneg (sq_nonneg β) hp0
  have hU : 0 ≤ U := mul_nonneg (mul_nonneg hc hT) (tripleLip_nonneg hM0 _)
  have hV : 0 ≤ V := mul_nonneg (mul_nonneg hk hT) (pairLip_nonneg hM0 _)
  have hdampC {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |(-d.multiplier t*d.C t s)-(-e.multiplier t*e.C t s)| ≤ A*comparisonNorm d e t :=
    damping_difference_le hM0 hL (comparisonNorm_nonneg hd he ht.1)
      (hM.multiplier_d t ht) (hM.correlation_e t ht s ⟨hs.1,hs.2.trans ht.2⟩)
      (correlation_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hs)
      (multiplier_difference_le hd he hM ht)
  have hdampR {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |(-d.multiplier t*d.R t s)-(-e.multiplier t*e.R t s)| ≤ A*comparisonNorm d e t :=
    damping_difference_le hM0 hL (comparisonNorm_nonneg hd he ht.1)
      (hM.multiplier_d t ht) (hM.response_e t ht s hs)
      (response_difference_le hd he ht.1 ⟨ht.1,le_refl t⟩ hs)
      (multiplier_difference_le hd he hM ht)
  have hmemC {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |c*(correlationMemory (p-2) d t s-correlationMemory (p-2) e t s)| ≤
        U*comparisonNorm d e t := by
    rw [abs_mul,abs_of_nonneg hc]
    have hh := mul_le_mul_of_nonneg_left (correlationMemory_difference_le hd he hM ht hs (p-2)) hc
    simpa only [U,mul_assoc] using hh
  have hmemR {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |c*(responseMemory (p-2) d t s-responseMemory (p-2) e t s)| ≤
        U*comparisonNorm d e t := by
    rw [abs_mul,abs_of_nonneg hc]
    have hh := mul_le_mul_of_nonneg_left (responseMemory_difference_le hd he hM ht hs (p-2)) hc
    simpa only [U,mul_assoc] using hh
  have hforce {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
      |k*(forcingMemory (p-1) d t s-forcingMemory (p-1) e t s)| ≤
        V*comparisonNorm d e t := by
    rw [abs_mul,abs_of_nonneg hk]
    have hh := mul_le_mul_of_nonneg_left (forcingMemory_difference_le hd he hM ht hs (p-1)) hk
    simpa only [V,mul_assoc] using hh
  refine ⟨B,add_nonneg (add_nonneg hA hU) hV,?_,?_⟩
  · intro t ht s hs
    have heq : correlationSlope p β d t s-correlationSlope p β e t s =
        ((-d.multiplier t*d.C t s)-(-e.multiplier t*e.C t s))+
        c*(correlationMemory (p-2) d t s-correlationMemory (p-2) e t s)+
        k*(forcingMemory (p-1) d t s-forcingMemory (p-1) e t s) := by
      rw [correlationSlope_normalized,correlationSlope_normalized]
      dsimp only [c,k]
      ring
    rw [heq]
    calc
      _ ≤ |(-d.multiplier t*d.C t s)-(-e.multiplier t*e.C t s)|+
          |c*(correlationMemory (p-2) d t s-correlationMemory (p-2) e t s)|+
          |k*(forcingMemory (p-1) d t s-forcingMemory (p-1) e t s)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ A*comparisonNorm d e t+U*comparisonNorm d e t+V*comparisonNorm d e t :=
        add_le_add (add_le_add (hdampC ht hs) (hmemC ht hs)) (hforce ht hs)
      _ = B*comparisonNorm d e t := by dsimp only [B]; ring
  · intro t ht s hs
    have heq : responseSlope p β d t s-responseSlope p β e t s =
        ((-d.multiplier t*d.R t s)-(-e.multiplier t*e.R t s))+
        c*(responseMemory (p-2) d t s-responseMemory (p-2) e t s) := by
      rw [responseSlope_normalized,responseSlope_normalized]
      dsimp only [c]
      ring
    rw [heq]
    calc
      _ ≤ |(-d.multiplier t*d.R t s)-(-e.multiplier t*e.R t s)|+
          |c*(responseMemory (p-2) d t s-responseMemory (p-2) e t s)| := abs_add_le _ _
      _ ≤ A*comparisonNorm d e t+U*comparisonNorm d e t :=
        add_le_add (hdampR ht hs) (hmemR ht hs)
      _ ≤ B*comparisonNorm d e t := by
        have hh := mul_nonneg hV (comparisonNorm_nonneg hd he ht.1)
        dsimp only [B]
        nlinarith only [hh]

/-- The uniqueness assertion of Proposition 3.2, for the exact nonlinear CK
system. Only the two systems of equations are hypotheses. -/
theorem ck_equations_unique {p : ℕ} {β : ℝ} {d e : CKData}
    (hd : CKEquations p β d) (he : CKEquations p β e) : DomainEquivalent d e := by
  have hcompact (T : ℝ) (hT : 0 ≤ T) :
      (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s=e.C t s) ∧
      (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, d.R t s=e.R t s) := by
    obtain ⟨B,hB,hC,hR⟩ := slope_difference_bounds hd he hT
    exact domain_equivalent_on_compact_of_slope_bounds hd he hT hB hC hR
  have hC (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) : d.C t s=e.C t s :=
    (hcompact (max t s) (ht.trans (le_max_left _ _))).1 t ⟨ht,le_max_left _ _⟩
      s ⟨hs,le_max_right _ _⟩
  have hR (t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) : d.R t s=e.R t s :=
    (hcompact t (hs.trans hst)).2 t ⟨hs.trans hst,le_refl t⟩ s ⟨hs,hst⟩
  refine ⟨hC,hR,?_⟩
  intro t ht
  have hmem : memoryMass p d t=memoryMass p e t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only [memoryMass]
    rw [hC t u ht hu.1,hR t u hu.1 hu.2]
  rw [hd.multiplier_eq t ht,he.multiplier_eq t ht,hmem]

end SphericalAging.CKWellposedness
