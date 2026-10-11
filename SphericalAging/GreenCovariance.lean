module

public import SphericalAging.CKSpecification
public import SphericalAging.VolterraUniqueness
public import SphericalAging.TriangleUniqueness
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

public section

/-!
# Green covariance calculations from the CK equations

The off-domain extensions below only make continuous functions on all of `ℝ`.
On the physical time domains they equal the supplied CK data. No Green identity
or vanishing covariance error is assumed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SphericalAging.GreenCovariance
open CKSpecification

/-- Continuous extension of the causal response; the first coordinate is
clamped to remain later than the nonnegative second coordinate. -/
@[expose] def clampedResponse (d : CKData) (t u : ℝ) : ℝ :=
  d.R (max t (max 0 u)) (max 0 u)

@[expose] def clampedCorrelation (d : CKData) (t s : ℝ) : ℝ :=
  d.C (max 0 t) (max 0 s)

@[expose] def clampedResponseSlope (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  responseSlope p β d (max t (max 0 u)) (max 0 u)

theorem clampedResponse_eq {d : CKData} {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    clampedResponse d t u = d.R t u := by
  simp [clampedResponse, max_eq_right hu, max_eq_left hut]

theorem clampedCorrelation_eq {d : CKData} {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    clampedCorrelation d t s = d.C t s := by
  simp [clampedCorrelation, max_eq_right ht, max_eq_right hs]

theorem clampedResponse_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (clampedResponse d)) := by
  exact h.response_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ => (max z.1 (max 0 z.2), max 0 z.2)) by fun_prop)
    (fun z => ⟨le_max_left 0 z.2, le_max_right z.1 (max 0 z.2)⟩)

theorem clampedCorrelation_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (clampedCorrelation d)) := by
  exact h.correlation_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ => (max 0 z.1, max 0 z.2)) by fun_prop)
    (fun z => ⟨le_max_left 0 z.1, le_max_left 0 z.2⟩)

theorem clampedResponseSlope_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    Continuous (Function.uncurry (clampedResponseSlope p β d)) := by
  exact h.response_slope_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ => (max z.1 (max 0 z.2), max 0 z.2)) by fun_prop)
    (fun z => ⟨le_max_left 0 z.2, le_max_right z.1 (max 0 z.2)⟩)

theorem response_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t u : ℝ} (hu : 0 ≤ u) (hut : u < t) :
    HasDerivAt (fun x => d.R x u) (responseSlope p β d t u) t :=
  (h.response_derivative t u hu hut.le).hasDerivAt (Ici_mem_nhds hut)

theorem clampedResponse_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t u : ℝ} (hu : 0 ≤ u) (hut : u < t) :
    HasDerivAt (fun x => clampedResponse d x u)
      (clampedResponseSlope p β d t u) t := by
  have hd := response_hasDerivAt h hu hut
  have he : (fun x => clampedResponse d x u) =ᶠ[𝓝 t] (fun x => d.R x u) := by
    filter_upwards [Ioi_mem_nhds hut] with x hx
    exact clampedResponse_eq hu hx.le
  simpa [clampedResponseSlope, max_eq_right hu, max_eq_left hut.le] using
    hd.congr_of_eventuallyEq he

/-- Fixed-domain Leibniz rule, with its domination supplied by compactness
of the jointly continuous derivative on a closed rectangle. -/
theorem hasDerivAt_intervalIntegral_of_continuous
    {F G : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) {a b l r x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Ioo l r)
    (hd : ∀ y ∈ Ioo l r, ∀ u ∈ Icc a b,
      HasDerivAt (fun z => F z u) (G y u) y) :
    HasDerivAt (fun y => ∫ u in a..b, F y u) (∫ u in a..b, G x u) x := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    hG.norm.continuousOn
  have hM' : ∀ y ∈ Icc l r, ∀ u ∈ Icc a b, ‖G y u‖ ≤ M := by
    intro y hy u hu
    exact hM ⟨(y,u), ⟨hy,hu⟩, rfl⟩
  have hrow (y : ℝ) : Continuous (F y) := hF.comp (continuous_const.prodMk continuous_id)
  have hgrow (y : ℝ) : Continuous (G y) := hG.comp (continuous_const.prodMk continuous_id)
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a b)) (F := F) (F' := G) (bound := fun _ => M)
    (Ioo_mem_nhds hx.1 hx.2)
    (Filter.Eventually.of_forall fun y => (hrow y).aestronglyMeasurable)
    ((hrow x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hgrow x).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun u hu y hy =>
      hM' y (Ioo_subset_Icc_self hy) u (Ioc_subset_Icc_self hu))))
    (integrable_const M)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun u hu y hy =>
      hd y hy u (Ioc_subset_Icc_self hu))))
  simpa only [intervalIntegral.integral_of_le hab] using hder.2

/-- Actual differentiation of the white-noise integral at a strictly later
first argument, before substituting and rearranging the Volterra memory. -/
theorem white_integral_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..s,
      clampedResponse d x u * clampedResponse d s u)
      (∫ u in (0 : ℝ)..s,
        clampedResponseSlope p β d t u * clampedResponse d s u) t := by
  let F : ℝ → ℝ → ℝ := fun x u =>
    clampedResponse d x u * clampedResponse d s u
  let G : ℝ → ℝ → ℝ := fun x u =>
    clampedResponseSlope p β d x u * clampedResponse d s u
  have hR := clampedResponse_continuous h
  have hD := clampedResponseSlope_continuous h
  apply hasDerivAt_intervalIntegral_of_continuous (F := F) (G := G)
    (hR.mul (hR.comp (continuous_const.prodMk continuous_snd)))
    (hD.mul (hR.comp (continuous_const.prodMk continuous_snd))) hs
    (show t ∈ Ioo s (t+1) by constructor; exact hst; linarith)
  intro y hy u hu
  exact (clampedResponse_hasDerivAt h hu.1 (lt_of_le_of_lt hu.2 hy.1)).mul_const _


/-- Continuous extension of the quadratic Green candidate. -/
@[expose] def clampedGreen (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  clampedResponse d t 0 * clampedResponse d s 0 +
    2 * (∫ u in (0 : ℝ)..min t s, clampedResponse d t u * clampedResponse d s u) +
    β ^ 2 * p * (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
      clampedResponse d t u * clampedResponse d s v * clampedCorrelation d u v ^ (p - 1))

theorem clampedGreen_eq {p : ℕ} {β : ℝ} {d : CKData} {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    clampedGreen p β d t s = greenCovariance p β d t s := by
  have hwhite : (∫ u in (0 : ℝ)..min t s,
      clampedResponse d t u * clampedResponse d s u) =
      ∫ u in (0 : ℝ)..min t s, d.R t u * d.R s u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (le_min ht hs)] at hu
    dsimp
    rw [clampedResponse_eq hu.1 (hu.2.trans (min_le_left _ _)),
      clampedResponse_eq hu.1 (hu.2.trans (min_le_right _ _))]
  have hcolored : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
      clampedResponse d t u * clampedResponse d s v * clampedCorrelation d u v ^ (p-1)) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        d.R t u * d.R s v * d.C u v ^ (p-1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hs] at hv
    dsimp
    rw [clampedResponse_eq hu.1 hu.2, clampedResponse_eq hv.1 hv.2,
      clampedCorrelation_eq hu.1 hv.1]
  simp only [clampedGreen, greenCovariance, hwhite, hcolored,
    clampedResponse_eq (le_refl 0) ht, clampedResponse_eq (le_refl 0) hs]

theorem clampedGreen_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (clampedGreen p β d)) := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  have hwhite : Continuous (fun z : ℝ × ℝ =>
      ∫ u in (0 : ℝ)..min z.1 z.2, clampedResponse d z.1 u * clampedResponse d z.2 u) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (hR.comp (continuous_fst.fst.prodMk continuous_snd)).mul
        (hR.comp (continuous_fst.snd.prodMk continuous_snd))
    · fun_prop
  have hinner : Continuous (fun z : (ℝ × ℝ) × ℝ => ∫ v in (0 : ℝ)..z.1.2,
      clampedResponse d z.1.1 z.2 * clampedResponse d z.1.2 v *
        clampedCorrelation d z.2 v ^ (p - 1)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact ((hR.comp (continuous_fst.fst.fst.prodMk continuous_fst.snd)).mul
        (hR.comp (continuous_fst.fst.snd.prodMk continuous_snd))).mul
        ((hC.comp (continuous_fst.snd.prodMk continuous_snd)).pow _)
    · fun_prop
  have hcolored : Continuous (fun z : ℝ × ℝ => ∫ u in (0 : ℝ)..z.1,
      ∫ v in (0 : ℝ)..z.2, clampedResponse d z.1 u * clampedResponse d z.2 v *
        clampedCorrelation d u v ^ (p - 1)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hinner continuous_fst
  exact ((hR.comp (continuous_fst.prodMk continuous_const)).mul
    (hR.comp (continuous_snd.prodMk continuous_const))).add
    (continuous_const.mul hwhite) |>.add
    ((continuous_const.mul continuous_const).mul hcolored)

theorem greenCovariance_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    ContinuousOn (Function.uncurry (greenCovariance p β d)) timeQuadrant := by
  apply (clampedGreen_continuous h).continuousOn.congr
  intro z hz
  exact (clampedGreen_eq hz.1 hz.2).symm

/-- Rectangular Fubini for the colored covariance, established using the
actual continuous integrand rather than an assumed swap identity. -/
theorem rectangle_integral_swap {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (a b c d : ℝ) :
    (∫ u in a..b, ∫ v in c..d, F u v) = ∫ v in c..d, ∫ u in a..b, F u v := by
  apply intervalIntegral_intervalIntegral_swap
  exact (hF.continuousOn.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

theorem clampedGreen_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    clampedGreen p β d t s = clampedGreen p β d s t := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  have hswap := rectangle_integral_swap
    (F := fun u v => clampedResponse d t u * clampedResponse d s v *
      clampedCorrelation d u v ^ (p-1))
    (((hR.comp (continuous_const.prodMk continuous_fst)).mul
      (hR.comp (continuous_const.prodMk continuous_snd))).mul (hC.pow (p-1))) 0 t 0 s
  have hcolored : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
      clampedResponse d t u * clampedResponse d s v * clampedCorrelation d u v ^ (p-1)) =
      ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..t,
        clampedResponse d s u * clampedResponse d t v * clampedCorrelation d u v ^ (p-1) := by
    rw [hswap]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp
    have hsym : clampedCorrelation d v u = clampedCorrelation d u v :=
      h.correlation_symmetric _ _ (le_max_left _ _) (le_max_left _ _)
    rw [hsym]
    ring
  have hwhite : (∫ u in (0 : ℝ)..min t s,
      clampedResponse d t u * clampedResponse d s u) =
      ∫ u in (0 : ℝ)..min s t, clampedResponse d s u * clampedResponse d t u := by
    rw [min_comm t s]
    simp_rw [mul_comm]
  simp only [clampedGreen, hcolored, hwhite]
  ring

theorem greenCovariance_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    greenCovariance p β d t s = greenCovariance p β d s t := by
  rw [← clampedGreen_eq ht hs, ← clampedGreen_eq hs ht]
  exact clampedGreen_symmetric h t s

/-- Positivity of the physical Green candidate on its diagonal. This is a
property of its explicit integrals, before proving that the candidate equals C. -/
theorem greenCovariance_diagonal_lower_bound {p : ℕ} {β : ℝ} {d : CKData}
    (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    2 * (∫ u in (0 : ℝ)..t, d.R t u ^ 2) ≤ greenCovariance p β d t t := by
  have hc : 0 ≤ ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
      d.R t u * d.R t v * d.C u v ^ (p - 1) := by
    apply intervalIntegral.integral_nonneg ht
    intro u hu
    apply intervalIntegral.integral_nonneg ht
    intro v hv
    exact mul_nonneg (mul_nonneg (hb.2 t u hu.1 hu.2) (hb.2 t v hv.1 hv.2))
      (pow_nonneg (hb.1 u v hu.1 hv.1).1 _)
  have hcoef : 0 ≤ β ^ 2 * (p : ℝ) := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hi : (∫ u in (0 : ℝ)..t, d.R t u * d.R t u) =
      ∫ u in (0 : ℝ)..t, d.R t u ^ 2 := by simp only [pow_two]
  unfold greenCovariance
  rw [min_self, hi]
  nlinarith [mul_nonneg hcoef hc, sq_nonneg (d.R t 0)]


/-- Self-energy kernel with the continuous causal extension used only outside
its physical triangle. -/
@[expose] def clampedMemory (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  β ^ 2 * xiDoublePrime p (clampedCorrelation d t u) * clampedResponse d t u

theorem clampedMemory_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    Continuous (Function.uncurry (clampedMemory p β d)) := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  unfold clampedMemory xiDoublePrime
  exact (continuous_const.mul ((continuous_const.mul continuous_const).mul (hC.pow _))).mul hR

theorem clampedMemory_eq {p : ℕ} {β : ℝ} {d : CKData} {t u : ℝ}
    (hu : 0 ≤ u) (hut : u ≤ t) :
    clampedMemory p β d t u = β ^ 2 * xiDoublePrime p (d.C t u) * d.R t u := by
  unfold clampedMemory
  rw [clampedCorrelation_eq (hu.trans hut) hu, clampedResponse_eq hu hut]

/-- The initial-time identity follows directly from the two CK row equations
and genuine homogeneous Volterra uniqueness; the Green identity is not an input. -/
theorem initial_correlation_eq_response {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (hT : 0 ≤ T) : d.C T 0 = d.R T 0 := by
  let f : ℝ → ℝ := fun t => clampedCorrelation d t 0 - clampedResponse d t 0
  let f' : ℝ → ℝ := fun t => correlationSlope p β d t 0 - responseSlope p β d t 0
  let K := clampedMemory p β d
  have hf : Continuous f := ((clampedCorrelation_continuous h).comp
    (continuous_id.prodMk continuous_const)).sub ((clampedResponse_continuous h).comp
    (continuous_id.prodMk continuous_const))
  have hfeq (t : ℝ) (ht : 0 ≤ t) : f t = d.C t 0 - d.R t 0 := by
    dsimp [f]
    rw [clampedCorrelation_eq ht (le_refl 0), clampedResponse_eq (le_refl 0) ht]
  have hfzero : f 0 = 0 := by
    rw [hfeq 0 (le_refl 0), h.correlation_diagonal 0 (le_refl 0),
      h.response_diagonal 0 (le_refl 0)]
    ring
  have hKcont := clampedMemory_continuous h
  obtain ⟨L₀, hL₀⟩ := isCompact_Icc.bddAbove_image
    ((h.multiplier_continuous.mono (show Icc 0 T ⊆ Ici 0 from fun _ hx => hx.1)).norm)
  obtain ⟨S₀, hS₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image hKcont.norm.continuousOn
  have hKrow (t : ℝ) : Continuous (K t) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hderiv (t : ℝ) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt f (f' t) (Ici t) t := by
    have hd := (h.correlation_derivative t 0 (le_refl 0) ht.1).sub
      (h.response_derivative t 0 (le_refl 0) ht.1)
    exact hd.congr_mono (fun x hx => hfeq x (ht.1.trans hx))
      (hfeq t ht.1) (fun x hx => ht.1.trans hx)
  have heq (t : ℝ) (ht : t ∈ Ico 0 T) :
      f' t = -d.multiplier t * f t + ∫ u in (0 : ℝ)..t, K t u * f u := by
    have hi : (∫ u in (0 : ℝ)..t, K t u * f u) =
        β ^ 2 * ((∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u) * d.R t u * d.C u 0) -
          (∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u) * d.R t u * d.R u 0)) := by
      have hC0 : Continuous (fun u => clampedCorrelation d u 0) :=
        (clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
      have hR0 : Continuous (fun u => clampedResponse d u 0) :=
        (clampedResponse_continuous h).comp (continuous_id.prodMk continuous_const)
      have he (u : ℝ) (hu : u ∈ Icc 0 t) :
          K t u * f u = β ^ 2 *
            (xiDoublePrime p (d.C t u) * d.R t u * d.C u 0 -
              xiDoublePrime p (d.C t u) * d.R t u * d.R u 0) := by
        dsimp [K]
        rw [clampedMemory_eq hu.1 hu.2, hfeq u hu.1]
        ring
      have hiC : IntervalIntegrable (fun u => xiDoublePrime p (d.C t u) * d.R t u * d.C u 0)
          volume 0 t := by
        have hx := ((hKrow t).mul hC0).intervalIntegrable (μ := volume) 0 t
        have hb : β ^ 2 ≠ 0 := pow_ne_zero _ h.beta_pos.ne'
        have hv := hx.const_mul (β ^ 2)⁻¹
        apply hv.congr
        intro u hu
        rw [uIoc_of_le ht.1] at hu
        have hu0 : 0 ≤ u := hu.1.le
        dsimp [K]
        rw [clampedMemory_eq hu0 hu.2, clampedCorrelation_eq hu0 (le_refl 0)]
        field_simp [h.beta_pos.ne']
      have hiR : IntervalIntegrable (fun u => xiDoublePrime p (d.C t u) * d.R t u * d.R u 0)
          volume 0 t := by
        have hx := ((hKrow t).mul hR0).intervalIntegrable (μ := volume) 0 t
        have hb : β ^ 2 ≠ 0 := pow_ne_zero _ h.beta_pos.ne'
        have hv := hx.const_mul (β ^ 2)⁻¹
        apply hv.congr
        intro u hu
        rw [uIoc_of_le ht.1] at hu
        have hu0 : 0 ≤ u := hu.1.le
        dsimp [K]
        rw [clampedMemory_eq hu0 hu.2, clampedResponse_eq (le_refl 0) hu0]
        field_simp [h.beta_pos.ne']
      calc
        (∫ u in (0 : ℝ)..t, K t u * f u) = ∫ u in (0 : ℝ)..t, β ^ 2 *
            (xiDoublePrime p (d.C t u) * d.R t u * d.C u 0 -
              xiDoublePrime p (d.C t u) * d.R t u * d.R u 0) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le ht.1] at hu
          exact he u hu
        _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hiC hiR]
    rw [hi, hfeq t ht.1]
    dsimp [f', correlationSlope, responseSlope]
    simp only [intervalIntegral.integral_same, mul_zero, add_zero]
    ring
  have hz := VolterraUniqueness.homogeneous_row_eq_zero f f' d.multiplier K 0 T
    (max 0 L₀) (max 0 S₀) hT (le_max_left _ _) (le_max_left _ _) hf hfzero
    hderiv heq
    (fun t ht => by
      have hl := hL₀ ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩
      exact (show |d.multiplier t| ≤ L₀ by simpa only [Real.norm_eq_abs] using hl).trans
        (le_max_right _ _))
    (fun t _ => ((hKrow t).mul hf).intervalIntegrable 0 t)
    (fun t ht u hu => by
      have hs := hS₀ ⟨(t,u), ⟨⟨ht.1, ht.2.le⟩, ⟨hu.1, hu.2.trans ht.2.le⟩⟩, rfl⟩
      exact (show |K t u| ≤ S₀ by simpa [K, Function.uncurry, Real.norm_eq_abs] using hs).trans
        (le_max_right _ _))
  have hfinal := hz T ⟨hT, le_refl _⟩
  rw [hfeq T hT] at hfinal
  exact sub_eq_zero.mp hfinal


/-- Joint continuity alone determines the moving-endpoint contribution.
The small strip has derivative equal to the integrand at its endpoint. -/
theorem moving_boundary_hasDerivAt {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (t : ℝ) :
    HasDerivAt (fun x => ∫ u in t..x, F x u) (F t t) t := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hn : {z : ℝ × ℝ | ‖F z.1 z.2 - F t t‖ < ε} ∈ 𝓝 (t,t) := by
    have hct : Continuous (fun z : ℝ × ℝ => ‖F z.1 z.2 - F t t‖) :=
      (hF.sub continuous_const).norm
    have hlimit : Tendsto (fun z : ℝ × ℝ => ‖F z.1 z.2 - F t t‖) (𝓝 (t,t)) (𝓝 0) := by
      simpa using (hct.continuousAt : ContinuousAt (fun z : ℝ × ℝ => ‖F z.1 z.2 - F t t‖) (t,t)).tendsto
    exact hlimit.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  filter_upwards [Metric.ball_mem_nhds t hδ] with x hx
  have hb : ∀ u ∈ uIoc t x, ‖F x u - F t t‖ ≤ ε := by
    intro u hu
    have hu' := uIoc_subset_uIcc hu
    have hd : dist u t ≤ dist x t := by
      rw [Real.dist_eq, Real.dist_eq]
      rcases mem_uIcc.mp hu' with hu'' | hu''
      · rw [abs_of_nonneg (sub_nonneg.mpr hu''.1),
          abs_of_nonneg (sub_nonneg.mpr (hu''.1.trans hu''.2))]
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr hu''.2),
          abs_of_nonpos (sub_nonpos.mpr (hu''.1.trans hu''.2))]
        linarith
    have hp : (x,u) ∈ Metric.ball (t,t) δ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨hx, hd.trans_lt hx⟩
    exact (hball hp).le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have he : (∫ u in t..x, F x u) - (∫ u in t..t, F t u) - (x-t) • F t t =
      ∫ u in t..x, (F x u - F t t) := by
    have hrow : Continuous (fun u => F x u) := hF.comp (continuous_const.prodMk continuous_id)
    rw [intervalIntegral.integral_sub (f := fun u => F x u) (g := fun _ => F t t)
      (hrow.intervalIntegrable t x) intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_same]
    simp only [smul_eq_mul]
    ring
  rw [he]
  simpa only [Real.norm_eq_abs] using hi


/-- Mean-value control for a row extended constantly before its initial time. -/
theorem causal_clamp_lipschitzOn {f f' : ℝ → ℝ} {a r : ℝ} {M : ℝ≥0}
    (har : a ≤ r)
    (hd : ∀ x ∈ Icc a r, HasDerivWithinAt f (f' x) (Ici a) x)
    (hbound : ∀ x ∈ Icc a r, ‖f' x‖ ≤ M) :
    LipschitzOnWith M (fun x => f (max x a)) (Iic r) := by
  have hl : LipschitzOnWith M f (Icc a r) :=
    (convex_Icc a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hd x hx).mono (fun _ hy => hy.1))
      (fun x hx => by exact_mod_cast hbound x hx)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hc := (LipschitzWith.id.max_const a).dist_le_mul x y
  have he := hl.dist_le_mul (max x a) ⟨le_max_right _ _,max_le hx har⟩
    (max y a) ⟨le_max_right _ _,max_le hy har⟩
  exact he.trans (mul_le_mul_of_nonneg_left (by simpa using hc) M.coe_nonneg)

/-- Fixed-domain differentiation when the parameter derivative is required
only almost everywhere at the chosen time, and a uniform row Lipschitz bound
handles the causal kink. -/
theorem fixed_integral_hasDerivAt_of_lipschitz
    {F : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {t : ℝ} {U : Set ℝ} {M : ℝ≥0}
    (hF : Continuous (Function.uncurry F)) (hD : Continuous D) (ht : 0 ≤ t)
    (hU : U ∈ 𝓝 t)
    (hLip : ∀ u ∈ Icc 0 t, LipschitzOnWith M (fun x => F x u) U)
    (hDiff : ∀ u ∈ Ico 0 t, HasDerivAt (fun x => F x u) (D u) t) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..t, F x u) (∫ u in (0 : ℝ)..t, D u) t := by
  have hrow (x : ℝ) : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hder := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict (Ioc 0 t)) (F := F) (F' := D) (bound := fun _ => (M : ℝ)) hU
    (Filter.Eventually.of_forall fun x => (hrow x).aestronglyMeasurable)
    ((hrow t).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hD.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun u hu => by
      simpa using hLip u (Ioc_subset_Icc_self hu))))
    (integrable_const (M : ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (show ∀ᵐ u ∂volume, u ≠ t from by simp [ae_iff])] with u hu hne
      exact hDiff u ⟨hu.1.le, lt_of_le_of_ne hu.2 hne⟩)
  simpa only [intervalIntegral.integral_of_le ht] using hder.2

/-- Moving-upper-limit Leibniz rule with pointwise causal derivative and
uniform local Lipschitz hypotheses, proved using the two preceding lemmas. -/
theorem moving_integral_hasDerivAt_of_lipschitz
    {F : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {t : ℝ} {U : Set ℝ} {M : ℝ≥0}
    (hF : Continuous (Function.uncurry F)) (hD : Continuous D) (ht : 0 ≤ t)
    (hU : U ∈ 𝓝 t)
    (hLip : ∀ u ∈ Icc 0 t, LipschitzOnWith M (fun x => F x u) U)
    (hDiff : ∀ u ∈ Ico 0 t, HasDerivAt (fun x => F x u) (D u) t) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, F x u)
      ((∫ u in (0 : ℝ)..t, D u) + F t t) t := by
  have ha := fixed_integral_hasDerivAt_of_lipschitz hF hD ht hU hLip hDiff
  have hb := moving_boundary_hasDerivAt hF t
  apply (ha.add hb).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro x
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable t x)).symm


theorem clampedResponseSlope_eq {p : ℕ} {β : ℝ} {d : CKData} {t u : ℝ}
    (hu : 0 ≤ u) (hut : u ≤ t) :
    clampedResponseSlope p β d t u = responseSlope p β d t u := by
  simp only [clampedResponseSlope, max_eq_right hu, max_eq_left hut]

/-- Actual derivative of the initial-condition contribution to Green covariance. -/
theorem initial_term_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt (fun x => d.R x 0 * d.R s 0)
      (-d.multiplier t * (d.R t 0 * d.R s 0) + β ^ 2 *
        ∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u) * d.R t u *
          (d.R u 0 * d.R s 0)) t := by
  have hd := (response_hasDerivAt h (le_refl 0) ht).mul_const (d.R s 0)
  have hi : (∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u) * d.R t u *
      (d.R u 0 * d.R s 0)) =
      (∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u) * d.R t u * d.R u 0) * d.R s 0 := by
    simp only [← mul_assoc, intervalIntegral.integral_mul_const]
  convert hd using 1
  rw [hi]
  unfold responseSlope
  ring

/-- Leibniz rule for the moving white-noise diagonal. In particular the
unit boundary term is proved from R(t,t)=1, including at time zero. -/
theorem white_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => ∫ u in (0 : ℝ)..x, d.R x u ^ 2)
      ((∫ u in (0 : ℝ)..t, 2 * d.R t u * responseSlope p β d t u) + 1) (Ici 0) t := by
  let r : ℝ := t+1
  let F : ℝ → ℝ → ℝ := fun x u => clampedResponse d x u ^ 2
  let G : ℝ → ℝ → ℝ := fun x u =>
    2 * clampedResponse d x u * clampedResponseSlope p β d x u
  have hR := clampedResponse_continuous h
  have hD := clampedResponseSlope_continuous h
  have hF : Continuous (Function.uncurry F) := hR.pow 2
  have hG : Continuous (Function.uncurry G) := (continuous_const.mul hR).mul hD
  obtain ⟨M₀,hM₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) r) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image hG.norm.continuousOn
  let M : ℝ≥0 := ⟨max 0 M₀, le_max_left _ _⟩
  have hLip (u : ℝ) (hu : u ∈ Icc 0 t) :
      LipschitzOnWith M (fun x => F x u) (Iic r) := by
    have hl := causal_clamp_lipschitzOn (f := fun x => d.R x u ^ 2)
      (f' := fun x => 2 * d.R x u * responseSlope p β d x u)
      (M := M) (a := u) (r := r) (hu.2.trans (by dsimp [r]; linarith))
      (fun x hx => by
        convert (h.response_derivative x u hu.1 hx.1).pow 2 using 1; norm_num)
      (fun x hx => by
        have hx0 := hu.1.trans hx.1
        have hur : u ≤ r := hu.2.trans (by dsimp [r]; linarith)
        have hb := hM₀ ⟨(x,u), ⟨⟨hx0,hx.2⟩,⟨hu.1,hur⟩⟩,rfl⟩
        have he : G x u = 2 * d.R x u * responseSlope p β d x u := by
          dsimp [G]
          rw [clampedResponse_eq hu.1 hx.1, clampedResponseSlope_eq hu.1 hx.1]
        change ‖2 * d.R x u * responseSlope p β d x u‖ ≤ max 0 M₀
        rw [← he]
        exact hb.trans (le_max_right _ _))
    simpa only [F,clampedResponse,max_eq_right hu.1] using hl
  have hDiff (u : ℝ) (hu : u ∈ Ico 0 t) :
      HasDerivAt (fun x => F x u) (G t u) t := by
    convert (clampedResponse_hasDerivAt h hu.1 hu.2).pow 2 using 1; norm_num [F, G]
  have hd := moving_integral_hasDerivAt_of_lipschitz (D := fun u => G t u) hF
    (hG.comp (continuous_const.prodMk continuous_id)) ht
    (show Iic r ∈ 𝓝 t from Iic_mem_nhds (by dsimp [r]; linarith)) hLip hDiff
  have hi : (∫ u in (0 : ℝ)..t, G t u) =
      ∫ u in (0 : ℝ)..t, 2 * d.R t u * responseSlope p β d t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp [G]
    rw [clampedResponse_eq hu.1 hu.2, clampedResponseSlope_eq hu.1 hu.2]
  have hdiag : F t t = 1 := by
    dsimp [F]
    rw [clampedResponse_eq ht (le_refl _), h.response_diagonal t ht]
    norm_num
  rw [hi,hdiag] at hd
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp [F]
    rw [clampedResponse_eq hu.1 hu.2]
  · exact ht


/-- Moving-endpoint propagation of any continuous deterministic forcing.
This differentiates the actual causal response integral, including the unit
response diagonal boundary term. -/
theorem weighted_response_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {A : ℝ → ℝ} (hA : Continuous A) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => ∫ u in (0 : ℝ)..x, d.R x u * A u)
      ((∫ u in (0 : ℝ)..t, responseSlope p β d t u * A u) + A t) (Ici 0) t := by
  let r : ℝ := t+1
  let F : ℝ → ℝ → ℝ := fun x u => clampedResponse d x u * A u
  let G : ℝ → ℝ → ℝ := fun x u => clampedResponseSlope p β d x u * A u
  have hR := clampedResponse_continuous h
  have hD := clampedResponseSlope_continuous h
  have hF : Continuous (Function.uncurry F) := hR.mul (hA.comp continuous_snd)
  have hG : Continuous (Function.uncurry G) := hD.mul (hA.comp continuous_snd)
  obtain ⟨M₀,hM₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) r) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image hG.norm.continuousOn
  let M : ℝ≥0 := ⟨max 0 M₀, le_max_left _ _⟩
  have hLip (u : ℝ) (hu : u ∈ Icc 0 t) :
      LipschitzOnWith M (fun x => F x u) (Iic r) := by
    have hl := causal_clamp_lipschitzOn (f := fun x => d.R x u * A u)
      (f' := fun x => responseSlope p β d x u * A u)
      (M := M) (a := u) (r := r) (hu.2.trans (by dsimp [r]; linarith))
      (fun x hx => (h.response_derivative x u hu.1 hx.1).mul_const _)
      (fun x hx => by
        have hx0 := hu.1.trans hx.1
        have hur : u ≤ r := hu.2.trans (by dsimp [r]; linarith)
        have hb := hM₀ ⟨(x,u), ⟨⟨hx0,hx.2⟩,⟨hu.1,hur⟩⟩,rfl⟩
        have he : G x u = responseSlope p β d x u * A u := by
          dsimp [G]
          rw [clampedResponseSlope_eq hu.1 hx.1]
        change ‖responseSlope p β d x u * A u‖ ≤ max 0 M₀
        rw [← he]
        exact hb.trans (le_max_right _ _))
    simpa only [F,clampedResponse,max_eq_right hu.1] using hl
  have hDiff (u : ℝ) (hu : u ∈ Ico 0 t) :
      HasDerivAt (fun x => F x u) (G t u) t :=
    (clampedResponse_hasDerivAt h hu.1 hu.2).mul_const _
  have hd := moving_integral_hasDerivAt_of_lipschitz (D := fun u => G t u) hF
    (hG.comp (continuous_const.prodMk continuous_id)) ht
    (show Iic r ∈ 𝓝 t from Iic_mem_nhds (by dsimp [r]; linarith)) hLip hDiff
  have hi : (∫ u in (0 : ℝ)..t, G t u) =
      ∫ u in (0 : ℝ)..t, responseSlope p β d t u * A u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp [G]
    rw [clampedResponseSlope_eq hu.1 hu.2]
  have hdiag : F t t = A t := by
    dsimp [F]
    rw [clampedResponse_eq ht (le_refl _), h.response_diagonal t ht,one_mul]
  rw [hi,hdiag] at hd
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp [F]
    rw [clampedResponse_eq hu.1 hu.2]
  · exact ht

/-- The colored forcing propagated at a fixed second time. -/
@[expose] def coloredForcing (p : ℕ) (β : ℝ) (d : CKData) (s u : ℝ) : ℝ :=
  β ^ 2 * p * ∫ v in (0 : ℝ)..s,
    clampedResponse d s v * clampedCorrelation d u v ^ (p-1)

theorem coloredForcing_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) : Continuous (coloredForcing p β d s) := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hR.comp (continuous_const.prodMk continuous_snd)).mul (hC.pow _)

/-- Actual moving-domain derivative of the colored term, expressed before
reordering its self-energy memory by triangular Fubini. -/
theorem colored_term_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => ∫ u in (0 : ℝ)..x,
        d.R x u * coloredForcing p β d s u)
      ((∫ u in (0 : ℝ)..t, responseSlope p β d t u * coloredForcing p β d s u) +
        coloredForcing p β d s t) (Ici 0) t :=
  weighted_response_hasDerivWithinAt h (coloredForcing_continuous h s) ht


/-- Moving both arguments of a symmetric kernel doubles the continuous
first-argument derivative. The proof uses the mean value bound uniformly on
the short parameter interval, so separate derivatives are not simply assumed
to imply joint differentiability. -/
theorem symmetric_diagonal_hasDerivWithinAt
    {F H : ℝ → ℝ → ℝ} (hH : Continuous (Function.uncurry H))
    (hSym : ∀ x y, 0 ≤ x → 0 ≤ y → F x y = F y x)
    (hPartial : ∀ x y, 0 ≤ x → 0 ≤ y →
      HasDerivWithinAt (fun z => F z y) (H x y) (Ici 0) x)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => F x x) (2 * H t t) (Ici 0) t := by
  have hright := (hPartial t t ht ht).isLittleO
  have hleft : (fun x => F x x - F t x - (x-t) • H t t) =o[𝓝[Ici 0] t]
      (fun x => x-t) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hct : Continuous (fun z : ℝ × ℝ => ‖H z.1 z.2 - H t t‖) :=
      (hH.sub continuous_const).norm
    have hlim : Tendsto (fun z : ℝ × ℝ => ‖H z.1 z.2 - H t t‖)
        (𝓝 (t,t)) (𝓝 0) := by
      simpa using (hct.continuousAt : ContinuousAt (fun z : ℝ × ℝ => ‖H z.1 z.2 - H t t‖) (t,t)).tendsto
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hlim.eventually (gt_mem_nhds hε))
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ x in 𝓝 t, x ∈ Metric.ball t δ from
        Metric.ball_mem_nhds t hδ).filter_mono nhdsWithin_le_nhds] with x hx hxball
    have hnonneg (v : ℝ) (hv : v ∈ uIcc t x) : 0 ≤ v := by
      rcases mem_uIcc.mp hv with hv' | hv'
      · exact ht.trans hv'.1
      · exact hx.trans hv'.1
    have hdist (v : ℝ) (hv : v ∈ uIcc t x) : dist v t ≤ dist x t := by
      rw [Real.dist_eq,Real.dist_eq]
      rcases mem_uIcc.mp hv with hv' | hv'
      · rw [abs_of_nonneg (sub_nonneg.mpr hv'.1),
          abs_of_nonneg (sub_nonneg.mpr (hv'.1.trans hv'.2))]
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr hv'.2),
          abs_of_nonpos (sub_nonpos.mpr (hv'.1.trans hv'.2))]
        linarith
    let g : ℝ → ℝ := fun v => F v x - v * H t t
    have hder (v : ℝ) (hv : v ∈ uIcc t x) :
        HasDerivWithinAt g (H v x - H t t) (uIcc t x) v := by
      have hd := (hPartial v x (hnonneg v hv) hx).sub
        ((hasDerivAt_id v).mul_const (H t t)).hasDerivWithinAt
      convert hd.mono (fun u hu => hnonneg u hu) using 1 <;> first | rfl | simp
    have hbound (v : ℝ) (hv : v ∈ uIcc t x) : ‖H v x - H t t‖ ≤ ε := by
      have hp : (v,x) ∈ Metric.ball (t,t) δ := by
        rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
        exact ⟨(hdist v hv).trans_lt hxball,hxball⟩
      exact (hball hp).le
    have he := (convex_uIcc t x).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound left_mem_uIcc right_mem_uIcc
    have ha : g x - g t = F x x - F t x - (x-t) • H t t := by
      dsimp [g]
      ring
    rw [ha] at he
    exact he
  apply HasDerivWithinAt.of_isLittleO
  apply (hleft.add hright).congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    dsimp
    rw [hSym t x ht hx]
    ring
  · exact Filter.EventuallyEq.rfl


@[expose] def coloredTerm (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, clampedResponse d t u * coloredForcing p β d s u

@[expose] def coloredPartial (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..t, clampedResponseSlope p β d t u * coloredForcing p β d s u) +
    coloredForcing p β d s t

theorem coloredForcing_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (coloredForcing p β d)) := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hR.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      ((hC.comp (continuous_fst.snd.prodMk continuous_snd)).pow _)
  · exact continuous_fst

theorem coloredTerm_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (coloredTerm p β d)) := by
  have hR := clampedResponse_continuous h
  have hA := coloredForcing_joint_continuous h
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hR.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hA.comp (continuous_fst.snd.prodMk continuous_snd))
  · exact continuous_fst

theorem coloredPartial_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (coloredPartial p β d)) := by
  have hD := clampedResponseSlope_continuous h
  have hA := coloredForcing_joint_continuous h
  apply Continuous.add
  · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (hD.comp (continuous_fst.fst.prodMk continuous_snd)).mul
        (hA.comp (continuous_fst.snd.prodMk continuous_snd))
    · exact continuous_fst
  · exact hA.comp (continuous_snd.prodMk continuous_fst)

theorem coloredTerm_eq_double_integral (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) :
    coloredTerm p β d t s = β ^ 2 * p *
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u * clampedResponse d s v * clampedCorrelation d u v ^ (p-1) := by
  unfold coloredTerm coloredForcing
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  ring

theorem coloredTerm_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    coloredTerm p β d t s = coloredTerm p β d s t := by
  rw [coloredTerm_eq_double_integral, coloredTerm_eq_double_integral]
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  have hswap := rectangle_integral_swap
    (F := fun u v => clampedResponse d t u * clampedResponse d s v *
      clampedCorrelation d u v ^ (p-1))
    (((hR.comp (continuous_const.prodMk continuous_fst)).mul
      (hR.comp (continuous_const.prodMk continuous_snd))).mul (hC.pow (p-1))) 0 t 0 s
  rw [hswap]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp
  have hsym : clampedCorrelation d v u = clampedCorrelation d u v :=
    h.correlation_symmetric _ _ (le_max_left _ _) (le_max_left _ _)
  rw [hsym]
  ring

theorem coloredTerm_partial_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => coloredTerm p β d x s)
      (coloredPartial p β d t s) (Ici 0) t := by
  have hd := colored_term_hasDerivWithinAt h s ht
  have hi : (∫ u in (0 : ℝ)..t, responseSlope p β d t u * coloredForcing p β d s u) =
      ∫ u in (0 : ℝ)..t, clampedResponseSlope p β d t u * coloredForcing p β d s u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp
    rw [clampedResponseSlope_eq hu.1 hu.2]
  rw [hi] at hd
  apply hd.congr_of_mem
  · intro x hx
    unfold coloredTerm
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp
    rw [clampedResponse_eq hu.1 hu.2]
  · exact ht

/-- The colored term's diagonal derivative moves both response arguments;
its factor two is proved from Fubini symmetry and the uniform partial derivative. -/
theorem coloredTerm_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => coloredTerm p β d x x)
      (2 * coloredPartial p β d t t) (Ici 0) t :=
  symmetric_diagonal_hasDerivWithinAt (coloredPartial_joint_continuous h)
    (fun t s _ _ => coloredTerm_symmetric h t s)
    (fun _t s ht _ => coloredTerm_partial_hasDerivWithinAt h s ht) ht


/-- Response slope as the linear Volterra operator with fixed CK self-energy. -/
theorem responseSlope_linear_memory {p : ℕ} {β : ℝ} {d : CKData}
    {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    responseSlope p β d t u = -d.multiplier t * clampedResponse d t u +
      ∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u := by
  have hi : (∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) =
      β ^ 2 * ∫ z in u..t, xiDoublePrime p (d.C t z) * d.R t z * d.R z u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hut] at hz
    dsimp
    rw [clampedMemory_eq (hu.trans hz.1) hz.2, clampedResponse_eq hu hz.1]
    ring
  rw [hi,clampedResponse_eq hu hut]
  rfl


@[expose] def initialTerm (d : CKData) (t s : ℝ) : ℝ :=
  clampedResponse d t 0 * clampedResponse d s 0

@[expose] def initialPartial (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  clampedResponseSlope p β d t 0 * clampedResponse d s 0

@[expose] def whiteTerm (d : CKData) (t s : ℝ) : ℝ :=
  2 * ∫ u in (0 : ℝ)..min t s, clampedResponse d t u * clampedResponse d s u

theorem clampedGreen_decomposition (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) :
    clampedGreen p β d t s = initialTerm d t s + whiteTerm d t s + coloredTerm p β d t s := by
  rw [coloredTerm_eq_double_integral]
  rfl

theorem initialPartial_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (initialPartial p β d)) := by
  exact ((clampedResponseSlope_continuous h).comp (continuous_fst.prodMk continuous_const)).mul
    ((clampedResponse_continuous h).comp (continuous_snd.prodMk continuous_const))

theorem initialTerm_partial_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => initialTerm d x s) (initialPartial p β d t s) (Ici 0) t := by
  have hd := (h.response_derivative t 0 (le_refl 0) ht).mul_const (clampedResponse d s 0)
  rw [← clampedResponseSlope_eq (le_refl 0) ht] at hd
  apply hd.congr_of_mem
  · intro x hx
    dsimp [initialTerm]
    rw [clampedResponse_eq (le_refl 0) hx]
  · exact ht

theorem initialTerm_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => initialTerm d x x) (2 * initialPartial p β d t t) (Ici 0) t :=
  symmetric_diagonal_hasDerivWithinAt (initialPartial_joint_continuous h)
    (fun _ _ _ _ => mul_comm _ _)
    (fun _ s ht _ => initialTerm_partial_hasDerivWithinAt h s ht) ht

theorem whiteTerm_offdiag_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivAt (fun x => whiteTerm d x s)
      (2 * ∫ u in (0 : ℝ)..s, clampedResponseSlope p β d t u * clampedResponse d s u) t := by
  have hd := (white_integral_hasDerivAt h hs hst).const_mul 2
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hst] with x hx
  dsimp [whiteTerm]
  rw [min_eq_right hx.le]

theorem whiteTerm_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => whiteTerm d x x)
      (2 * ((∫ u in (0 : ℝ)..t,
        2 * clampedResponse d t u * clampedResponseSlope p β d t u) + 1)) (Ici 0) t := by
  have hd := (white_diagonal_hasDerivWithinAt h ht).const_mul 2
  have hi : (∫ u in (0 : ℝ)..t, 2 * d.R t u * responseSlope p β d t u) =
      ∫ u in (0 : ℝ)..t, 2 * clampedResponse d t u * clampedResponseSlope p β d t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp
    rw [clampedResponse_eq hu.1 hu.2,clampedResponseSlope_eq hu.1 hu.2]
  rw [hi] at hd
  apply hd.congr_of_mem
  · intro x hx
    unfold whiteTerm
    rw [min_self]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp
    rw [clampedResponse_eq hu.1 hu.2]
    ring
  · exact ht


/-- The integrated linear response equation, with its triangular memory
reordered by the actual compact Fubini theorem. -/
theorem responseSlope_integral_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {A : ℝ → ℝ} (hA : Continuous A)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ u in (0 : ℝ)..s, clampedResponseSlope p β d t u * A u) =
      -d.multiplier t * (∫ u in (0 : ℝ)..s, clampedResponse d t u * A u) +
      ∫ z in (0 : ℝ)..t, clampedMemory p β d t z *
        (∫ u in (0 : ℝ)..min z s, clampedResponse d z u * A u) := by
  have hR := clampedResponse_continuous h
  have hD := clampedResponseSlope_continuous h
  have hK := clampedMemory_continuous h
  have hi : (∫ u in (0 : ℝ)..s,
      clampedResponseSlope p β d t u * A u +
        d.multiplier t * (clampedResponse d t u * A u)) =
      ∫ u in (0 : ℝ)..s, A u *
        (∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs] at hu
    dsimp
    rw [clampedResponseSlope_eq hu.1 (hu.2.trans hst),
      responseSlope_linear_memory hu.1 (hu.2.trans hst)]
    ring
  have hDi : Continuous (fun u => clampedResponseSlope p β d t u * A u) :=
    (hD.comp (continuous_const.prodMk continuous_id)).mul hA
  have hRi : Continuous (fun u => d.multiplier t * (clampedResponse d t u * A u)) :=
    continuous_const.mul ((hR.comp (continuous_const.prodMk continuous_id)).mul hA)
  rw [intervalIntegral.integral_add (f := fun u => clampedResponseSlope p β d t u * A u)
    (g := fun u => d.multiplier t * (clampedResponse d t u * A u))
    (hDi.intervalIntegrable 0 s) (hRi.intervalIntegrable 0 s),
    intervalIntegral.integral_const_mul,
    TriangleUniqueness.weighted_triangle_memory_swap hR hK hA hs hst] at hi
  linarith only [hi]

theorem coloredPartial_linear {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    coloredPartial p β d t s = -d.multiplier t * coloredTerm p β d t s +
      (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * coloredTerm p β d z s) +
      coloredForcing p β d s t := by
  have hi := responseSlope_integral_identity h (coloredForcing_continuous h s) ht (le_refl t)
  have hm : (∫ z in (0 : ℝ)..t, clampedMemory p β d t z *
      (∫ u in (0 : ℝ)..min z t, clampedResponse d z u * coloredForcing p β d s u)) =
      ∫ z in (0 : ℝ)..t, clampedMemory p β d t z * coloredTerm p β d z s := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le ht] at hz
    dsimp
    rw [min_eq_left hz.2]
    rfl
  unfold coloredPartial
  rw [hi,hm]
  rfl

theorem initialPartial_linear {p : ℕ} {β : ℝ} {d : CKData}
    (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    initialPartial p β d t s = -d.multiplier t * initialTerm d t s +
      ∫ z in (0 : ℝ)..t, clampedMemory p β d t z * initialTerm d z s := by
  have hi : (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * initialTerm d z s) =
      (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedResponse d z 0) *
        clampedResponse d s 0 := by
    unfold initialTerm
    simp only [← mul_assoc,intervalIntegral.integral_mul_const]
  rw [hi]
  unfold initialPartial initialTerm
  rw [clampedResponseSlope_eq (le_refl 0) ht,responseSlope_linear_memory (le_refl 0) ht]
  ring

theorem white_offdiag_slope_linear {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (2 * ∫ u in (0 : ℝ)..s,
      clampedResponseSlope p β d t u * clampedResponse d s u) =
      -d.multiplier t * whiteTerm d t s +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z * whiteTerm d z s := by
  have hR := clampedResponse_continuous h
  have hi := responseSlope_integral_identity h (A := fun u => clampedResponse d s u)
    (hR.comp (continuous_const.prodMk continuous_id)) hs hst
  have hm : (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * whiteTerm d z s) =
      2 * ∫ z in (0 : ℝ)..t, clampedMemory p β d t z *
        (∫ u in (0 : ℝ)..min z s, clampedResponse d z u * clampedResponse d s u) := by
    calc
      (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * whiteTerm d z s) =
        ∫ z in (0 : ℝ)..t, 2 * (clampedMemory p β d t z *
          (∫ u in (0 : ℝ)..min z s, clampedResponse d z u * clampedResponse d s u)) := by
        apply intervalIntegral.integral_congr
        intro z _
        dsimp [whiteTerm]
        ring
      _ = _ := intervalIntegral.integral_const_mul 2 _
  rw [hm]
  unfold whiteTerm
  rw [min_eq_right hst,hi]
  ring

theorem white_diagonal_slope_linear {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    (2 * ((∫ u in (0 : ℝ)..t,
      2 * clampedResponse d t u * clampedResponseSlope p β d t u) + 1)) =
      -2 * d.multiplier t * whiteTerm d t t +
        2 * (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * whiteTerm d z t) + 2 := by
  have hi := white_offdiag_slope_linear h ht (le_refl t)
  have hm : (∫ u in (0 : ℝ)..t,
      2 * clampedResponse d t u * clampedResponseSlope p β d t u) =
      2 * ∫ u in (0 : ℝ)..t,
        clampedResponseSlope p β d t u * clampedResponse d t u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp
    ring
  rw [hm,hi]
  ring


theorem initialTerm_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (initialTerm d)) := by
  have hR := clampedResponse_continuous h
  exact (hR.comp (continuous_fst.prodMk continuous_const)).mul
    (hR.comp (continuous_snd.prodMk continuous_const))

theorem whiteTerm_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (whiteTerm d)) := by
  have hR := clampedResponse_continuous h
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hR.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hR.comp (continuous_fst.snd.prodMk continuous_snd))
  · exact continuous_fst.min continuous_snd

theorem green_memory_decomposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedGreen p β d z s) =
      (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * initialTerm d z s) +
      (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * whiteTerm d z s) +
      (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * coloredTerm p β d z s) := by
  have hK : Continuous (fun z => clampedMemory p β d t z) :=
    (clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
  have hI : Continuous (fun z => clampedMemory p β d t z * initialTerm d z s) :=
    hK.mul ((initialTerm_joint_continuous h).comp (continuous_id.prodMk continuous_const))
  have hW : Continuous (fun z => clampedMemory p β d t z * whiteTerm d z s) :=
    hK.mul ((whiteTerm_joint_continuous h).comp (continuous_id.prodMk continuous_const))
  have hC : Continuous (fun z => clampedMemory p β d t z * coloredTerm p β d z s) :=
    hK.mul ((coloredTerm_joint_continuous h).comp (continuous_id.prodMk continuous_const))
  calc
    (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedGreen p β d z s) =
      ∫ z in (0 : ℝ)..t, (clampedMemory p β d t z * initialTerm d z s +
        clampedMemory p β d t z * whiteTerm d z s) +
          clampedMemory p β d t z * coloredTerm p β d z s := by
      apply intervalIntegral.integral_congr
      intro z _
      dsimp
      rw [clampedGreen_decomposition]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (f := fun z => clampedMemory p β d t z * initialTerm d z s +
          clampedMemory p β d t z * whiteTerm d z s)
        (g := fun z => clampedMemory p β d t z * coloredTerm p β d z s)
        ((hI.add hW).intervalIntegrable 0 t) (hC.intervalIntegrable 0 t),
        intervalIntegral.integral_add
        (f := fun z => clampedMemory p β d t z * initialTerm d z s)
        (g := fun z => clampedMemory p β d t z * whiteTerm d z s)
        (hI.intervalIntegrable 0 t) (hW.intervalIntegrable 0 t)]

/-- The full Green candidate satisfies the off-diagonal linear correlation
Volterra equation, derived term by term from CK, Leibniz and triangular Fubini. -/
theorem clampedGreen_offdiag_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivAt (fun x => clampedGreen p β d x s)
      (-d.multiplier t * clampedGreen p β d t s +
        (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedGreen p β d z s) +
        coloredForcing p β d s t) t := by
  have ht : 0 ≤ t := hs.trans hst.le
  have htpos : 0 < t := lt_of_le_of_lt hs hst
  have hi := (initialTerm_partial_hasDerivWithinAt h s ht).hasDerivAt (Ici_mem_nhds htpos)
  have hw := whiteTerm_offdiag_hasDerivAt h hs hst
  have hc := (coloredTerm_partial_hasDerivWithinAt h s ht).hasDerivAt (Ici_mem_nhds htpos)
  convert (hi.add hw).add hc using 1
  · funext x
    exact clampedGreen_decomposition p β d x s
  · rw [initialPartial_linear s ht,white_offdiag_slope_linear h hs hst.le,
      coloredPartial_linear h s ht,green_memory_decomposition h t s,clampedGreen_decomposition]
    ring

/-- The full diagonal equation includes both moving response arguments and
the white-noise boundary term 2. -/
theorem clampedGreen_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => clampedGreen p β d x x)
      (-2 * d.multiplier t * clampedGreen p β d t t +
        2 * (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedGreen p β d z t) +
        2 * coloredForcing p β d t t + 2) (Ici 0) t := by
  have hi := initialTerm_diagonal_hasDerivWithinAt h ht
  have hw := whiteTerm_diagonal_hasDerivWithinAt h ht
  have hc := coloredTerm_diagonal_hasDerivWithinAt h ht
  convert (hi.add hw).add hc using 1
  · funext x
    exact clampedGreen_decomposition p β d x x
  · rw [initialPartial_linear t ht,white_diagonal_slope_linear h ht,
      coloredPartial_linear h t ht,green_memory_decomposition h t t,clampedGreen_decomposition]
    ring

end SphericalAging.GreenCovariance
