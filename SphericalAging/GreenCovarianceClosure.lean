module

public import SphericalAging.GreenCovariance
public import SphericalAging.CKDiagonal

public section

/-!
# Closure of the Green covariance identity

This identifies the explicit Green candidate with the CK correlation from
its actual differential equations and two-variable Volterra uniqueness.
The Green identity and zero covariance error are conclusions, not inputs.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.GreenCovarianceClosure
open CKSpecification GreenCovariance

theorem correlation_memory_eq {p : ℕ} {β : ℝ} {d : CKData} {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u s) =
      β ^ 2 * ∫ u in (0 : ℝ)..t,
        xiDoublePrime p (d.C t u) * d.R t u * d.C u s := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp
  rw [clampedMemory_eq hu.1 hu.2,clampedCorrelation_eq hu.1 hs]
  ring

theorem coloredForcing_eq {p : ℕ} {β : ℝ} {d : CKData} {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    coloredForcing p β d s t =
      β ^ 2 * ∫ u in (0 : ℝ)..s, xiPrime p (d.C t u) * d.R s u := by
  have hi : (∫ u in (0 : ℝ)..s, xiPrime p (d.C t u) * d.R s u) =
      (p : ℝ) * ∫ u in (0 : ℝ)..s,
        clampedResponse d s u * clampedCorrelation d t u ^ (p-1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs] at hu
    dsimp [xiPrime]
    rw [clampedResponse_eq hu.1 hu.2,clampedCorrelation_eq ht hu.1]
    ring
  unfold coloredForcing
  rw [hi]
  ring

theorem correlationSlope_linear {p : ℕ} {β : ℝ} {d : CKData} {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    correlationSlope p β d t s = -d.multiplier t * clampedCorrelation d t s +
      (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u s) +
      coloredForcing p β d s t := by
  rw [clampedCorrelation_eq ht hs,correlation_memory_eq ht hs,coloredForcing_eq ht hs]
  rfl

theorem clampedCorrelation_offdiag_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivAt (fun x => clampedCorrelation d x s)
      (-d.multiplier t * clampedCorrelation d t s +
        (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u s) +
        coloredForcing p β d s t) t := by
  have ht : 0 ≤ t := hs.trans hst.le
  have hd := (h.correlation_derivative t s hs hst.le).hasDerivAt (Ici_mem_nhds hst)
  rw [correlationSlope_linear ht hs] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (lt_of_le_of_lt hs hst)] with x hx
  exact clampedCorrelation_eq hx.le hs

theorem clampedCorrelation_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => clampedCorrelation d x x) 0 (Ici 0) t := by
  apply (hasDerivWithinAt_const t (Ici 0) (1 : ℝ)).congr_of_mem
  · intro x hx
    rw [clampedCorrelation_eq hx hx]
    exact h.correlation_diagonal x hx
  · exact ht

theorem clampedCorrelation_diagonal_cancellation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    -2 * d.multiplier t * clampedCorrelation d t t +
      2 * (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u t) +
      2 * coloredForcing p β d t t + 2 = 0 := by
  have hs := CKDiagonal.correlation_diagonal_slope h ht
  rw [correlationSlope_linear ht ht] at hs
  nlinarith only [hs]

@[expose] def covarianceError (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  clampedGreen p β d t s - clampedCorrelation d t s

theorem covarianceError_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (covarianceError p β d)) :=
  (clampedGreen_continuous h).sub (clampedCorrelation_continuous h)

theorem covarianceError_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    covarianceError p β d t s = covarianceError p β d s t := by
  unfold covarianceError
  rw [clampedGreen_symmetric h t s]
  have he : clampedCorrelation d t s = clampedCorrelation d s t :=
    h.correlation_symmetric _ _ (le_max_left _ _) (le_max_left _ _)
  rw [he]

theorem covarianceError_zero_initial {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : covarianceError p β d 0 0 = 0 := by
  have hG : clampedGreen p β d 0 0 = 1 := by
    rw [clampedGreen_eq (le_refl 0) (le_refl 0),
      greenCovariance_initial (h.response_diagonal 0 (le_refl 0)) 0 (le_refl 0),
      h.response_diagonal 0 (le_refl 0)]
  unfold covarianceError
  rw [hG,clampedCorrelation_eq (le_refl 0) (le_refl 0),h.correlation_diagonal 0 (le_refl 0)]
  ring

theorem covarianceError_memory_eq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * covarianceError p β d u s) =
      (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedGreen p β d u s) -
      (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u s) := by
  have hK : Continuous (fun u => clampedMemory p β d t u) :=
    (clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
  have hG : Continuous (fun u => clampedMemory p β d t u * clampedGreen p β d u s) :=
    hK.mul ((clampedGreen_continuous h).comp (continuous_id.prodMk continuous_const))
  have hC : Continuous (fun u => clampedMemory p β d t u * clampedCorrelation d u s) :=
    hK.mul ((clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const))
  rw [← intervalIntegral.integral_sub (hG.intervalIntegrable 0 t) (hC.intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp [covarianceError]
  ring

theorem covarianceError_offdiag_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivAt (fun x => covarianceError p β d x s)
      (TriangleUniqueness.offdiagSlope (covarianceError p β d) d.multiplier
        (clampedMemory p β d) t s) t := by
  have hd := (clampedGreen_offdiag_hasDerivAt h hs hst).sub
    (clampedCorrelation_offdiag_hasDerivAt h hs hst)
  convert hd using 1
  · rfl
  · unfold TriangleUniqueness.offdiagSlope
    rw [covarianceError_memory_eq h t s]
    unfold covarianceError
    ring

theorem covarianceError_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun x => covarianceError p β d x x)
      (TriangleUniqueness.diagonalSlope (covarianceError p β d) d.multiplier
        (clampedMemory p β d) t) (Ici 0) t := by
  have hd := (clampedGreen_diagonal_hasDerivWithinAt h ht).sub
    (clampedCorrelation_diagonal_hasDerivWithinAt h ht)
  have hc := clampedCorrelation_diagonal_cancellation h ht
  convert hd using 1
  · rfl
  · unfold TriangleUniqueness.diagonalSlope
    rw [covarianceError_memory_eq h t t]
    unfold covarianceError
    nlinarith only [hc]


/-- The covariance error vanishes by genuine two-variable Volterra triangle
uniqueness. Its diagonal is determined by its equation, not assumed zero. -/
theorem covarianceError_eq_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    covarianceError p β d t s = 0 := by
  let T : ℝ := max t s
  have hT : 0 ≤ T := ht.trans (le_max_left _ _)
  obtain ⟨L₀,hL₀⟩ := isCompact_Icc.bddAbove_image
    ((h.multiplier_continuous.mono (show Icc 0 T ⊆ Ici 0 from fun _ hx => hx.1)).norm)
  obtain ⟨S₀,hS₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image (clampedMemory_continuous h).norm.continuousOn
  have hz := TriangleUniqueness.homogeneous_triangle_eq_zero
    (D := covarianceError p β d) (K := clampedMemory p β d) (ell := d.multiplier)
    (T := T) (L := max 0 L₀) (S := max 0 S₀) hT (le_max_left _ _) (le_max_left _ _)
    (covarianceError_continuous h)
    (fun t _ s _ => covarianceError_symmetric h t s) (covarianceError_zero_initial h)
    (fun t ht => by
      have hl := hL₀ ⟨t,ht,rfl⟩
      exact (show |d.multiplier t| ≤ L₀ by simpa only [Real.norm_eq_abs] using hl).trans
        (le_max_right _ _))
    (fun t ht u hu => by
      have hsu := hS₀ ⟨(t,u),⟨ht,⟨hu.1,hu.2.trans ht.2⟩⟩,rfl⟩
      exact (show |clampedMemory p β d t u| ≤ S₀ by
        simpa only [Function.uncurry_apply_pair,Real.norm_eq_abs] using hsu).trans (le_max_right _ _))
    (fun _ _ _ hs hst => covarianceError_offdiag_hasDerivAt h hs.1 hst)
    (fun _ ht => covarianceError_diagonal_hasDerivWithinAt h ht.1)
  exact hz t ⟨ht,le_max_left _ _⟩ s ⟨hs,le_max_right _ _⟩

/-- Full Green covariance identity (Proposition 4.2), for all nonnegative
pairs of times and from the faithful CK equations alone. -/
theorem green_covariance_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    d.C t s = greenCovariance p β d t s := by
  have hz := covarianceError_eq_zero h ht hs
  unfold covarianceError at hz
  have he := sub_eq_zero.mp hz
  rw [clampedGreen_eq ht hs,clampedCorrelation_eq ht hs] at he
  exact he.symm

/-- The physical Green covariance diagonal bounds the squared response row. -/
theorem response_row_sq_integral_le {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hphysical : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    2 * (∫ u in (0 : ℝ)..t, d.R t u ^ 2) ≤ 1 := by
  have hb := greenCovariance_diagonal_lower_bound (p := p) (β := β) hphysical ht
  rw [← green_covariance_identity h ht ht,h.correlation_diagonal t ht] at hb
  exact hb

/-- All three assertions of Proposition 4.2, with precisely the CK equations
and the physical positivity supplied by Proposition 3.2 as hypotheses. -/
theorem green_covariance_proposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hphysical : PhysicalBounds d) :
    (∀ t s, 0 ≤ t → 0 ≤ s → d.C t s = greenCovariance p β d t s) ∧
    (∀ t, 0 ≤ t → d.C t 0 = d.R t 0) ∧
    (∀ t, 0 ≤ t → 2 * (∫ u in (0 : ℝ)..t, d.R t u ^ 2) ≤ 1) := by
  refine ⟨fun _ _ ht hs => green_covariance_identity h ht hs,?_,?_⟩
  · exact fun t ht => GreenCovariance.initial_correlation_eq_response h t ht
  · exact fun _ ht => response_row_sq_integral_le h hphysical ht

end SphericalAging.GreenCovarianceClosure
