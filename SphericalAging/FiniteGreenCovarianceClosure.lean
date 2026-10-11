module

public import SphericalAging.FiniteGreenCovariance

public section

/-! Finite-horizon closure of the actual CK Green covariance identity. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.FiniteGreenCovarianceClosure
open CKSpecification GreenCovariance GreenCovarianceClosure CKLocalExistence FiniteGreenCovariance

theorem correlation_diagonal_slope {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    correlationSlope p β d t t = -1 := by
  have hc : ContinuousOn (fun u => d.C t u) (Icc 0 t) :=
    (h.correlation_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hr : ContinuousOn (fun u => d.R t u) (Icc 0 t) :=
    (h.response_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hfirst : IntervalIntegrable
      (fun u => xiDoublePrime p (d.C t u)*d.R t u*d.C t u) volume 0 t :=
    (show ContinuousOn (fun u => xiDoublePrime p (d.C t u)*d.R t u*d.C t u)
      (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact ((((hc.pow (p-2)).const_mul ((p:ℝ)*((p:ℝ)-1))).mul hr).mul hc)).intervalIntegrable
  have hsecond : IntervalIntegrable (fun u => xiPrime p (d.C t u)*d.R t u) volume 0 t :=
    (show ContinuousOn (fun u => xiPrime p (d.C t u)*d.R t u) (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact ((hc.pow (p-1)).const_mul (p:ℝ)).mul hr).intervalIntegrable
  have hsym : (∫ u in 0..t, xiDoublePrime p (d.C t u)*d.R t u*d.C u t) =
      ∫ u in 0..t, xiDoublePrime p (d.C t u)*d.R t u*d.C t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [h.correlation_symmetric u t]
  have hsum : (∫ u in 0..t, xiDoublePrime p (d.C t u)*d.R t u*d.C t u)+
      (∫ u in 0..t, xiPrime p (d.C t u)*d.R t u) = (p:ℝ)^2*memoryMass p d t := by
    rw [← intervalIntegral.integral_add hfirst hsecond, memoryMass,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    have hi := xi_multiplier_integrand p h.spin_ge_three (d.C t u)
    have him := congrArg (fun x : ℝ => x*d.R t u) hi
    nlinarith only [him]
  unfold correlationSlope
  rw [h.correlation_diagonal t ⟨ht,htT⟩, hsym, h.multiplier_eq t ⟨ht,htT⟩]
  nlinarith only [hsum]

theorem clampedCorrelation_offdiag_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (htT : t < T) :
    HasDerivAt (fun x => clampedCorrelation d x s)
      (-d.multiplier t * clampedCorrelation d t s +
        (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u s) +
        coloredForcing p β d s t) t := by
  have ht : 0 ≤ t := hs.trans hst.le
  have hd := (h.correlation_derivative t ⟨hs.trans hst.le,htT.le⟩ s ⟨hs,hst.le⟩).hasDerivAt (Icc_mem_nhds hst htT)
  rw [correlationSlope_linear ht hs] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (lt_of_le_of_lt hs hst)] with x hx
  exact clampedCorrelation_eq hx.le hs


theorem clampedCorrelation_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => clampedCorrelation d x x) 0 (Ici 0) t  := by
  apply (hasDerivWithinAt_const t (Ici 0) (1 : ℝ)).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds htT).filter_mono nhdsWithin_le_nhds] with x hx hxT
    rw [clampedCorrelation_eq hx hx]
    exact h.correlation_diagonal x ⟨hx,hxT.le⟩
  · rw [clampedCorrelation_eq ht ht]
    exact h.correlation_diagonal t ⟨ht,htT.le⟩


theorem clampedCorrelation_diagonal_cancellation {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    -2 * d.multiplier t * clampedCorrelation d t t +
      2 * (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u t) +
      2 * coloredForcing p β d t t + 2 = 0 := by
  have hs := correlation_diagonal_slope h ht htT.le
  rw [correlationSlope_linear ht ht] at hs
  nlinarith only [hs]


theorem covarianceError_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (covarianceError p β d)) :=
  (clampedGreen_continuous h).sub (clampedCorrelation_continuous h)


theorem covarianceError_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (t s : ℝ) :
    covarianceError p β d t s = covarianceError p β d s t := by
  unfold covarianceError
  rw [clampedGreen_symmetric h t s]
  have he : clampedCorrelation d t s = clampedCorrelation d s t :=
    h.correlation_symmetric _ _
  rw [he]


theorem covarianceError_zero_initial {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : covarianceError p β d 0 0 = 0 := by
  have hG : clampedGreen p β d 0 0 = 1 := by
    rw [clampedGreen_eq (le_refl 0) (le_refl 0),
      greenCovariance_initial (h.response_diagonal 0 ⟨le_refl 0,h.horizon_pos.le⟩) 0 (le_refl 0),
      h.response_diagonal 0 ⟨le_refl 0,h.horizon_pos.le⟩]
  unfold covarianceError
  rw [hG,clampedCorrelation_eq (le_refl 0) (le_refl 0),h.correlation_diagonal 0 ⟨le_refl 0,h.horizon_pos.le⟩]
  ring


theorem covarianceError_memory_eq {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (t s : ℝ) :
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
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (htT : t < T) :
    HasDerivAt (fun x => covarianceError p β d x s)
      (TriangleUniqueness.offdiagSlope (covarianceError p β d) d.multiplier
        (clampedMemory p β d) t s) t := by
  have hd := (clampedGreen_offdiag_hasDerivAt h hs hst htT).sub
    (clampedCorrelation_offdiag_hasDerivAt h hs hst htT)
  convert hd using 1
  · rfl
  · unfold TriangleUniqueness.offdiagSlope
    rw [covarianceError_memory_eq h t s]
    unfold covarianceError
    ring


theorem covarianceError_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => covarianceError p β d x x)
      (TriangleUniqueness.diagonalSlope (covarianceError p β d) d.multiplier
        (clampedMemory p β d) t) (Ici 0) t := by
  have hd := (clampedGreen_diagonal_hasDerivWithinAt h ht htT).sub
    (clampedCorrelation_diagonal_hasDerivWithinAt h ht htT)
  have hc := clampedCorrelation_diagonal_cancellation h ht htT
  convert hd using 1
  · rfl
  · unfold TriangleUniqueness.diagonalSlope
    rw [covarianceError_memory_eq h t t]
    unfold covarianceError
    nlinarith only [hc]



theorem covarianceError_eq_zero_lt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (htT : t < T) (hsT : s < T) :
    covarianceError p β d t s = 0 := by
  let U : ℝ := max t s
  have hT : 0 ≤ U := ht.trans (le_max_left _ _)
  obtain ⟨L₀,hL₀⟩ := isCompact_Icc.bddAbove_image
    h.multiplier_continuous.norm.continuousOn
  obtain ⟨S₀,hS₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) U ×ˢ Icc (0 : ℝ) U) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image (clampedMemory_continuous h).norm.continuousOn
  have hz := TriangleUniqueness.homogeneous_triangle_eq_zero
    (D := covarianceError p β d) (K := clampedMemory p β d) (ell := d.multiplier)
    (T := U) (L := max 0 L₀) (S := max 0 S₀) hT (le_max_left _ _) (le_max_left _ _)
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
    (fun x hx _ hs hst => covarianceError_offdiag_hasDerivAt h hs.1 hst
      (lt_of_le_of_lt hx.2 (max_lt htT hsT)))
    (fun x hx => covarianceError_diagonal_hasDerivWithinAt h hx.1
      (lt_of_le_of_lt hx.2 (max_lt htT hsT)))
  exact hz t ⟨ht,le_max_left _ _⟩ s ⟨hs,le_max_right _ _⟩



/-- Finite-horizon Green identity including the final horizon. The identity
is first proved on the open horizon by actual triangle uniqueness, and
joint continuity supplies the closed boundary. -/
theorem covarianceError_eq_zero {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    covarianceError p β d t s = 0 := by
  let Z : Set (ℝ × ℝ) := {z | covarianceError p β d z.1 z.2 = 0}
  have hZ : IsClosed Z :=
    isClosed_eq (covarianceError_continuous h) continuous_const
  have hsub : Ico (0 : ℝ) T ×ˢ Ico (0 : ℝ) T ⊆ Z := by
    intro z hz
    exact covarianceError_eq_zero_lt h hz.1.1 hz.2.1 hz.1.2 hz.2.2
  have hclosure : closure (Ico (0 : ℝ) T ×ˢ Ico (0 : ℝ) T) =
      Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T := by
    rw [closure_prod_eq,closure_Ico h.horizon_pos.ne]
  have hc := hZ.closure_subset_iff.mpr hsub
  rw [hclosure] at hc
  exact hc (show (t,s) ∈ Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T from ⟨ht,hs⟩)

theorem green_covariance_identity {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    d.C t s = greenCovariance p β d t s := by
  have hz := covarianceError_eq_zero h ht hs
  unfold covarianceError at hz
  have he := sub_eq_zero.mp hz
  rw [clampedGreen_eq ht.1 hs.1,clampedCorrelation_eq ht.1 hs.1] at he
  exact he.symm

/-- Entrywise positivity is kept distinct from positive semidefiniteness
and from the eventual correlation upper bound. -/
@[expose] def NonnegativeOnHorizon (T : ℝ) (d : CKData) : Prop :=
  (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, 0 ≤ d.C t s) ∧
    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, 0 ≤ d.R t s)

/-- The squared response-row bound needs only entrywise nonnegativity,
not an assumed correlation bound C≤1 or a PSD hypothesis. -/
theorem response_row_sq_integral_le {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    2*(∫ u in (0 : ℝ)..t, d.R t u ^ 2) ≤ 1 := by
  have hcolored : 0 ≤ ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
      d.R t u * d.R t v * d.C u v ^ (p-1) := by
    apply intervalIntegral.integral_nonneg ht.1
    intro u hu
    apply intervalIntegral.integral_nonneg ht.1
    intro v hv
    exact mul_nonneg (mul_nonneg (hb.2 t ht u hu) (hb.2 t ht v hv))
      (pow_nonneg (hb.1 u ⟨hu.1,hu.2.trans ht.2⟩ v ⟨hv.1,hv.2.trans ht.2⟩) _)
  have hcoef : 0 ≤ β^2*(p : ℝ) := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hi : (∫ u in (0 : ℝ)..t, d.R t u * d.R t u) =
      ∫ u in (0 : ℝ)..t, d.R t u ^ 2 := by simp only [pow_two]
  have hdiag := green_covariance_identity h ht ht
  rw [h.correlation_diagonal t ht] at hdiag
  unfold greenCovariance at hdiag
  rw [min_self,hi] at hdiag
  nlinarith [sq_nonneg (d.R t 0),mul_nonneg hcoef hcolored]

/-- The explicit untruncated Picard solution has the exact Green covariance
and its deterministic squared response row bound on its whole local horizon. -/
theorem local_picard_green_and_row_bound {p : ℕ} (hp : 3 ≤ p) {β : ℝ} (hβ : 0 < β) :
    ∃ d : CKData, CKOnHorizon p β (localHorizon p β) d ∧
      (∀ t ∈ Icc 0 (localHorizon p β), ∀ s ∈ Icc 0 (localHorizon p β),
        d.C t s = greenCovariance p β d t s) ∧
      (∀ t ∈ Icc 0 (localHorizon p β), 2*(∫ u in (0 : ℝ)..t, d.R t u^2) ≤ 1) := by
  obtain ⟨d,hd,hbounds⟩ := ck_local_existence hp hβ
  have hb : NonnegativeOnHorizon (localHorizon p β) d := by
    constructor
    · intro t _ s _
      have hh := (hbounds t s).1.1
      linarith
    · intro t _ s _
      have hh := (hbounds t s).2.1
      linarith
  exact ⟨d,hd,fun _ ht _ hs => green_covariance_identity hd ht hs,
    fun _ ht => response_row_sq_integral_le hd hb ht⟩


theorem initial_correlation_eq_response {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t : ℝ} (ht : t ∈ Icc 0 T) : d.C t 0 = d.R t 0 := by
  rw [green_covariance_identity h ht ⟨le_refl 0,h.horizon_pos.le⟩]
  exact greenCovariance_initial (h.response_diagonal 0 ⟨le_refl 0,h.horizon_pos.le⟩) t ht.1

/-- Entire Proposition 4.2 on the actual finite CK horizon. The only sign
input is entrywise nonnegativity; PSD and C≤1 are not assumed. -/
theorem finite_green_covariance_proposition {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) :
    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s=greenCovariance p β d t s) ∧
    (∀ t ∈ Icc 0 T, d.C t 0=d.R t 0) ∧
    (∀ t ∈ Icc 0 T, 2*(∫ u in (0 : ℝ)..t, d.R t u^2) ≤ 1) :=
  ⟨fun _ ht _ hs => green_covariance_identity h ht hs,
    fun _ ht => initial_correlation_eq_response h ht,
    fun _ ht => response_row_sq_integral_le h hb ht⟩

end SphericalAging.FiniteGreenCovarianceClosure
