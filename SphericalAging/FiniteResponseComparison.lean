module

public import SphericalAging.CovariancePSD
public import SphericalAging.BackwardResponse

public section

/-! Actual response domination on the finite CK horizon. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace SphericalAging.FiniteResponseComparison
open CKSpecification GreenCovariance GreenCovarianceClosure CKLocalExistence
open BackwardResponse FiniteGreenCovariance FiniteGreenCovarianceClosure

theorem correlation_derivative_right {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => d.C x u) (correlationSlope p β d t u) (Ici u) t := by
  apply (h.correlation_derivative t ⟨hu.trans hut,htT.le⟩ u ⟨hu,hut⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 t, x ≤ T from Iic_mem_nhds htT).filter_mono nhdsWithin_le_nhds] with x hx hxT
  exact ⟨hx,hxT⟩

theorem weighted_response_from_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {A : ℝ → ℝ} (hA : Continuous A) {a t : ℝ} (ha : 0 ≤ a) (ht : a ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => ∫ u in a..x, d.R x u * A u)
      ((∫ u in a..t, responseSlope p β d t u * A u) + A t) (Ici a) t := by
  let r : ℝ := (t+T)/2
  let F : ℝ → ℝ → ℝ := fun x u => clampedResponse d x u * A u
  let G : ℝ → ℝ → ℝ := fun x u => clampedResponseSlope p β d x u * A u
  have hR := FiniteGreenCovariance.clampedResponse_continuous h
  have hD := FiniteGreenCovariance.clampedResponseSlope_continuous h
  have hF : Continuous (Function.uncurry F) := hR.mul (hA.comp continuous_snd)
  have hG : Continuous (Function.uncurry G) := hD.mul (hA.comp continuous_snd)
  obtain ⟨M₀,hM₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) r) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image hG.norm.continuousOn
  let M : ℝ≥0 := ⟨max 0 M₀, le_max_left _ _⟩
  have hLip (u : ℝ) (hu : u ∈ Icc a t) :
      LipschitzOnWith M (fun x => F x u) (Iic r) := by
    have hl := causal_clamp_lipschitzOn (f := fun x => d.R x u * A u)
      (f' := fun x => responseSlope p β d x u * A u)
      (M := M) (a := u) (r := r) (hu.2.trans (by dsimp [r]; linarith))
      (fun x hx => (response_derivative_right h (ha.trans hu.1) hx.1
        (by have hxR := hx.2; dsimp [r] at hxR; linarith)).mul_const _)
      (fun x hx => by
        have hx0 := (ha.trans hu.1).trans hx.1
        have hur : u ≤ r := hu.2.trans (by dsimp [r]; linarith)
        have hb := hM₀ ⟨(x,u), ⟨⟨hx0,hx.2⟩,⟨ha.trans hu.1,hur⟩⟩,rfl⟩
        have he : G x u = responseSlope p β d x u * A u := by
          dsimp [G]
          rw [clampedResponseSlope_eq (ha.trans hu.1) hx.1]
        change ‖responseSlope p β d x u * A u‖ ≤ max 0 M₀
        rw [← he]
        exact hb.trans (le_max_right _ _))
    simpa only [F,clampedResponse,max_eq_right (ha.trans hu.1)] using hl
  have hDiff (u : ℝ) (hu : u ∈ Ico a t) :
      HasDerivAt (fun x => F x u) (G t u) t :=
    (FiniteGreenCovariance.clampedResponse_hasDerivAt h (ha.trans hu.1) hu.2 htT).mul_const _
  have hd := moving_integral_hasDerivAt_of_lipschitz_from (D := fun u => G t u) hF
    (hG.comp (continuous_const.prodMk continuous_id)) ht
    (show Iic r ∈ 𝓝 t from Iic_mem_nhds (by dsimp [r]; linarith)) hLip hDiff
  have hi : (∫ u in a..t, G t u) =
      ∫ u in a..t, responseSlope p β d t u * A u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp [G]
    rw [clampedResponseSlope_eq (ha.trans hu.1) hu.2]
  have hdiag : F t t = A t := by
    dsimp [F]
    rw [clampedResponse_eq (ha.trans ht) (le_refl _), h.response_diagonal t ⟨ha.trans ht,htT.le⟩,one_mul]
  rw [hi,hdiag] at hd
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp [F]
    rw [clampedResponse_eq (ha.trans hu.1) hu.2]
  · exact ht



theorem weighted_response_from_linear_derivative {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {A : ℝ → ℝ} (hA : Continuous A)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => ∫ u in a..x, clampedResponse d x u * A u)
      (-d.multiplier t * (∫ u in a..t, clampedResponse d t u * A u) +
        (∫ z in a..t, clampedMemory p β d t z *
          (∫ u in a..z, clampedResponse d z u * A u)) + A t) (Ici a) t := by
  have hd := weighted_response_from_hasDerivWithinAt h hA ha hat htT
  have hR := FiniteGreenCovariance.clampedResponse_continuous h
  have hK := FiniteGreenCovariance.clampedMemory_continuous h
  have hI : (∫ u in a..t, responseSlope p β d t u * A u) =
      -d.multiplier t * (∫ u in a..t, clampedResponse d t u * A u) +
        ∫ z in a..t, clampedMemory p β d t z *
          (∫ u in a..z, clampedResponse d z u * A u) := by
    have hmem : Continuous (fun u => ∫ z in u..t,
        clampedMemory p β d t z * clampedResponse d z u) := by
      have hc : Continuous (fun u => ∫ z in t..u,
          clampedMemory p β d t z * clampedResponse d z u) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          ((hK.comp (continuous_const.prodMk continuous_snd)).mul
            (hR.comp (continuous_snd.prodMk continuous_fst))) continuous_id
      convert hc.neg using 1
      funext u
      exact intervalIntegral.integral_symm (f := fun z =>
        clampedMemory p β d t z * clampedResponse d z u) t u
    calc
      (∫ u in a..t, responseSlope p β d t u * A u) =
          ∫ u in a..t, (-d.multiplier t * clampedResponse d t u +
            ∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) * A u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hat] at hu
        dsimp
        rw [responseSlope_linear_memory (ha.trans hu.1) hu.2]
      _ = -d.multiplier t * (∫ u in a..t, clampedResponse d t u * A u) +
          ∫ u in a..t, A u * (∫ z in u..t,
            clampedMemory p β d t z * clampedResponse d z u) := by
        have he : (fun u => (-d.multiplier t * clampedResponse d t u +
            ∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) * A u) =
            (fun u => -d.multiplier t * (clampedResponse d t u * A u) +
              A u * (∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u)) := by
          funext u; ring
        rw [he,intervalIntegral.integral_add
          (f := fun u => -d.multiplier t * (clampedResponse d t u * A u))
          (g := fun u => A u * (∫ z in u..t,
            clampedMemory p β d t z * clampedResponse d z u))
          ((((hR.comp (continuous_const.prodMk continuous_id)).mul hA).const_mul
            (-d.multiplier t)).intervalIntegrable a t)
          ((hA.mul hmem).intervalIntegrable a t),intervalIntegral.integral_const_mul]
      _ = _ := by rw [weighted_memory_from hR hK hA hat]
  rw [hI] at hd
  apply hd.congr_of_mem
  · intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp
    rw [clampedResponse_eq (ha.trans hu.1) hu.2]
  · exact hat



theorem ck_homogeneous_row_zero {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {f f' : ℝ → ℝ} {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (htT : t < T) (hf : Continuous f) (hzero : f a = 0)
    (hd : ∀ x, a ≤ x → x < T → HasDerivWithinAt f (f' x) (Ici a) x)
    (heq : ∀ x, a ≤ x → x < T → f' x = -d.multiplier x * f x +
      ∫ u in a..x, clampedMemory p β d x u * f u) : f t = 0 := by
  obtain ⟨L₀,hL₀⟩ := isCompact_Icc.bddAbove_image
    h.multiplier_continuous.norm.continuousOn
  have hK := FiniteGreenCovariance.clampedMemory_continuous h
  obtain ⟨S₀,hS₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) t ×ˢ Icc (0 : ℝ) t) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image hK.norm.continuousOn
  have hz := VolterraUniqueness.homogeneous_row_eq_zero f f' d.multiplier
    (clampedMemory p β d) a t (max 0 L₀) (max 0 S₀) hat
    (le_max_left _ _) (le_max_left _ _) hf hzero
    (fun x hx => (hd x hx.1 (hx.2.trans htT)).mono (fun _ hu => hx.1.trans hu))
    (fun x hx => heq x hx.1 (hx.2.trans htT))
    (fun x hx => by
      have hl := hL₀ ⟨x,⟨ha.trans hx.1,hx.2.le⟩,rfl⟩
      exact (show |d.multiplier x| ≤ L₀ by simpa only [Real.norm_eq_abs] using hl).trans
        (le_max_right _ _))
    (fun x _ => (((hK.comp (continuous_const.prodMk continuous_id)).mul hf).intervalIntegrable a x))
    (fun x hx u hu => by
      have hb := hS₀ ⟨(x,u),⟨⟨ha.trans hx.1,hx.2.le⟩,
        ⟨ha.trans hu.1,hu.2.trans hx.2.le⟩⟩,rfl⟩
      exact (show |clampedMemory p β d x u| ≤ S₀ by
        simpa only [Function.uncurry_apply_pair,Real.norm_eq_abs] using hb).trans (le_max_right _ _))
  exact hz t ⟨hat,le_refl t⟩


theorem clampedResponse_forward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => clampedResponse d x s)
      (-d.multiplier t * clampedResponse d t s +
        ∫ u in s..t, clampedMemory p β d t u * clampedResponse d u s) (Ici s) t := by
  have hd := response_derivative_right h hs hst htT
  rw [responseSlope_linear_memory hs hst] at hd
  apply hd.congr_of_mem
  · intro x hx
    exact clampedResponse_eq hs hx
  · exact hst


theorem ck_inhomogeneous_rows_eq {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {F G A : ℝ → ℝ} {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (htT : t < T) (hF : Continuous F) (hG : Continuous G)
    (hzero : F a = G a)
    (hFd : ∀ x, a ≤ x → x < T → HasDerivWithinAt F
      (-d.multiplier x * F x + (∫ u in a..x, clampedMemory p β d x u * F u) + A x) (Ici a) x)
    (hGd : ∀ x, a ≤ x → x < T → HasDerivWithinAt G
      (-d.multiplier x * G x + (∫ u in a..x, clampedMemory p β d x u * G u) + A x) (Ici a) x) :
    F t = G t := by
  let f : ℝ → ℝ := fun x => F x-G x
  let f' : ℝ → ℝ := fun x => -d.multiplier x * f x +
    ∫ u in a..x, clampedMemory p β d x u * f u
  have hder (x : ℝ) (hx : a ≤ x) (hxT : x < T) : HasDerivWithinAt f (f' x) (Ici a) x := by
    have hk : Continuous (fun u => clampedMemory p β d x u) :=
      (FiniteGreenCovariance.clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
    have hi : (∫ u in a..x, clampedMemory p β d x u * f u) =
        (∫ u in a..x, clampedMemory p β d x u * F u) -
          (∫ u in a..x, clampedMemory p β d x u * G u) := by
      simp only [f,mul_sub]
      exact intervalIntegral.integral_sub (f := fun u => clampedMemory p β d x u * F u)
        (g := fun u => clampedMemory p β d x u * G u)
        ((hk.mul hF).intervalIntegrable a x) ((hk.mul hG).intervalIntegrable a x)
    convert (hFd x hx hxT).sub (hGd x hx hxT) using 1
    dsimp [f']
    rw [hi]
    dsimp [f]
    ring
  have hz := ck_homogeneous_row_zero h ha hat htT (hF.sub hG)
    (show f a = 0 from sub_eq_zero.mpr hzero) hder (fun _ _ _ => rfl)
  exact sub_eq_zero.mp hz


theorem comparisonForcing_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (s : ℝ) : Continuous (comparisonForcing p β d s) := by
  have hi : Continuous (fun t => ∫ u in (0 : ℝ)..s,
      clampedMemory p β d t u * clampedCorrelation d u s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t u => clampedMemory p β d t u * clampedCorrelation d u s)
      ((FiniteGreenCovariance.clampedMemory_continuous h).mul
        ((FiniteGreenCovariance.clampedCorrelation_continuous h).comp (continuous_snd.prodMk continuous_const))) 0 s
  exact hi.add (FiniteGreenCovariance.coloredForcing_continuous h s)


theorem responseGap_row_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (s : ℝ) : Continuous (fun t => responseGap d t s) :=
  ((FiniteGreenCovariance.clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)).sub
    ((FiniteGreenCovariance.clampedResponse_continuous h).comp (continuous_id.prodMk continuous_const))


theorem responseGap_forward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => responseGap d x s)
      (-d.multiplier t * responseGap d t s +
        (∫ u in s..t, clampedMemory p β d t u * responseGap d u s) +
          comparisonForcing p β d s t) (Ici s) t := by
  have hdC := correlation_derivative_right h hs hst htT
  rw [correlationSlope_linear (hs.trans hst) hs] at hdC
  have hdCC : HasDerivWithinAt (fun x => clampedCorrelation d x s)
      (-d.multiplier t * clampedCorrelation d t s +
        (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u s) +
          coloredForcing p β d s t) (Ici s) t := by
    apply hdC.congr_of_mem
    · intro x hx
      exact clampedCorrelation_eq (hs.trans hx) hs
    · exact hst
  have hd := hdCC.sub (clampedResponse_forward_derivative h hs hst htT)
  have hK : Continuous (fun u => clampedMemory p β d t u) :=
    (FiniteGreenCovariance.clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
  have hC : Continuous (fun u => clampedCorrelation d u s) :=
    (FiniteGreenCovariance.clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
  have hR : Continuous (fun u => clampedResponse d u s) :=
    (FiniteGreenCovariance.clampedResponse_continuous h).comp (continuous_id.prodMk continuous_const)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hK.mul hC).intervalIntegrable 0 s) ((hK.mul hC).intervalIntegrable s t)
  have hsub : (∫ u in s..t, clampedMemory p β d t u * responseGap d u s) =
      (∫ u in s..t, clampedMemory p β d t u * clampedCorrelation d u s) -
        ∫ u in s..t, clampedMemory p β d t u * clampedResponse d u s := by
    simp only [responseGap,mul_sub]
    exact intervalIntegral.integral_sub
      (f := fun u => clampedMemory p β d t u * clampedCorrelation d u s)
      (g := fun u => clampedMemory p β d t u * clampedResponse d u s)
      ((hK.mul hC).intervalIntegrable s t) ((hK.mul hR).intervalIntegrable s t)
  convert hd using 1
  · rfl
  · rw [hsub]
    dsimp [responseGap,comparisonForcing]
    dsimp only [Pi.mul_apply] at hsplit
    nlinarith only [hsplit]


theorem response_gap_identity {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t < T) :
    d.C t s - d.R t s =
      ∫ u in s..t, d.R t u * comparisonForcing p β d s u := by
  have hF := comparisonForcing_continuous h s
  have hY : Continuous (fun x => ∫ u in s..x,
      clampedResponse d x u * comparisonForcing p β d s u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((FiniteGreenCovariance.clampedResponse_continuous h).mul (hF.comp continuous_snd)) continuous_id
  have he := ck_inhomogeneous_rows_eq h
    (F := fun x => responseGap d x s)
    (G := fun x => ∫ u in s..x, clampedResponse d x u * comparisonForcing p β d s u)
    (A := comparisonForcing p β d s) hs hst htT (responseGap_row_continuous h s) hY
    (by simp [responseGap,clampedCorrelation_eq hs hs,clampedResponse_eq hs (le_refl s),
      h.correlation_diagonal s ⟨hs,hst.trans htT.le⟩,h.response_diagonal s ⟨hs,hst.trans htT.le⟩])
    (fun x hx hxT => responseGap_forward_derivative h hs hx hxT)
    (fun x hx hxT => weighted_response_from_linear_derivative h hF hs hx hxT)
  rw [responseGap,clampedCorrelation_eq (hs.trans hst) hs,clampedResponse_eq hs hst] at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hst] at hu
  dsimp
  rw [clampedResponse_eq (hs.trans hu.1) hu.2]



theorem comparisonForcing_nonnegative {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ∈ Icc 0 T) :
    0 ≤ comparisonForcing p β d s t := by
  have hsT : s ∈ Icc 0 T := ⟨hs,hst.trans ht.2⟩
  have hpm : 0 ≤ (p : ℝ)-1 := by exact_mod_cast (show 0 ≤ (p : ℤ)-1 by have hp := h.spin_ge_three; omega)
  unfold comparisonForcing coloredForcing
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg hs
    intro u hu
    rw [clampedMemory_eq hu.1 (hu.2.trans hst),clampedCorrelation_eq hu.1 hs]
    unfold xiDoublePrime
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hpm) (pow_nonneg (hb.1 t ht u ⟨hu.1,hu.2.trans hsT.2⟩) _)))
        (hb.2 t ht u ⟨hu.1,hu.2.trans hst⟩))
      (hb.1 u ⟨hu.1,hu.2.trans hsT.2⟩ s hsT)
  · apply mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    apply intervalIntegral.integral_nonneg hs
    intro u hu
    rw [clampedResponse_eq hu.1 hu.2,clampedCorrelation_eq ht.1 hu.1]
    exact mul_nonneg (hb.2 s hsT u hu)
      (pow_nonneg (hb.1 t ht u ⟨hu.1,hu.2.trans hsT.2⟩) _)

/-- Actual finite-horizon response domination, with no upper-bound or PSD
premise. The final horizon follows by continuity of the physical rows. -/
theorem response_le_correlation {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) {s t : ℝ}
    (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) : d.R t s ≤ d.C t s := by
  have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
  by_cases hslt : s < T
  · let f : ℝ → ℝ := fun x => d.C x s-d.R x s
    have hf : Continuous f :=
      (h.correlation_continuous.comp (continuous_id.prodMk continuous_const)).sub
        (h.response_continuous.comp (continuous_id.prodMk continuous_const))
    have hZ : IsClosed {x | 0 ≤ f x} := isClosed_le continuous_const hf
    have hsub : Ico s T ⊆ {x | 0 ≤ f x} := by
      intro x hx
      change 0 ≤ d.C x s-d.R x s
      rw [response_gap_identity h hs.1 hx.1 hx.2]
      apply intervalIntegral.integral_nonneg hx.1
      intro u hu
      exact mul_nonneg (hb.2 x ⟨hs.1.trans hx.1,hx.2.le⟩ u ⟨hs.1.trans hu.1,hu.2⟩)
        (comparisonForcing_nonnegative h hb hs.1 hu.1 ⟨hs.1.trans hu.1,hu.2.trans hx.2.le⟩)
    have hc := hZ.closure_subset_iff.mpr hsub
    rw [closure_Ico hslt.ne] at hc
    have hh := hc (show t ∈ Icc s T from ⟨hs.2,ht.2⟩)
    dsimp [f] at hh
    linarith
  · have hsEq : s=T := le_antisymm hsT.2 (le_of_not_gt hslt)
    have htEq : t=T := le_antisymm ht.2 (hsEq ▸ hs.2)
    subst s
    subst t
    rw [h.response_diagonal T ⟨h.horizon_pos.le,le_refl T⟩,
      h.correlation_diagonal T ⟨h.horizon_pos.le,le_refl T⟩]

/-- All pointwise finite CK physical bounds, with entrywise positivity as
the sole sign input and actual covariance PSD giving C≤1. -/
theorem finite_response_correlation_bounds {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) {s t : ℝ}
    (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 t) :
    0 ≤ d.R t s ∧ d.R t s ≤ d.C t s ∧ d.C t s ≤ 1 :=
  ⟨hb.2 t ht s hs,response_le_correlation h hb ht hs,
    CovariancePSD.correlation_le_one h hb ht ⟨hs.1,hs.2.trans ht.2⟩⟩

end SphericalAging.FiniteResponseComparison
