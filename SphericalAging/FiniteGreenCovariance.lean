module

public import SphericalAging.GreenCovarianceClosure
public import SphericalAging.CKLocalExistence

public section

/-! Localized Green covariance calculations for genuine CK solutions on a
finite horizon. The equations are used only strictly before the horizon;
continuity supplies the final boundary values. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace SphericalAging.FiniteGreenCovariance
open CKSpecification GreenCovariance CKLocalExistence

theorem response_derivative_right {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => d.R x u) (responseSlope p β d t u) (Ici u) t := by
  apply (h.response_derivative t ⟨hu.trans hut,htT.le⟩ u ⟨hu,hut⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 t, x ≤ T from Iic_mem_nhds htT).filter_mono nhdsWithin_le_nhds] with x hx hxT
  exact ⟨hx,hxT⟩

theorem clampedResponse_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (clampedResponse d)) :=
  h.response_continuous.comp
    (show Continuous (fun z : ℝ × ℝ => (max z.1 (max 0 z.2),max 0 z.2)) by fun_prop)


theorem clampedCorrelation_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (clampedCorrelation d)) :=
  h.correlation_continuous.comp
    (show Continuous (fun z : ℝ × ℝ => (max 0 z.1,max 0 z.2)) by fun_prop)


theorem clampedResponseSlope_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (clampedResponseSlope p β d)) :=
  h.response_slope_continuous.comp
    (show Continuous (fun z : ℝ × ℝ => (max z.1 (max 0 z.2),max 0 z.2)) by fun_prop)


theorem response_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t u : ℝ} (hu : 0 ≤ u) (hut : u < t) (htT : t < T) :
    HasDerivAt (fun x => d.R x u) (responseSlope p β d t u) t :=
  (response_derivative_right h hu hut.le htT).hasDerivAt (Ici_mem_nhds hut)


theorem clampedResponse_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t u : ℝ} (hu : 0 ≤ u) (hut : u < t) (htT : t < T) :
    HasDerivAt (fun x => clampedResponse d x u)
      (clampedResponseSlope p β d t u) t := by
  have hd := response_hasDerivAt h hu hut htT
  have he : (fun x => clampedResponse d x u) =ᶠ[𝓝 t] (fun x => d.R x u) := by
    filter_upwards [Ioi_mem_nhds hut] with x hx
    exact clampedResponse_eq hu hx.le
  simpa [clampedResponseSlope, max_eq_right hu, max_eq_left hut.le] using
    hd.congr_of_eventuallyEq he


theorem white_integral_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (htT : t < T) :
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
    (show t ∈ Ioo s T by constructor; exact hst; linarith)
  intro y hy u hu
  exact (clampedResponse_hasDerivAt h hu.1 (lt_of_le_of_lt hu.2 hy.1) hy.2).mul_const _



theorem clampedGreen_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (clampedGreen p β d)) := by
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
    {T : ℝ} (h : CKOnHorizon p β T d) :
    ContinuousOn (Function.uncurry (greenCovariance p β d)) timeQuadrant := by
  apply (clampedGreen_continuous h).continuousOn.congr
  intro z hz
  exact (clampedGreen_eq hz.1 hz.2).symm


theorem clampedGreen_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (t s : ℝ) :
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
      h.correlation_symmetric _ _
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
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    greenCovariance p β d t s = greenCovariance p β d s t := by
  rw [← clampedGreen_eq ht hs, ← clampedGreen_eq hs ht]
  exact clampedGreen_symmetric h t s


theorem clampedMemory_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) :
    Continuous (Function.uncurry (clampedMemory p β d)) := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  unfold clampedMemory xiDoublePrime
  exact (continuous_const.mul ((continuous_const.mul continuous_const).mul (hC.pow _))).mul hR


theorem white_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => ∫ u in (0 : ℝ)..x, d.R x u ^ 2)
      ((∫ u in (0 : ℝ)..t, 2 * d.R t u * responseSlope p β d t u) + 1) (Ici 0) t := by
  let r : ℝ := (t+T)/2
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
        convert (response_derivative_right h hu.1 hx.1 (by have hxr := hx.2; dsimp [r] at hxr; linarith)).pow 2 using 1; norm_num)
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
    convert (clampedResponse_hasDerivAt h hu.1 hu.2 htT).pow 2 using 1; norm_num [F, G]
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
    rw [clampedResponse_eq ht (le_refl _), h.response_diagonal t ⟨ht,htT.le⟩]
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



theorem weighted_response_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {A : ℝ → ℝ} (hA : Continuous A) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => ∫ u in (0 : ℝ)..x, d.R x u * A u)
      ((∫ u in (0 : ℝ)..t, responseSlope p β d t u * A u) + A t) (Ici 0) t := by
  let r : ℝ := (t+T)/2
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
      (fun x hx => (response_derivative_right h hu.1 hx.1 (by have hxr := hx.2; dsimp [r] at hxr; linarith)).mul_const _)
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
    (clampedResponse_hasDerivAt h hu.1 hu.2 htT).mul_const _
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
    rw [clampedResponse_eq ht (le_refl _), h.response_diagonal t ⟨ht,htT.le⟩,one_mul]
  rw [hi,hdiag] at hd
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp [F]
    rw [clampedResponse_eq hu.1 hu.2]
  · exact ht


theorem coloredForcing_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (s : ℝ) : Continuous (coloredForcing p β d s) := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hR.comp (continuous_const.prodMk continuous_snd)).mul (hC.pow _)


theorem colored_term_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => ∫ u in (0 : ℝ)..x,
        d.R x u * coloredForcing p β d s u)
      ((∫ u in (0 : ℝ)..t, responseSlope p β d t u * coloredForcing p β d s u) +
        coloredForcing p β d s t) (Ici 0) t :=
  weighted_response_hasDerivWithinAt h (coloredForcing_continuous h s) ht htT



theorem symmetric_diagonal_hasDerivWithinAt
    {F H : ℝ → ℝ → ℝ} {T : ℝ} (hH : Continuous (Function.uncurry H))
    (hSym : ∀ x y, 0 ≤ x → 0 ≤ y → F x y = F y x)
    (hPartial : ∀ x y, 0 ≤ x → 0 ≤ y → x < T → y < T →
      HasDerivWithinAt (fun z => F z y) (H x y) (Ici 0) x)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => F x x) (2 * H t t) (Ici 0) t := by
  have hright := (hPartial t t ht ht htT htT).isLittleO
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
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds htT).filter_mono nhdsWithin_le_nhds,
      (show ∀ᶠ x in 𝓝 t, x ∈ Metric.ball t δ from
        Metric.ball_mem_nhds t hδ).filter_mono nhdsWithin_le_nhds] with x hx hxT hxball
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
      have hd := (hPartial v x (hnonneg v hv) hx (by
        rcases mem_uIcc.mp hv with hv | hv <;> linarith) hxT).sub
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



theorem coloredForcing_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (coloredForcing p β d)) := by
  have hR := clampedResponse_continuous h
  have hC := clampedCorrelation_continuous h
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hR.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      ((hC.comp (continuous_fst.snd.prodMk continuous_snd)).pow _)
  · exact continuous_fst


theorem coloredTerm_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (coloredTerm p β d)) := by
  have hR := clampedResponse_continuous h
  have hA := coloredForcing_joint_continuous h
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hR.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hA.comp (continuous_fst.snd.prodMk continuous_snd))
  · exact continuous_fst


theorem coloredPartial_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (coloredPartial p β d)) := by
  have hD := clampedResponseSlope_continuous h
  have hA := coloredForcing_joint_continuous h
  apply Continuous.add
  · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (hD.comp (continuous_fst.fst.prodMk continuous_snd)).mul
        (hA.comp (continuous_fst.snd.prodMk continuous_snd))
    · exact continuous_fst
  · exact hA.comp (continuous_snd.prodMk continuous_fst)


theorem coloredTerm_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (t s : ℝ) :
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
    h.correlation_symmetric _ _
  rw [hsym]
  ring


theorem coloredTerm_partial_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => coloredTerm p β d x s)
      (coloredPartial p β d t s) (Ici 0) t := by
  have hd := colored_term_hasDerivWithinAt h s ht htT
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


theorem coloredTerm_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => coloredTerm p β d x x)
      (2 * coloredPartial p β d t t) (Ici 0) t :=
  symmetric_diagonal_hasDerivWithinAt (coloredPartial_joint_continuous h)
    (fun t s _ _ => coloredTerm_symmetric h t s)
    (fun _t s ht _ htT _ => coloredTerm_partial_hasDerivWithinAt h s ht htT) ht htT



theorem initialPartial_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (initialPartial p β d)) := by
  exact ((clampedResponseSlope_continuous h).comp (continuous_fst.prodMk continuous_const)).mul
    ((clampedResponse_continuous h).comp (continuous_snd.prodMk continuous_const))


theorem initialTerm_partial_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => initialTerm d x s) (initialPartial p β d t s) (Ici 0) t := by
  have hd := (response_derivative_right h (le_refl 0) ht htT).mul_const (clampedResponse d s 0)
  rw [← clampedResponseSlope_eq (le_refl 0) ht] at hd
  apply hd.congr_of_mem
  · intro x hx
    dsimp [initialTerm]
    rw [clampedResponse_eq (le_refl 0) hx]
  · exact ht


theorem initialTerm_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => initialTerm d x x) (2 * initialPartial p β d t t) (Ici 0) t :=
  symmetric_diagonal_hasDerivWithinAt (initialPartial_joint_continuous h)
    (fun _ _ _ _ => mul_comm _ _)
    (fun _ s ht _ htT _ => initialTerm_partial_hasDerivWithinAt h s ht htT) ht htT


theorem whiteTerm_offdiag_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (htT : t < T) :
    HasDerivAt (fun x => whiteTerm d x s)
      (2 * ∫ u in (0 : ℝ)..s, clampedResponseSlope p β d t u * clampedResponse d s u) t := by
  have hd := (white_integral_hasDerivAt h hs hst htT).const_mul 2
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hst] with x hx
  dsimp [whiteTerm]
  rw [min_eq_right hx.le]


theorem whiteTerm_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => whiteTerm d x x)
      (2 * ((∫ u in (0 : ℝ)..t,
        2 * clampedResponse d t u * clampedResponseSlope p β d t u) + 1)) (Ici 0) t := by
  have hd := (white_diagonal_hasDerivWithinAt h ht htT).const_mul 2
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



theorem responseSlope_integral_identity {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {A : ℝ → ℝ} (hA : Continuous A)
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
    {T : ℝ} (h : CKOnHorizon p β T d) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
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
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
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
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) :
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
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (initialTerm d)) := by
  have hR := clampedResponse_continuous h
  exact (hR.comp (continuous_fst.prodMk continuous_const)).mul
    (hR.comp (continuous_snd.prodMk continuous_const))


theorem whiteTerm_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (whiteTerm d)) := by
  have hR := clampedResponse_continuous h
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hR.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hR.comp (continuous_fst.snd.prodMk continuous_snd))
  · exact continuous_fst.min continuous_snd


theorem green_memory_decomposition {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) (t s : ℝ) :
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


theorem clampedGreen_offdiag_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (htT : t < T) :
    HasDerivAt (fun x => clampedGreen p β d x s)
      (-d.multiplier t * clampedGreen p β d t s +
        (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedGreen p β d z s) +
        coloredForcing p β d s t) t := by
  have ht : 0 ≤ t := hs.trans hst.le
  have htpos : 0 < t := lt_of_le_of_lt hs hst
  have hi := (initialTerm_partial_hasDerivWithinAt h s ht htT).hasDerivAt (Ici_mem_nhds htpos)
  have hw := whiteTerm_offdiag_hasDerivAt h hs hst htT
  have hc := (coloredTerm_partial_hasDerivWithinAt h s ht htT).hasDerivAt (Ici_mem_nhds htpos)
  convert (hi.add hw).add hc using 1
  · funext x
    exact clampedGreen_decomposition p β d x s
  · rw [initialPartial_linear s ht,white_offdiag_slope_linear h hs hst.le,
      coloredPartial_linear h s ht,green_memory_decomposition h t s,clampedGreen_decomposition]
    ring


theorem clampedGreen_diagonal_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℝ} (h : CKOnHorizon p β T d) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt (fun x => clampedGreen p β d x x)
      (-2 * d.multiplier t * clampedGreen p β d t t +
        2 * (∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedGreen p β d z t) +
        2 * coloredForcing p β d t t + 2) (Ici 0) t := by
  have hi := initialTerm_diagonal_hasDerivWithinAt h ht htT
  have hw := whiteTerm_diagonal_hasDerivWithinAt h ht htT
  have hc := coloredTerm_diagonal_hasDerivWithinAt h ht htT
  convert (hi.add hw).add hc using 1
  · funext x
    exact clampedGreen_decomposition p β d x x
  · rw [initialPartial_linear t ht,white_diagonal_slope_linear h ht,
      coloredPartial_linear h t ht,green_memory_decomposition h t t,clampedGreen_decomposition]
    ring


end SphericalAging.FiniteGreenCovariance
