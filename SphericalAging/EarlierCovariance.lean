module

public import SphericalAging.RecentForwardDerivative
public import SphericalAging.BackwardResponse

public section

/-! The genuine earlier-coordinate covariance equation, derived from the
proved Green identity and the actual forward response equation. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Topology InnerProductSpace
open Set MeasureTheory Filter
namespace SphericalAging.EarlierCovariance
open CKSpecification GreenCovariance GreenCovarianceClosure BackwardResponse

/-- The actual colored convolution, with continuous off-domain extensions. -/
@[expose] def coloredMemory (p : ℕ) (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, clampedResponse d t u*clampedCorrelation d u s^(p-1)

theorem coloredMemory_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (coloredMemory p d)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (((clampedResponse_continuous h).comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (((clampedCorrelation_continuous h).comp (continuous_snd.prodMk continuous_fst.snd)).pow (p-1)))
    continuous_fst

theorem coloredMemory_eq {p : ℕ} {d : CKData} {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    coloredMemory p d t s = ∫ u in (0 : ℝ)..t, d.R t u*d.C u s^(p-1) := by
  unfold coloredMemory
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [clampedResponse_eq hu.1 hu.2,clampedCorrelation_eq hu.1 hs]

theorem coloredMemory_nonneg {p : ℕ} {d : CKData} (hb : PhysicalBounds d)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) : 0 ≤ coloredMemory p d t s := by
  rw [coloredMemory_eq ht hs]
  exact intervalIntegral.integral_nonneg ht (fun u hu =>
    mul_nonneg (hb.2 t u hu.1 hu.2) (pow_nonneg (hb.1 u s hu.1 hs).1 _))

/-- The true finite colored rectangle is reordered into the earlier-time convolution. -/
theorem colored_rectangle {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (t s : ℝ) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
      clampedResponse d t u*clampedResponse d s v*clampedCorrelation d u v^(p-1)) =
    ∫ v in (0 : ℝ)..s, clampedResponse d s v*coloredMemory p d t v := by
  have hcont : Continuous (fun z : ℝ×ℝ => clampedResponse d t z.1*
      clampedResponse d s z.2*clampedCorrelation d z.1 z.2^(p-1)) := by
    exact (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_fst)).mul
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_snd))).mul
      ((clampedCorrelation_continuous h).pow (p-1))
  rw [rectangle_integral_swap (F := fun u v => clampedResponse d t u*clampedResponse d s v*
    clampedCorrelation d u v^(p-1)) hcont 0 t 0 s]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only [coloredMemory]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  ring

@[expose] def earlierForcing (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  2*clampedResponse d t s+β^2*(p : ℝ)*coloredMemory p d t s

theorem earlierForcing_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : Continuous (earlierForcing p β d t) := by
  exact (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).const_mul 2).add
    (((coloredMemory_continuous h).comp (continuous_const.prodMk continuous_id)).const_mul (β^2*(p : ℝ)))

/-- A full-line Green extension for differentiating the earlier coordinate. -/
@[expose] def earlierGreen (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  d.R t 0*d.R s 0+∫ v in (0 : ℝ)..s, clampedResponse d s v*earlierForcing p β d t v

theorem earlierGreen_eq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    earlierGreen p β d t s = d.C t s := by
  have ht := hs.trans hst
  rw [green_covariance_identity h ht hs,earlierGreen,greenCovariance,min_eq_right hst]
  have hR := clampedResponse_continuous h
  have hK := coloredMemory_continuous h
  have hwhite : IntervalIntegrable (fun v => clampedResponse d t v*clampedResponse d s v) volume 0 s :=
    ((hR.comp (continuous_const.prodMk continuous_id)).mul
      (hR.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 s
  have hcol : IntervalIntegrable (fun v => clampedResponse d s v*coloredMemory p d t v) volume 0 s :=
    ((hR.comp (continuous_const.prodMk continuous_id)).mul
      (hK.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 s
  have hi : (∫ v in (0 : ℝ)..s, clampedResponse d s v*earlierForcing p β d t v) =
      2*(∫ v in (0 : ℝ)..s, clampedResponse d t v*clampedResponse d s v)+
      β^2*(p : ℝ)*(∫ v in (0 : ℝ)..s, clampedResponse d s v*coloredMemory p d t v) := by
    have he : (fun v => clampedResponse d s v*earlierForcing p β d t v) =
      (fun v => 2*(clampedResponse d t v*clampedResponse d s v)+
        β^2*(p : ℝ)*(clampedResponse d s v*coloredMemory p d t v)) := by
      funext v; unfold earlierForcing; ring
    rw [he,intervalIntegral.integral_add (hwhite.const_mul 2) (hcol.const_mul (β^2*(p : ℝ))),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hw : (∫ v in (0 : ℝ)..s, clampedResponse d t v*clampedResponse d s v) =
      ∫ v in (0 : ℝ)..s, d.R t v*d.R s v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hs] at hv
    dsimp only
    rw [clampedResponse_eq hv.1 (hv.2.trans hst),clampedResponse_eq hv.1 hv.2]
  have hc : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
      clampedResponse d t u*clampedResponse d s v*clampedCorrelation d u v^(p-1)) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*d.C u v^(p-1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hs] at hv
    dsimp only
    rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2,
      clampedCorrelation_eq hu.1 hv.1]
  rw [hi,← colored_rectangle h t s,hw,hc]
  ring

@[expose] def earlierSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -d.multiplier s*d.C t s+2*d.R t s+
    (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*d.C t u)+
    β^2*(p : ℝ)*coloredMemory p d t s

/-- The genuine earlier-coordinate CK derivative, including its right endpoint at 0.
It is a theorem from the actual Green and response equations, not an input. -/
theorem correlation_earlier_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HasDerivWithinAt (fun x => d.C t x) (earlierSlope p β d t s) (Icc 0 t) s := by
  have h0 := (h.response_derivative s 0 le_rfl hs).const_mul (d.R t 0)
  have hi := weighted_response_from_linear_derivative h (earlierForcing_continuous h t) le_rfl hs
  have hd := (h0.add hi).mono (show Icc 0 t ⊆ Ici 0 from fun _ hx => hx.1)
  have hf : (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*
      (d.R t 0*clampedResponse d u 0+∫ v in (0 : ℝ)..u,
        clampedResponse d u v*earlierForcing p β d t v)) =
      ∫ u in (0 : ℝ)..s, clampedMemory p β d s u*d.C t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs] at hu
    dsimp only
    rw [clampedResponse_eq le_rfl hu.1,← earlierGreen,earlierGreen_eq h hu.1 (hu.2.trans hst)]
  have hm := responseSlope_linear_memory (p := p) (β := β) (d := d) le_rfl hs
  have hR := clampedResponse_continuous h
  have hK := clampedMemory_continuous h
  have hI1 : IntervalIntegrable
      (fun u => clampedMemory p β d s u*(d.R t 0*clampedResponse d u 0)) volume 0 s := by
    exact ((hK.comp (continuous_const.prodMk continuous_id)).mul
      ((hR.comp (continuous_id.prodMk continuous_const)).const_mul (d.R t 0))).intervalIntegrable 0 s
  have hI2 : IntervalIntegrable
      (fun u => clampedMemory p β d s u*
        (∫ v in (0 : ℝ)..u, clampedResponse d u v*earlierForcing p β d t v)) volume 0 s := by
    exact ((hK.comp (continuous_const.prodMk continuous_id)).mul
      (show Continuous (fun u => ∫ v in (0 : ℝ)..u, clampedResponse d u v*earlierForcing p β d t v) from
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (hR.mul ((earlierForcing_continuous h t).comp continuous_snd)) continuous_id)).intervalIntegrable 0 s
  have hg : d.R t 0*responseSlope p β d s 0+
      (-d.multiplier s*(∫ v in (0 : ℝ)..s, clampedResponse d s v*earlierForcing p β d t v)+
        (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*
          (∫ v in (0 : ℝ)..u, clampedResponse d u v*earlierForcing p β d t v))+
        earlierForcing p β d t s) = earlierSlope p β d t s := by
    rw [hm,clampedResponse_eq le_rfl hs]
    have hsum : (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*d.C t u) =
      d.R t 0*(∫ u in (0 : ℝ)..s, clampedMemory p β d s u*clampedResponse d u 0)+
      (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*
        (∫ v in (0 : ℝ)..u, clampedResponse d u v*earlierForcing p β d t v)) := by
      rw [← hf]
      simp_rw [mul_add]
      rw [intervalIntegral.integral_add hI1 hI2]
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      ring
    unfold earlierSlope
    rw [hsum,← earlierGreen_eq h hs hst]
    unfold earlierGreen earlierForcing
    rw [clampedResponse_eq hs hst]
    ring
  rw [hg] at hd
  apply hd.congr_of_mem
  · intro x hx
    exact (earlierGreen_eq h hx.1 hx.2).symm
  · exact ⟨hs,hst⟩

/-- On the open causal triangle this is an ordinary earlier derivative. -/
theorem correlation_earlier_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 < s) (hst : s < t) :
    HasDerivAt (fun x => d.C t x) (earlierSlope p β d t s) s :=
  (correlation_earlier_hasDerivWithinAt h hs.le hst.le).hasDerivAt
    (Icc_mem_nhds hs hst)

/-- The same genuine equation gives the right derivative at the initial endpoint. -/
theorem correlation_earlier_initial_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun x => d.C t x) (earlierSlope p β d t 0) (Ici 0) 0 := by
  apply (correlation_earlier_hasDerivWithinAt h le_rfl ht.le).mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds ht))

/-- Exact expansion in the manuscript's normalization. -/
theorem earlierSlope_eq {p : ℕ} {β : ℝ} {d : CKData} {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    earlierSlope p β d t s = -d.multiplier s*d.C t s+2*d.R t s+
      β^2*(p : ℝ)*((p : ℝ)-1)*
        (∫ u in (0 : ℝ)..s, d.C s u^(p-2)*d.R s u*d.C t u)+
      β^2*(p : ℝ)*(∫ u in (0 : ℝ)..t, d.R t u*d.C u s^(p-1)) := by
  unfold earlierSlope
  rw [coloredMemory_eq (hs.trans hst) hs]
  congr 1
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hs] at hu
  dsimp only
  rw [clampedMemory_eq hu.1 hu.2]
  unfold xiDoublePrime
  ring

@[expose] def clampedEarlierSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -clampedMultiplier d s*clampedCorrelation d t s+2*clampedResponse d t s+
    (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*clampedCorrelation d t u)+
    β^2*(p : ℝ)*coloredMemory p d t s

theorem clampedEarlierSlope_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (clampedEarlierSlope p β d)) := by
  have hm := clampedMultiplier_continuous h
  have hc := clampedCorrelation_continuous h
  have hr := clampedResponse_continuous h
  have hk := clampedMemory_continuous h
  have hi : Continuous (fun z : ℝ×ℝ => ∫ u in (0 : ℝ)..z.2,
      clampedMemory p β d z.2 u*clampedCorrelation d z.1 u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((hk.comp (continuous_fst.snd.prodMk continuous_snd)).mul
        (hc.comp (continuous_fst.fst.prodMk continuous_snd))) continuous_snd
  exact (((hm.comp continuous_snd).neg.mul hc).add (hr.const_mul 2)).add hi |>.add
    ((coloredMemory_continuous h).const_mul (β^2*(p : ℝ)))

theorem clampedEarlierSlope_eq {p : ℕ} {β : ℝ} {d : CKData} {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    clampedEarlierSlope p β d t s = earlierSlope p β d t s := by
  unfold clampedEarlierSlope earlierSlope clampedMultiplier
  rw [max_eq_right hs,clampedCorrelation_eq (hs.trans hst) hs,clampedResponse_eq hs hst]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hs] at hu
  dsimp only
  rw [clampedCorrelation_eq (hs.trans hst) hu.1]

/-- The actual earlier derivative is jointly continuous on every causal triangle. -/
theorem earlierSlope_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    ContinuousOn (Function.uncurry (earlierSlope p β d)) causalTriangle := by
  apply (clampedEarlierSlope_continuous h).continuousOn.congr
  intro z hz
  exact (clampedEarlierSlope_eq (p := p) (β := β) (d := d) hz.1 hz.2).symm

end SphericalAging.EarlierCovariance
