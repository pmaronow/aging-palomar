module

public import SphericalAging.ProjectedTreeDrift

public section

/-! The genuine finite triple-integral rearrangement in the reflected stationary
rectangle equation. All swaps follow from actual compact continuity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace SphericalAging.ReflectionFiniteFubini

/-- Compact three-variable Fubini over the region w≤U and w≤V. -/
theorem triple_min_swap {F : ℝ → ℝ → ℝ → ℝ}
    (hF : Continuous (fun z : ℝ × (ℝ×ℝ) => F z.1 z.2.1 z.2.2))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ w in (0 : ℝ)..min a b, ∫ U in w..a, ∫ V in w..b, F w U V) =
      ∫ U in (0 : ℝ)..a, ∫ V in (0 : ℝ)..b, ∫ w in (0 : ℝ)..min U V, F w U V := by
  have hG : Continuous (fun z : ℝ×ℝ => ∫ V in z.1..b, F z.1 z.2 V) := by
    have hcomp : Continuous (fun z : (ℝ×ℝ)×ℝ => F z.1.1 z.1.2 z.2) :=
      hF.comp (show Continuous (fun z : (ℝ×ℝ)×ℝ => (z.1.1,(z.1.2,z.2))) by fun_prop)
    have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := b) (f := fun z : ℝ×ℝ => fun V => F z.1 z.2 V)
        hcomp continuous_fst
    apply hi.neg.congr
    intro z
    exact (intervalIntegral.integral_symm (μ := volume) (f := fun V => F z.1 z.2 V) b z.1).symm
  rw [TriangleUniqueness.triangular_integral_swap (F := fun w U => ∫ V in w..b, F w U V) hG (le_min ha hb) (min_le_left _ _)]
  apply intervalIntegral.integral_congr
  intro U hU
  dsimp only
  rw [uIcc_of_le ha] at hU
  have hFU : Continuous (fun z : ℝ×ℝ => F z.1 U z.2) :=
    hF.comp (show Continuous (fun z : ℝ×ℝ => (z.1,(U,z.2))) by fun_prop)
  rw [TriangleUniqueness.triangular_integral_swap (F := fun w V => F w U V) hFU
    (le_min hU.1 (le_min ha hb)) ((min_le_right _ _).trans (min_le_right _ _))]
  apply intervalIntegral.integral_congr
  intro V hV
  dsimp only
  rw [uIcc_of_le hb] at hV
  have hm : min V (min U (min a b))=min U V := by
    apply le_antisymm
    · exact le_min ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)
    · exact le_min (min_le_right _ _) (le_min (min_le_left _ _)
        (le_min ((min_le_left U V).trans hU.2) ((min_le_right U V).trans hV.2)))
  rw [hm]

/-- The exact affine translations of both future memory variables. -/
theorem double_integral_translate (F : ℝ → ℝ → ℝ → ℝ) (w a b : ℝ) :
    (∫ u in (0 : ℝ)..a-w, ∫ v in (0 : ℝ)..b-w, F w (w+u) (w+v)) =
      ∫ U in w..a, ∫ V in w..b, F w U V := by
  calc
    _ = ∫ u in (0 : ℝ)..a-w, ∫ V in w..b, F w (w+u) V := by
      apply intervalIntegral.integral_congr
      intro u _
      simpa only [add_zero, show w+(b-w)=b from by ring] using
        (intervalIntegral.integral_comp_add_left (fun V => F w (w+u) V) w (a := 0) (b := b-w))
    _ = _ := by
      simpa only [add_zero, show w+(a-w)=a from by ring] using
        (intervalIntegral.integral_comp_add_left (fun U => ∫ V in w..b, F w U V) w (a := 0) (b := a-w))

/-- The memory kernel's inner affine integral has exactly the reflected bounds. -/
theorem reflected_inner_integral (sigma : ℝ → ℝ) (U V : ℝ) :
    2*(∫ w in (0 : ℝ)..min U V, sigma (U+V-2*w)) =
      ∫ z in |U-V|..U+V, sigma z := by
  have hi := intervalIntegral.smul_integral_comp_sub_mul sigma
    (a := 0) (b := min U V) (2 : ℝ) (U+V)
  have hm : U+V-2*min U V=|U-V| := by
    rcases le_total U V with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  simpa only [smul_eq_mul, mul_zero, sub_zero, hm] using hi

/-- The actual finite compact rearrangement required for the reflected candidate.
It uses neither Laplace transforms nor an assumed Fubini formula. -/
theorem reflected_memory_rearrangement {r sigma : ℝ → ℝ}
    (hr : Continuous r) (hsigma : Continuous sigma) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2*(∫ w in (0 : ℝ)..min a b, ∫ u in (0 : ℝ)..a-w, ∫ v in (0 : ℝ)..b-w,
      r (a-w-u)*r (b-w-v)*sigma (u+v)) =
    ∫ U in (0 : ℝ)..a, ∫ V in (0 : ℝ)..b,
      r (a-U)*r (b-V)*(∫ z in |U-V|..U+V, sigma z) := by
  let F : ℝ → ℝ → ℝ → ℝ := fun w U V => r (a-U)*r (b-V)*sigma (U+V-2*w)
  have hF : Continuous (fun z : ℝ×(ℝ×ℝ) => F z.1 z.2.1 z.2.2) := by
    unfold F
    fun_prop
  have ht (w : ℝ) :
      (∫ u in (0 : ℝ)..a-w, ∫ v in (0 : ℝ)..b-w,
        r (a-w-u)*r (b-w-v)*sigma (u+v)) =
      ∫ U in w..a, ∫ V in w..b, F w U V := by
    rw [← double_integral_translate F w a b]
    apply intervalIntegral.integral_congr
    intro u _
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only [F]
    rw [show a-(w+u)=a-w-u from by ring, show b-(w+v)=b-w-v from by ring,
      show (w+u)+(w+v)-2*w=u+v from by ring]
  simp_rw [ht]
  rw [triple_min_swap hF ha hb]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro U _
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro V _
  dsimp only [F]
  rw [intervalIntegral.integral_const_mul]
  rw [show 2*(r (a-U)*r (b-V)*(∫ w in (0 : ℝ)..min U V, sigma (U+V-2*w))) =
    r (a-U)*r (b-V)*(2*(∫ w in (0 : ℝ)..min U V, sigma (U+V-2*w))) from by ring,
    reflected_inner_integral]

/-- The same true finite rearrangement needs continuity only on the physical time ray. -/
theorem reflected_memory_rearrangement_on_ray {r sigma : ℝ → ℝ}
    (hr : ContinuousOn r (Ici 0)) (hsigma : ContinuousOn sigma (Ici 0)) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2*(∫ w in (0 : ℝ)..min a b, ∫ u in (0 : ℝ)..a-w, ∫ v in (0 : ℝ)..b-w,
      r (a-w-u)*r (b-w-v)*sigma (u+v)) =
    ∫ U in (0 : ℝ)..a, ∫ V in (0 : ℝ)..b,
      r (a-U)*r (b-V)*(∫ z in |U-V|..U+V, sigma z) := by
  have hrc : Continuous (fun x => r (max 0 x)) :=
    hr.comp_continuous (continuous_const.max continuous_id) (fun x => show 0 ≤ max 0 x from le_max_left 0 x)
  have hsc : Continuous (fun x => sigma (max 0 x)) :=
    hsigma.comp_continuous (continuous_const.max continuous_id) (fun x => show 0 ≤ max 0 x from le_max_left 0 x)
  have hi := reflected_memory_rearrangement hrc hsc ha hb
  have hleft :
      (∫ w in (0 : ℝ)..min a b, ∫ u in (0 : ℝ)..a-w, ∫ v in (0 : ℝ)..b-w,
        r (max 0 (a-w-u))*r (max 0 (b-w-v))*sigma (max 0 (u+v))) =
      ∫ w in (0 : ℝ)..min a b, ∫ u in (0 : ℝ)..a-w, ∫ v in (0 : ℝ)..b-w,
        r (a-w-u)*r (b-w-v)*sigma (u+v) := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le (le_min ha hb)] at hw
    apply intervalIntegral.integral_congr
    intro u hu
    have haw : 0 ≤ a-w := sub_nonneg.mpr (hw.2.trans (min_le_left _ _))
    rw [uIcc_of_le haw] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    have hbw : 0 ≤ b-w := sub_nonneg.mpr (hw.2.trans (min_le_right _ _))
    rw [uIcc_of_le hbw] at hv
    dsimp only
    rw [max_eq_right (show 0 ≤ a-w-u from by linarith [hu.2]),
      max_eq_right (show 0 ≤ b-w-v from by linarith [hv.2]), max_eq_right (add_nonneg hu.1 hv.1)]
  have hright :
      (∫ U in (0 : ℝ)..a, ∫ V in (0 : ℝ)..b,
        r (max 0 (a-U))*r (max 0 (b-V))*(∫ z in |U-V|..U+V, sigma (max 0 z))) =
      ∫ U in (0 : ℝ)..a, ∫ V in (0 : ℝ)..b,
        r (a-U)*r (b-V)*(∫ z in |U-V|..U+V, sigma z) := by
    apply intervalIntegral.integral_congr
    intro U hU
    rw [uIcc_of_le ha] at hU
    apply intervalIntegral.integral_congr
    intro V hV
    rw [uIcc_of_le hb] at hV
    dsimp only
    rw [max_eq_right (sub_nonneg.mpr hU.2), max_eq_right (sub_nonneg.mpr hV.2)]
    congr 1
    apply intervalIntegral.integral_congr
    intro z hz
    have hl : |U-V| ≤ U+V := abs_le.mpr ⟨by linarith [hU.1],by linarith [hV.1]⟩
    rw [uIcc_of_le hl] at hz
    dsimp only
    rw [max_eq_right ((abs_nonneg _).trans hz.1)]
  change 2*(∫ w in (0 : ℝ)..min a b, ∫ u in (0 : ℝ)..a-w, ∫ v in (0 : ℝ)..b-w,
      r (max 0 (a-w-u))*r (max 0 (b-w-v))*sigma (max 0 (u+v))) = _ at hi
  rw [hleft, hright] at hi
  exact hi

end SphericalAging.ReflectionFiniteFubini
