module

public import SphericalAging.CausalTreeLabelEquivalence
public import SphericalAging.ResponseCompactness
public import SphericalAging.TreePolynomialDrift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ParametricIntegral

public section

/-! Strong Hilbert derivatives of the actual causally projected tree curve. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory Filter UniformSpace
namespace SphericalAging.ProjectedTreeDrift
open CausalTree CausalTreeRealization CausalTreePositivity CKSpecification GreenCovariance
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The original causal response integrand is genuinely Bochner integrable. -/
theorem original_memory_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => d.R t u • graftTensor (p - 1)
      (standardTensorPower (ckTreeState h u))) volume 0 t := by
  apply (ckTreeState_integrable h hb ht).congr
  intro u hu
  rw [uIoc_of_le ht] at hu
  dsimp only
  rw [clampedResponse_eq hu.1.le hu.2, graftTensor_power]

section BochnerLeibniz
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A moving strip has its genuine strong Hilbert derivative from joint continuity alone. -/
theorem moving_boundary_hasDerivAt {F : ℝ → ℝ → E}
    (hF : Continuous (Function.uncurry F)) (t : ℝ) :
    HasDerivAt (fun x => ∫ u in t..x, F x u) (F t t) t := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hn : {z : ℝ × ℝ | ‖F z.1 z.2 - F t t‖ < ε} ∈ 𝓝 (t,t) := by
    have hc : Continuous (fun z : ℝ × ℝ => ‖F z.1 z.2 - F t t‖) := (hF.sub continuous_const).norm
    have hl : Tendsto (fun z : ℝ × ℝ => ‖F z.1 z.2 - F t t‖) (𝓝 (t,t)) (𝓝 0) := by
      simpa using (hc.continuousAt : ContinuousAt (fun z : ℝ × ℝ => ‖F z.1 z.2 - F t t‖) (t,t)).tendsto
    exact hl.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  filter_upwards [Metric.ball_mem_nhds t hδ] with x hx
  have hb : ∀ u ∈ uIoc t x, ‖F x u - F t t‖ ≤ ε := by
    intro u hu
    have hu' := uIoc_subset_uIcc hu
    have hd : dist u t ≤ dist x t := by
      rw [Real.dist_eq, Real.dist_eq]
      rcases mem_uIcc.mp hu' with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h.1), abs_of_nonneg (sub_nonneg.mpr (h.1.trans h.2))]
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr h.2), abs_of_nonpos (sub_nonpos.mpr (h.1.trans h.2))]
        linarith
    have hp : (x,u) ∈ Metric.ball (t,t) δ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨hx, hd.trans_lt hx⟩
    exact (hball hp).le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have he : (∫ u in t..x, F x u) - (∫ u in t..t, F t u) - (x-t) • F t t =
      ∫ u in t..x, (F x u - F t t) := by
    have hr : Continuous (fun u => F x u) := hF.comp (continuous_const.prodMk continuous_id)
    rw [intervalIntegral.integral_sub (hr.intervalIntegrable t x) intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_same]
    simp
  rw [he]
  simpa only [Real.norm_eq_abs] using hi

/-- Fixed-domain dominated differentiation is a strong Bochner theorem, including the causal kink. -/
theorem fixed_integral_hasDerivAt_of_lipschitz {F : ℝ → ℝ → E} {D : ℝ → E}
    {t : ℝ} {U : Set ℝ} {M : ℝ≥0} (hF : Continuous (Function.uncurry F)) (hD : Continuous D)
    (ht : 0 ≤ t) (hU : U ∈ 𝓝 t)
    (hLip : ∀ u ∈ Icc 0 t, LipschitzOnWith M (fun x => F x u) U)
    (hDiff : ∀ u ∈ Ico 0 t, HasDerivAt (fun x => F x u) (D u) t) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..t, F x u) (∫ u in (0 : ℝ)..t, D u) t := by
  have hr (x : ℝ) : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hd := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict (Ioc 0 t)) (F := F) (F' := D) (bound := fun _ => (M : ℝ)) hU
    (Filter.Eventually.of_forall fun x => (hr x).aestronglyMeasurable)
    ((hr t).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hD.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun u hu => by
      simpa using hLip u (Ioc_subset_Icc_self hu)))) (integrable_const (M : ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (show ∀ᵐ u ∂volume, u ≠ t from by simp [ae_iff])] with u hu hne
      exact hDiff u ⟨hu.1.le, lt_of_le_of_ne hu.2 hne⟩)
  simpa only [intervalIntegral.integral_of_le ht] using hd.2

/-- Strong moving-endpoint Bochner differentiation of a continuous causal response convolution. -/
theorem moving_integral_hasDerivAt_of_lipschitz {F : ℝ → ℝ → E} {D : ℝ → E}
    {t : ℝ} {U : Set ℝ} {M : ℝ≥0} (hF : Continuous (Function.uncurry F)) (hD : Continuous D)
    (ht : 0 ≤ t) (hU : U ∈ 𝓝 t)
    (hLip : ∀ u ∈ Icc 0 t, LipschitzOnWith M (fun x => F x u) U)
    (hDiff : ∀ u ∈ Ico 0 t, HasDerivAt (fun x => F x u) (D u) t) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, F x u) ((∫ u in (0 : ℝ)..t, D u) + F t t) t := by
  have ha := fixed_integral_hasDerivAt_of_lipschitz hF hD ht hU hLip hDiff
  have hb := moving_boundary_hasDerivAt hF t
  apply (ha.add hb).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro x
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable t x)).symm

end BochnerLeibniz

section StrongL2Derivative
variable {A : Type} [MeasurableSpace A] {μ : Measure A}

/-- The square norm of an actual L² representative, used for strong derivative limits. -/
theorem toLp_norm_sq {f : A → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ u, f u ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with u hu
  simp [hu, RCLike.inner_apply, pow_two]

/-- Pointwise derivatives with an actual L² domination produce a strong Hilbert derivative.
The conclusion concerns norm convergence of the difference quotients, not weak derivatives. -/
theorem toLp_hasDerivAt_of_domination {f : ℝ → A → ℝ} {g b : A → ℝ} {t : ℝ} {U : Set ℝ}
    (hf : ∀ x, MemLp (f x) 2 μ) (hg : MemLp g 2 μ) (hb : MemLp b 2 μ) (hU : U ∈ 𝓝 t)
    (hbound : ∀ x ∈ U, ∀ᵐ u ∂μ, |f x u - f t u| ≤ |x - t| * b u)
    (hgB : ∀ᵐ u ∂μ, |g u| ≤ b u)
    (hDiff : ∀ᵐ u ∂μ, HasDerivAt (fun x => f x u) (g u) t) :
    HasDerivAt (fun x => (hf x).toLp (f x)) (hg.toLp g) t := by
  let F : ℝ → Lp ℝ 2 μ := fun x => (hf x).toLp (f x)
  let G : Lp ℝ 2 μ := hg.toLp g
  let q : ℝ → A → ℝ := fun x u => (x - t)⁻¹ * (f x u - f t u) - g u
  have hqm (x : ℝ) : MemLp (q x) 2 μ := ((hf x).sub (hf t)).const_mul (x-t)⁻¹ |>.sub hg
  have hcoe (x : ℝ) : (hqm x).toLp (q x) = (x-t)⁻¹ • (F x - F t) - G := by
    apply Lp.ext
    filter_upwards [(hqm x).coeFn_toLp, (hf x).coeFn_toLp, (hf t).coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_sub (F x) (F t), Lp.coeFn_smul (x-t)⁻¹ (F x-F t),
      Lp.coeFn_sub ((x-t)⁻¹ • (F x-F t)) G] with u hq hx ht hgv hs ha hr
    change ((x-t)⁻¹ • (F x-F t) - G) u = ((x-t)⁻¹ • (F x-F t)) u - G u at hr
    change ((x-t)⁻¹ • (F x-F t)) u = (x-t)⁻¹ * (F x-F t) u at ha
    change (F x-F t) u = F x u-F t u at hs
    rw [hq, hr, ha, hs]
    change q x u = (x-t)⁻¹ * ((hf x).toLp (f x) u - (hf t).toLp (f t) u) - hg.toLp g u
    rw [hx, ht, hgv]
  have hbounded : ∀ᶠ x in 𝓝[≠] t, ∀ᵐ u ∂μ, ‖q x u ^ 2‖ ≤ (2*b u)^2 := by
    filter_upwards [show U ∈ 𝓝[≠] t from nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with x hx hxt
    have hne : x-t ≠ 0 := sub_ne_zero.mpr hxt
    filter_upwards [hbound x hx, hgB] with u hxu hgu
    have hquot : |(x-t)⁻¹ * (f x u-f t u)| ≤ b u := by
      calc
        _ = |x-t|⁻¹ * |f x u-f t u| := by rw [abs_mul, abs_inv]
        _ ≤ |x-t|⁻¹ * (|x-t| * b u) := mul_le_mul_of_nonneg_left hxu (inv_nonneg.mpr (abs_nonneg _))
        _ = b u := by rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hne), one_mul]
    have hq : |q x u| ≤ 2*b u := (abs_sub _ _).trans (by linarith)
    have hbu : 0 ≤ 2*b u := by linarith [abs_nonneg (g u)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ = |q x u| ^ 2 := (sq_abs _).symm
      _ ≤ _ := (sq_le_sq₀ (abs_nonneg _) hbu).mpr hq
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun x => q x u ^ 2) (𝓝[≠] t) (𝓝 (0 : ℝ)) := by
    filter_upwards [hDiff] with u hu
    have hq : Tendsto (fun x => q x u) (𝓝[≠] t) (𝓝 (0 : ℝ)) := by
      simpa [q, slope, smul_eq_mul] using hu.tendsto_slope.sub_const (g u)
    simpa using hq.pow 2
  have hbi : Integrable (fun u => (2*b u)^2) μ := by
    convert hb.integrable_sq.const_mul (4 : ℝ) using 1
    ext u
    ring
  have hi : Tendsto (fun x => ∫ u, q x u ^ 2 ∂μ) (𝓝[≠] t) (𝓝 (0 : ℝ)) := by
    simpa using tendsto_integral_filter_of_dominated_convergence (fun u => (2*b u)^2)
      (Filter.Eventually.of_forall fun x => (hqm x).aestronglyMeasurable.pow 2) hbounded hbi hlim
  have hn : Tendsto (fun x => ‖(x-t)⁻¹ • (F x-F t) - G‖) (𝓝[≠] t) (𝓝 (0 : ℝ)) := by
    have he : (fun x => ‖(x-t)⁻¹ • (F x-F t) - G‖) =
        (fun x => Real.sqrt (∫ u, q x u ^ 2 ∂μ)) := by
      funext x
      rw [← hcoe x, ← toLp_norm_sq (hqm x), Real.sqrt_sq (norm_nonneg _)]
    rw [he]
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hi using 1 <;>
      simp [Function.comp_def]
  apply hasDerivAt_iff_tendsto_slope.mpr
  change Tendsto (fun x => (x-t)⁻¹ • (F x-F t)) (𝓝[≠] t) (𝓝 G)
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hn

end StrongL2Derivative

/-- A response row on a fixed noise prefix, as a genuine L² function. -/
@[expose] def fixedNoiseFunction (T : ℝ) (r : ℝ → ℝ → ℝ) (x : ℝ) : ℝ → ℝ :=
  (Ioc 0 T).indicator (r x)

theorem fixedNoiseFunction_memLp (T : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (x : ℝ) :
    MemLp (fixedNoiseFunction T r x) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  exact (WhiteCovarianceKernel.rowCut_memLp (fun _ u => r x u)
    (hr.comp (continuous_const.prodMk continuous_snd)) T).mono_measure Measure.restrict_le_self

@[expose] def fixedNoiseRow (T : ℝ) (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (x : ℝ) : NoiseSpace :=
  (fixedNoiseFunction_memLp T r hr x).toLp (fixedNoiseFunction T r x)

theorem fixedNoiseRow_coe (T : ℝ) (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (x : ℝ) :
    (fixedNoiseRow T r hr x : ℝ → ℝ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] fixedNoiseFunction T r x :=
  (fixedNoiseFunction_memLp T r hr x).coeFn_toLp

/-- Strong L² differentiation on a fixed cutoff follows from actual compact response derivatives. -/
theorem fixedNoiseRow_hasDerivAt {T l r t : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g))
    (ht : t ∈ Ioo l r)
    (hd : ∀ x ∈ Icc l r, ∀ u ∈ Icc 0 T, HasDerivAt (fun y => f y u) (g x u) x) :
    HasDerivAt (fixedNoiseRow T f hf) (fixedNoiseRow T g hg t) t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hg.norm.continuousOn
  let K : ℝ := max 0 M
  have hK : 0 ≤ K := le_max_left _ _
  have hnorm : ∀ x ∈ Icc l r, ∀ u ∈ Icc 0 T, ‖g x u‖ ≤ K := by
    intro x hx u hu
    exact (hM ⟨(x,u), ⟨hx,hu⟩, rfl⟩).trans (le_max_right _ _)
  let b : ℝ → ℝ := (Ioc 0 T).indicator (fun _ => K)
  have hb : MemLp b 2 (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_indicator_const 2 measurableSet_Ioc K (Or.inr (ne_of_lt
      ((Measure.restrict_apply_le (Ioi (0 : ℝ)) (Ioc 0 T)).trans_lt
        (show volume (Ioc 0 T) < ∞ from measure_Ioc_lt_top))))
  apply toLp_hasDerivAt_of_domination
    (f := fixedNoiseFunction T f) (g := fixedNoiseFunction T g t) (b := b)
    (fun x => fixedNoiseFunction_memLp T f hf x) (fixedNoiseFunction_memLp T g hg t) hb
    (Ioo_mem_nhds ht.1 ht.2)
  · intro x hx
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ Ioc 0 T
    · have hi := (convex_Icc l r).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun x => f x u) (f' := fun x => g x u) (C := K)
        (fun y hy => (hd y hy u ⟨hu.1.le, hu.2⟩).hasDerivWithinAt)
        (fun y hy => hnorm y hy u ⟨hu.1.le, hu.2⟩)
        (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self hx)
      simpa only [fixedNoiseFunction, indicator_of_mem hu, b, Real.norm_eq_abs, mul_comm] using hi
    · simp [fixedNoiseFunction, b, indicator_of_notMem hu]
  · apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ Ioc 0 T
    · simpa only [fixedNoiseFunction, b, indicator_of_mem hu, Real.norm_eq_abs] using
        hnorm t (Ioo_subset_Icc_self ht) u ⟨hu.1.le, hu.2⟩
    · simp [fixedNoiseFunction, b, indicator_of_notMem hu]
  · apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ Ioc 0 T
    · simpa only [fixedNoiseFunction, indicator_of_mem hu] using
        hd t (Ioo_subset_Icc_self ht) u ⟨hu.1.le, hu.2⟩
    · simpa [fixedNoiseFunction, hu] using (hasDerivAt_const t (0 : ℝ))

/-- The actual response gives the strong L² derivative after its causal cutoff has stopped moving. -/
theorem ckFixedNoiseRow_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t : ℝ} (hT : 0 ≤ T) (ht : T < t) :
    HasDerivAt (fixedNoiseRow T (clampedResponse d) (clampedResponse_continuous h))
      (fixedNoiseRow T (clampedResponseSlope p β d) (clampedResponseSlope_continuous h) t) t := by
  apply fixedNoiseRow_hasDerivAt (l := (T+t)/2) (r := t+1)
    (clampedResponse_continuous h) (clampedResponseSlope_continuous h)
    (show t ∈ Ioo ((T+t)/2) (t+1) from ⟨by linarith, by linarith⟩)
  intro x hx u hu
  exact clampedResponse_hasDerivAt h hu.1 (by linarith [hx.1, hu.2])

/-- Exact identification of the projected Brownian row with its stopped cutoff. -/
theorem noisePrefix_noiseFeature {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t)
    (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) :
    noisePrefix T (noiseFeature r hr t) = fixedNoiseRow T r hr t := by
  apply Lp.ext
  filter_upwards [noisePrefix_coe T (noiseFeature r hr t), noiseFeature_coe r hr t,
    fixedNoiseRow_coe T r hr t] with u hp hf hfixed
  rw [hp, hfixed]
  by_cases hu : u ∈ Ioc 0 T
  · rw [indicator_of_mem (show u ∈ Iic T from hu.2), hf, WhiteCovarianceKernel.rowCut,
      indicator_of_mem (show u ∈ Ioc 0 t from ⟨hu.1, hu.2.trans ht⟩), fixedNoiseFunction, indicator_of_mem hu]
  · by_cases huT : u ≤ T
    · have hu0 : u ≤ 0 := le_of_not_gt (fun h => hu ⟨h, huT⟩)
      rw [indicator_of_mem (show u ∈ Iic T from huT), hf, WhiteCovarianceKernel.rowCut,
        indicator_of_notMem (show u ∉ Ioc 0 t from fun h => not_lt_of_ge hu0 h.1),
        fixedNoiseFunction, indicator_of_notMem hu]
    · rw [indicator_of_notMem (show u ∉ Iic T from huT), fixedNoiseFunction, indicator_of_notMem hu]


/-- The stopped Brownian row has its exact finite-interval Gram kernel. -/
theorem fixedNoiseRow_inner {T : ℝ} (hT : 0 ≤ T) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (x y : ℝ) :
    inner ℝ (fixedNoiseRow T r hr x) (fixedNoiseRow T r hr y) =
      ∫ u in (0 : ℝ)..T, r x u * r y u := by
  rw [L2.inner_def]
  calc
    _ = ∫ u, (Ioc 0 T).indicator (fun u => r x u * r y u) u
        ∂volume.restrict (Ioi (0 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [fixedNoiseRow_coe T r hr x, fixedNoiseRow_coe T r hr y] with u hx hy
      rw [hx, hy]
      by_cases hu : u ∈ Ioc 0 T <;>
        simp [fixedNoiseFunction, hu, RCLike.inner_apply, mul_comm]
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (show Ioc (0 : ℝ) T ⊆ Ioi 0 from fun _ h => h.1),
        ← intervalIntegral.integral_of_le hT]

theorem fixedNoiseRow_continuous {T : ℝ} (hT : 0 ≤ T) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) : Continuous (fixedNoiseRow T r hr) := by
  apply continuous_of_gram
  simp_rw [fixedNoiseRow_inner hT]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hr.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hr.comp (continuous_fst.snd.prodMk continuous_snd))
  · exact continuous_const

/-- Actual leaf response with the Brownian cutoff stopped at T. -/
@[expose] def stoppedLeaf (T : ℝ) (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    (x : ℝ) : LeafSpace :=
  WithLp.toLp 2 (r x 0, Real.sqrt 2 • fixedNoiseRow T r hr x)

theorem stoppedLeaf_continuous {T : ℝ} (hT : 0 ≤ T) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) : Continuous (stoppedLeaf T r hr) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ NoiseSpace).symm.continuous.comp
    ((hr.comp (continuous_id.prodMk continuous_const)).prodMk
      ((fixedNoiseRow_continuous hT r hr).const_smul (Real.sqrt 2)))

/-- Projection of the actual Brownian leaf, including its initial atom, is the stopped leaf. -/
theorem leafPrefix_leafResponseFeature {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t)
    (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) :
    leafPrefix T (leafResponseFeature r hr t) = stoppedLeaf T r hr t := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change r (max 0 t) 0 = r t 0
    rw [max_eq_right (hT.trans ht)]
  · change noisePrefix T (Real.sqrt 2 • noiseFeature r hr (max 0 t)) =
      Real.sqrt 2 • fixedNoiseRow T r hr t
    rw [noisePrefix_smul, max_eq_right (hT.trans ht), noisePrefix_noiseFeature hT ht]

/-- The genuinely strong Hilbert derivative of the projected leaf after its cutoff. -/
theorem stoppedLeaf_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t : ℝ} (hT : 0 ≤ T) (ht : T < t) :
    HasDerivAt (stoppedLeaf T (clampedResponse d) (clampedResponse_continuous h))
      (stoppedLeaf T (clampedResponseSlope p β d) (clampedResponseSlope_continuous h) t) t := by
  have ha := clampedResponse_hasDerivAt h (show (0 : ℝ) ≤ 0 from le_rfl) (hT.trans_lt ht)
  have hn := (ckFixedNoiseRow_hasDerivAt h hT ht).const_smul (Real.sqrt 2)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ NoiseSpace).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (ha.prodMk hn)

/-- The actual projected one-leaf vector is strongly differentiable on the open post-cutoff ray. -/
theorem projectedBase_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t : ℝ} (hT : 0 ≤ T) (ht : T < t) :
    HasDerivAt (fun x => timePrefix T
      (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) x))
      (lp.single 2 CausalTree.Tree.leaf
        (stoppedLeaf T (clampedResponseSlope p β d) (clampedResponseSlope_continuous h) t)) t := by
  have hd := (lp.singleContinuousLinearMap ℝ (fun τ : CausalTree.Tree (p-1) => (fiber τ).Carrier) 2 (CausalTree.Tree.leaf : CausalTree.Tree (p-1))).hasFDerivAt.comp_hasDerivAt t
    (stoppedLeaf_hasDerivAt h hT ht)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  apply lp.ext
  funext τ
  by_cases hτ : τ = CausalTree.Tree.leaf
  · subst τ
    simp only [Function.comp_apply, lp.singleContinuousLinearMap_apply, timePrefix_apply, fiberPrefix_leaf, baseVector, lp.single_apply_self]
    exact leafPrefix_leafResponseFeature hT hx.le _ _
  · simp only [Function.comp_apply, lp.singleContinuousLinearMap_apply, timePrefix_apply, baseVector, lp.single_apply_ne _ _ _ hτ, map_zero]


section HilbertFubini
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open WeightedHilbertKernel

/-- The triangular Fubini rule holds for actual strong Hilbert integrals. -/
theorem standard_triangle_integral_swap {F : ℝ → ℝ → E}
    (hF : Continuous (Function.uncurry F)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ v in (0 : ℝ)..t, ∫ u in (0 : ℝ)..v, F v u) =
      ∫ u in (0 : ℝ)..t, ∫ v in u..t, F v u := by
  have hforward : Continuous (fun v => ∫ u in (0 : ℝ)..v, F v u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_id
  have hbackward : Continuous (fun u => ∫ v in u..t, F v u) := by
    have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := t) (f := fun u v => F v u) (hF.comp continuous_swap) continuous_id
    apply hc.neg.congr
    intro u
    exact (intervalIntegral.integral_symm (μ := volume) (f := fun v => F v u) t u).symm
  apply ext_inner_left ℝ
  intro w
  rw [inner_intervalIntegral w (hforward.intervalIntegrable 0 t),
    inner_intervalIntegral w (hbackward.intervalIntegrable 0 t)]
  have he (v : ℝ) : inner ℝ w (∫ u in (0 : ℝ)..v, F v u) =
      ∫ u in (0 : ℝ)..v, inner ℝ w (F v u) :=
    inner_intervalIntegral w ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 v)
  have he' (u : ℝ) : inner ℝ w (∫ v in u..t, F v u) =
      ∫ v in u..t, inner ℝ w (F v u) :=
    inner_intervalIntegral w ((hF.comp (continuous_id.prodMk continuous_const)).intervalIntegrable u t)
  simp_rw [he, he']
  exact TriangleUniqueness.standard_triangle_integral_swap (F := fun v u => inner ℝ w (F v u))
    ((innerSL ℝ w).continuous.comp hF) ht

/-- Continuous vector forcing may be transported through the actual CK response memory. -/
theorem weighted_triangle_memory_diagonal {R Sigma : ℝ → ℝ → ℝ} {A : ℝ → E}
    (hR : Continuous (Function.uncurry R)) (hSigma : Continuous (Function.uncurry Sigma))
    (hA : Continuous A) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, (∫ z in u..t, Sigma t z * R z u) • A u) =
      ∫ z in (0 : ℝ)..t, Sigma t z • (∫ u in (0 : ℝ)..z, R z u • A u) := by
  have hF : Continuous (Function.uncurry (fun z u => (Sigma t z * R z u) • A u)) :=
    (((hSigma.comp (continuous_const.prodMk continuous_fst)).mul hR).smul
      (hA.comp continuous_snd))
  calc
    _ = ∫ u in (0 : ℝ)..t, ∫ z in u..t, (Sigma t z * R z u) • A u := by
      simp_rw [intervalIntegral.integral_smul_const]
    _ = ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..z, (Sigma t z * R z u) • A u :=
      (standard_triangle_integral_swap hF ht).symm
    _ = _ := by simp_rw [mul_smul, intervalIntegral.integral_smul]

/-- The causal-clamp mean-value estimate works in the actual strong Hilbert norm. -/
theorem causal_clamp_lipschitzOn {f f' : ℝ → E} {a r : ℝ} {M : ℝ≥0}
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
  have he := hl.dist_le_mul (max x a) ⟨le_max_right _ _, max_le hx har⟩
    (max y a) ⟨le_max_right _ _, max_le hy har⟩
  exact he.trans (mul_le_mul_of_nonneg_left (by simpa using hc) M.coe_nonneg)

/-- Genuine strong differentiation of a CK response convolution with continuous Hilbert forcing. -/
theorem weighted_response_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {A : ℝ → E} (hA : Continuous A) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, clampedResponse d x u • A u)
      ((∫ u in (0 : ℝ)..t, clampedResponseSlope p β d t u • A u) + A t) t := by
  let r : ℝ := t + 1
  let F : ℝ → ℝ → E := fun x u => clampedResponse d x u • A u
  let G : ℝ → ℝ → E := fun x u => clampedResponseSlope p β d x u • A u
  have hF : Continuous (Function.uncurry F) := (clampedResponse_continuous h).smul
    (hA.comp continuous_snd)
  have hG : Continuous (Function.uncurry G) := (clampedResponseSlope_continuous h).smul
    (hA.comp continuous_snd)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (show ContinuousOn (fun z : ℝ × ℝ => ‖G z.1 z.2‖) (Icc 0 r ×ˢ Icc 0 r) from hG.norm.continuousOn)
  let M : ℝ≥0 := ⟨max 0 M₀, le_max_left _ _⟩
  have hLip (u : ℝ) (hu : u ∈ Icc 0 t) :
      LipschitzOnWith M (fun x => F x u) (Iic r) := by
    have hl := causal_clamp_lipschitzOn (f := fun x => d.R x u • A u)
      (f' := fun x => responseSlope p β d x u • A u)
      (M := M) (a := u) (r := r) (hu.2.trans (by dsimp [r]; linarith))
      (fun x hx => (h.response_derivative x u hu.1 hx.1).smul_const (A u))
      (fun x hx => by
        have hx0 := hu.1.trans hx.1
        have hur : u ≤ r := hu.2.trans (by dsimp [r]; linarith)
        have hb := hM₀ ⟨(x,u), ⟨⟨hx0,hx.2⟩,⟨hu.1,hur⟩⟩,rfl⟩
        change ‖responseSlope p β d x u • A u‖ ≤ max 0 M₀
        have he : G x u = responseSlope p β d x u • A u := by
          dsimp only [G]
          rw [clampedResponseSlope_eq hu.1 hx.1]
        rw [← he]
        exact hb.trans (le_max_right _ _))
    simpa only [F, clampedResponse, max_eq_right hu.1] using hl
  have hDiff (u : ℝ) (hu : u ∈ Ico 0 t) :
      HasDerivAt (fun x => F x u) (G t u) t :=
    (clampedResponse_hasDerivAt h hu.1 hu.2).smul_const (A u)
  have hd := moving_integral_hasDerivAt_of_lipschitz (D := fun u => G t u) hF
    (hG.comp (continuous_const.prodMk continuous_id)) ht.le
    (show Iic r ∈ 𝓝 t from Iic_mem_nhds (by dsimp [r]; linarith)) hLip hDiff
  have he : F t t = A t := by
    dsimp only [F]
    rw [clampedResponse_eq ht.le le_rfl, h.response_diagonal t ht.le, one_smul]
  simpa only [F, G, he] using hd

end HilbertFubini


/-- The explicit strong derivative of the actual projected tree curve. -/
@[expose] def projectedDerivative {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T t : ℝ) : CausalTree.Space (p-1) :=
  lp.single 2 CausalTree.Tree.leaf
      (stoppedLeaf T (clampedResponseSlope p β d) (clampedResponseSlope_continuous h) t) +
    (β * Real.sqrt p) • timePrefix T
      ((∫ u in (0 : ℝ)..t, clampedResponseSlope p β d t u •
        graftPower (ckTreeState h (max 0 u))) + graftPower (ckTreeState h (max 0 t)))

/-- Actual strong differentiation of every causal projection after the cutoff time. -/
theorem projectedTree_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t : ℝ} (hT : 0 ≤ T) (ht : T < t) :
    HasDerivAt (fun x => timePrefix T (ckTreeState h x)) (projectedDerivative h T t) t := by
  have hc : Continuous (fun u => graftPower (ckTreeState h (max 0 u))) :=
    (graftPower_continuous (p-1)).comp (ckTreeState_clamped_continuous h hb)
  have hm := weighted_response_hasDerivAt h hc (hT.trans_lt ht)
  have hp := (timePrefixL (p-1) T).hasFDerivAt.comp_hasDerivAt t hm
  have hd := (projectedBase_hasDerivAt h hT ht).add (hp.const_smul (β * Real.sqrt p))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (hT.trans_lt ht)] with x hx
  rw [ckTreeState_volterra_clamped h hb hx.le]
  change timePrefixL (p-1) T (_ + _) = _
  rw [map_add, map_smul]
  congr 2
  apply congrArg (timePrefixL (p-1) T)
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hx.le] at hu
  dsimp only
  rw [max_eq_right hu.1]

/-- The strong derivative varies continuously on the full real line after extension. -/
theorem projectedDerivative_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (projectedDerivative h T) := by
  have hc : Continuous (fun u => graftPower (ckTreeState h (max 0 u))) :=
    (graftPower_continuous (p-1)).comp (ckTreeState_clamped_continuous h hb)
  have hi : Continuous (fun t => ∫ u in (0 : ℝ)..t,
      clampedResponseSlope p β d t u • graftPower (ckTreeState h (max 0 u))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((clampedResponseSlope_continuous h).smul (hc.comp continuous_snd)) continuous_id
  exact ((lp.singleContinuousLinearMap ℝ (fun τ : CausalTree.Tree (p-1) => (fiber τ).Carrier)
    2 CausalTree.Tree.leaf).continuous.comp
      (stoppedLeaf_continuous hT _ (clampedResponseSlope_continuous h))).add
    (((timePrefixL (p-1) T).continuous.comp (hi.add hc)).const_smul (β * Real.sqrt p))


section L2Integral
variable {A X : Type} [MeasurableSpace A] [MeasurableSpace X]
    {μ : Measure A} {ν : Measure X} [SFinite μ] [SFinite ν]

/-- Genuine L²/Bochner integral commutation, proved by scalar Fubini against all Hilbert tests. -/
theorem toLp_integral {f : X → A → ℝ} {g : A → ℝ}
    (hf : ∀ x, MemLp (f x) 2 μ) (hg : MemLp g 2 μ)
    (he : ∀ᵐ u ∂μ, g u = ∫ x, f x u ∂ν)
    (hcurve : Integrable (fun x => (hf x).toLp (f x)) ν)
    (hpair : ∀ w : Lp ℝ 2 μ, Integrable (fun z : X × A => w z.2 * f z.1 z.2) (ν.prod μ)) :
    hg.toLp g = ∫ x, (hf x).toLp (f x) ∂ν := by
  apply ext_inner_left ℝ
  intro w
  have hr (x : X) : inner ℝ w ((hf x).toLp (f x)) = ∫ u, w u * f x u ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hf x).coeFn_toLp] with u hu
    simp [hu, RCLike.inner_apply, mul_comm]
  have hl : inner ℝ w (hg.toLp g) = ∫ u, w u * g u ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with u hu
    simp [hu, RCLike.inner_apply, mul_comm]
  rw [hl]
  have hi : inner ℝ w (∫ x, (hf x).toLp (f x) ∂ν) =
      ∫ x, inner ℝ w ((hf x).toLp (f x)) ∂ν :=
    ((innerSL ℝ w).integral_comp_comm hcurve).symm
  rw [hi]
  simp_rw [hr]
  calc
    _ = ∫ u, w u * (∫ x, f x u ∂ν) ∂μ := integral_congr_ae (he.mono fun u hu => by rw [hu])
    _ = ∫ u, ∫ x, w u * f x u ∂ν ∂μ := by simp_rw [integral_const_mul]
    _ = _ := (integral_integral_swap (hpair w)).symm

end L2Integral


section MemoryRecombination
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full CK response slope recombines to the actual strong vector memory equation. -/
theorem responseSlope_integral_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {A : ℝ → E} (hA : Continuous A) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, clampedResponseSlope p β d t u • A u) =
      -d.multiplier t • (∫ u in (0 : ℝ)..t, clampedResponse d t u • A u) +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
          (∫ u in (0 : ℝ)..z, clampedResponse d z u • A u) := by
  have hc : Continuous (fun u => clampedResponse d t u • A u) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul hA
  have hmem : Continuous (fun u => (∫ z in u..t,
      clampedMemory p β d t z * clampedResponse d z u) • A u) := by
    have hz : Continuous (fun u => ∫ z in u..t,
        clampedMemory p β d t z * clampedResponse d z u) := by
      have hi : Continuous (fun u => ∫ z in t..u,
          clampedMemory p β d t z * clampedResponse d z u) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (((clampedMemory_continuous h).comp (continuous_const.prodMk continuous_snd)).mul
            ((clampedResponse_continuous h).comp continuous_swap)) continuous_id
      apply hi.neg.congr
      intro u
      exact (intervalIntegral.integral_symm (μ := volume)
        (f := fun z => clampedMemory p β d t z * clampedResponse d z u) t u).symm
    exact hz.smul hA
  calc
    _ = ∫ u in (0 : ℝ)..t, (-d.multiplier t) • (clampedResponse d t u • A u) +
        (∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) • A u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht] at hu
      dsimp only
      rw [clampedResponseSlope_eq hu.1 hu.2, responseSlope_linear_memory hu.1 hu.2,
        add_smul, mul_smul]
    _ = (-d.multiplier t) • (∫ u in (0 : ℝ)..t, clampedResponse d t u • A u) +
        ∫ u in (0 : ℝ)..t, (∫ z in u..t,
          clampedMemory p β d t z * clampedResponse d z u) • A u := by
      rw [intervalIntegral.integral_add
        (f := fun u => (-d.multiplier t) • (clampedResponse d t u • A u))
        (g := fun u => (∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) • A u)
        ((hc.const_smul _).intervalIntegrable 0 t) (hmem.intervalIntegrable 0 t),
        intervalIntegral.integral_smul]
    _ = _ := by rw [weighted_triangle_memory_diagonal
      (clampedResponse_continuous h) (clampedMemory_continuous h) hA ht]

end MemoryRecombination


/-- Causal triangular Fubini requires actual rectangle integrability, with no continuity premise. -/
theorem triangular_integral_swap_of_integrable {F : ℝ → ℝ → ℝ} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hFi : IntegrableOn (Function.uncurry F) (Ioc 0 s ×ˢ Ioc 0 t)) :
    (∫ u in (0 : ℝ)..s, ∫ z in u..t, F u z) =
      ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..min z s, F u z := by
  let G : ℝ → ℝ → ℝ := fun u z => if u < z then F u z else 0
  have ht : 0 ≤ t := hs.trans hst
  have hGi : IntegrableOn (Function.uncurry G) (uIoc 0 s ×ˢ uIoc 0 t) := by
    have hi := hFi.indicator (measurableSet_lt measurable_fst measurable_snd)
    rw [uIoc_of_le hs, uIoc_of_le ht]
    exact hi
  have hswap := intervalIntegral_intervalIntegral_swap hGi
  calc
    _ = ∫ u in (0 : ℝ)..s, ∫ z in (0 : ℝ)..t, G u z := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hs] at hu
      exact (TriangleUniqueness.integral_strict_above hu.1 (hu.2.trans hst)).symm
    _ = ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..s, G u z := hswap
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le ht] at hz
      exact TriangleUniqueness.integral_strict_below hz.1 hs

/-- The causal memory swap is valid against all integrable, possibly discontinuous, Hilbert tests. -/
theorem weighted_triangle_memory_swap_integrable {R Sigma : ℝ → ℝ → ℝ} {A : ℝ → ℝ}
    (hR : Continuous (Function.uncurry R)) (hSigma : Continuous (Function.uncurry Sigma))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hA : IntervalIntegrable A volume 0 s) :
    (∫ u in (0 : ℝ)..s, A u * (∫ z in u..t, Sigma t z * R z u)) =
      ∫ z in (0 : ℝ)..t, Sigma t z * (∫ u in (0 : ℝ)..min z s, R z u * A u) := by
  have ht := hs.trans hst
  let B : ℝ × ℝ → ℝ := fun z => Sigma t z.2 * R z.2 z.1
  have hB : Continuous B :=
    (hSigma.comp (continuous_const.prodMk continuous_snd)).mul (hR.comp continuous_swap)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (show ContinuousOn (fun z : ℝ × ℝ => ‖B z‖) (Icc 0 s ×ˢ Icc 0 t) from hB.norm.continuousOn)
  have hAp : Integrable (fun z : ℝ × ℝ => A z.1)
      ((volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 t))) := by
    simpa using (hA.1.mul_prod (integrable_const (1 : ℝ)))
  rw [Measure.prod_restrict] at hAp
  have hFi : IntegrableOn (Function.uncurry (fun u z => Sigma t z * R z u * A u))
      (Ioc 0 s ×ˢ Ioc 0 t) := by
    have hi := hAp.mul_bdd hB.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      exact hM ⟨z, ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩, rfl⟩)
    change Integrable _ ((volume.prod volume).restrict (Ioc 0 s ×ˢ Ioc 0 t))
    convert hi using 1
    funext z
    dsimp only [Function.uncurry, B]
    ring
  calc
    _ = ∫ u in (0 : ℝ)..s, ∫ z in u..t, Sigma t z * R z u * A u := by
      simp_rw [intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      ring
    _ = ∫ z in (0 : ℝ)..t, ∫ u in (0 : ℝ)..min z s, Sigma t z * R z u * A u :=
      triangular_integral_swap_of_integrable hs hst hFi
    _ = _ := by simp_rw [mul_assoc, intervalIntegral.integral_const_mul]


/-- Every Hilbert test is genuinely integrable on a finite Brownian cutoff. -/
theorem noise_test_intervalIntegrable (w : NoiseSpace) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => w u) volume 0 T := by
  have hi := integrableOn_Lp_of_measure_ne_top w (show (1 : ℝ≥0∞) ≤ 2 from by norm_num)
    (s := Ioc 0 T) (ne_of_lt ((Measure.restrict_apply_le (Ioi (0 : ℝ)) (Ioc 0 T)).trans_lt
      (show volume (Ioc 0 T) < ∞ from measure_Ioc_lt_top)))
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0 : ℝ) T ⊆ Ioi 0 from fun _ h => h.1)] at hi
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hi

/-- Actual L² pairing against every test, including discontinuous tests. -/
theorem fixedNoiseRow_inner_test {T : ℝ} (hT : 0 ≤ T) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (x : ℝ) (w : NoiseSpace) :
    inner ℝ w (fixedNoiseRow T r hr x) = ∫ u in (0 : ℝ)..T, w u * r x u := by
  rw [L2.inner_def]
  calc
    _ = ∫ u, (Ioc 0 T).indicator (fun u => w u * r x u) u
        ∂volume.restrict (Ioi (0 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [fixedNoiseRow_coe T r hr x] with u hx
      rw [hx]
      by_cases hu : u ∈ Ioc 0 T <;>
        simp [fixedNoiseFunction, hu, RCLike.inner_apply, mul_comm]
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (show Ioc (0 : ℝ) T ⊆ Ioi 0 from fun _ h => h.1),
        ← intervalIntegral.integral_of_le hT]

/-- Causal and stopped cutoffs agree with their actual minimum cutoff. -/
theorem noisePrefix_noiseFeature_min {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) :
    noisePrefix T (noiseFeature r hr t) = fixedNoiseRow (min T t) r hr t := by
  rcases le_total T t with h | h
  · rw [min_eq_left h]
    exact noisePrefix_noiseFeature hT h r hr
  · rw [min_eq_right h, noiseFeature_prefix r hr ht h]
    have he := noisePrefix_noiseFeature ht (le_refl t) r hr
    rw [noiseFeature_prefix r hr ht (le_refl t)] at he
    exact he

/-- Continuity of the actual noise curve across its moving cutoff. -/
theorem noiseFeature_clamped_continuous (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) :
    Continuous (fun t : ℝ => noiseFeature r hr (max 0 t)) := by
  apply continuous_of_gram
  simp_rw [noiseFeature_inner r hr (le_max_left _ _) (le_max_left _ _)]
  have hmax : Continuous (fun t : ℝ => max 0 t) := continuous_const.max continuous_id
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (hr.comp ((hmax.comp continuous_fst.fst).prodMk continuous_snd)).mul
      (hr.comp ((hmax.comp continuous_fst.snd).prodMk continuous_snd))
  · exact (hmax.comp continuous_fst).min (hmax.comp continuous_snd)

/-- The actual projected Brownian row satisfies the strong linear response memory equation. -/
theorem fixedNoiseRow_slope_memory {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) :
    fixedNoiseRow T (clampedResponseSlope p β d) (clampedResponseSlope_continuous h) t =
      -d.multiplier t • fixedNoiseRow T (clampedResponse d) (clampedResponse_continuous h) t +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
          noisePrefix T (noiseFeature (clampedResponse d) (clampedResponse_continuous h) (max 0 z)) := by
  have htc := hT.trans ht
  have hc : Continuous (fun z => clampedMemory p β d t z •
      noisePrefix T (noiseFeature (clampedResponse d) (clampedResponse_continuous h) (max 0 z))) :=
    ((clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      ((noisePrefixL T).continuous.comp
        (noiseFeature_clamped_continuous _ (clampedResponse_continuous h)))
  apply ext_inner_left ℝ
  intro w
  rw [fixedNoiseRow_inner_test hT, inner_add_right, real_inner_smul_right,
    fixedNoiseRow_inner_test hT,
    WeightedHilbertKernel.inner_intervalIntegral w (hc.intervalIntegrable 0 t)]
  have hnoise (z : ℝ) (hz : 0 ≤ z) :
      inner ℝ w (noisePrefix T (noiseFeature (clampedResponse d) (clampedResponse_continuous h) (max 0 z))) =
        ∫ u in (0 : ℝ)..min z T, clampedResponse d z u * w u := by
    rw [max_eq_right hz, noisePrefix_noiseFeature_min hT hz,
      fixedNoiseRow_inner_test (le_min hT hz), min_comm]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  have hswap := weighted_triangle_memory_swap_integrable (clampedResponse_continuous h)
    (clampedMemory_continuous h) hT ht (noise_test_intervalIntegrable w hT)
  have hi : (∫ u in (0 : ℝ)..T, w u * clampedResponseSlope p β d t u) =
      -d.multiplier t * (∫ u in (0 : ℝ)..T, w u * clampedResponse d t u) +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z *
          (∫ u in (0 : ℝ)..min z T, clampedResponse d z u * w u) := by
    calc
      _ = ∫ u in (0 : ℝ)..T, (-d.multiplier t) * (w u * clampedResponse d t u) +
          w u * (∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hT] at hu
        dsimp only
        rw [clampedResponseSlope_eq hu.1 (hu.2.trans ht), responseSlope_linear_memory hu.1 (hu.2.trans ht)]
        ring
      _ = _ := by
        have hi1 : IntervalIntegrable (fun u => (-d.multiplier t) * (w u * clampedResponse d t u)) volume 0 T :=
          ((noise_test_intervalIntegrable w hT).mul_continuousOn
            ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).continuousOn).const_mul _
        have hi2 : IntervalIntegrable (fun u => w u * (∫ z in u..t,
            clampedMemory p β d t z * clampedResponse d z u)) volume 0 T := by
          have hcf : Continuous (fun u => ∫ z in u..t,
              clampedMemory p β d t z * clampedResponse d z u) := by
            have hif : Continuous (fun u => ∫ z in t..u,
                clampedMemory p β d t z * clampedResponse d z u) :=
              intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
                (((clampedMemory_continuous h).comp (continuous_const.prodMk continuous_snd)).mul
                  ((clampedResponse_continuous h).comp continuous_swap)) continuous_id
            apply hif.neg.congr
            intro u
            exact (intervalIntegral.integral_symm (μ := volume)
              (f := fun z => clampedMemory p β d t z * clampedResponse d z u) t u).symm
          exact (noise_test_intervalIntegrable w hT).mul_continuousOn hcf.continuousOn
        rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul, hswap]
  rw [hi]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le htc] at hz
  dsimp only
  rw [real_inner_smul_right, hnoise z hz.1]


/-- The actual root frame without its redundant causal projection. -/
theorem root_frame_clamped {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    graftTensorAdjoint (p-1) (ckTreeState h t) = (β * Real.sqrt p) •
      ∫ u in (0 : ℝ)..t, clampedResponse d t u • standardTensorPower (ckTreeState h (max 0 u)) := by
  have hf := ckTreeState_prefix_root_frame h hb ht t
  rw [ckTreeState_timePrefix h hb ht le_rfl] at hf
  rw [hf]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [max_eq_right hu.1, ckTreeState_timePrefix h hb hu.1 hu.2]

/-- Contraction of the true completed root frame with one varied tensor slot. -/
theorem root_frame_inner_updated {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin (p-1)) (w : CausalTree.Space (p-1)) :
    inner ℝ (graftTensorAdjoint (p-1) (ckTreeState h t))
      (HilbertDatum.finitePure (p-1) (fun _ => spaceDatum (p-1))
        (Function.update (fun _ => ckTreeState h t) i w)) =
      (β * Real.sqrt p) * (∫ u in (0 : ℝ)..t,
        clampedResponse d t u * clampedCorrelation d t u ^ (p-2) *
          inner ℝ (ckTreeState h (max 0 u)) w) := by
  have hc : Continuous (fun u => clampedResponse d t u • standardTensorPower (ckTreeState h (max 0 u))) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      ((ScalarHilbertKernel.finitePure_continuous (p-1) (fun _ => spaceDatum (p-1)) (fun _ => id)
        (fun _ => continuous_id)).comp (ckTreeState_clamped_continuous h hb))
  rw [root_frame_clamped h hb ht, real_inner_smul_left,
    WeightedHilbertKernel.intervalIntegral_inner _ (hc.intervalIntegrable 0 t)]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [real_inner_smul_left, TreePolynomialDrift.standardTensorPower_inner_updated,
    max_eq_right hu.1, ckTreeState_gram h hb hu.1 ht,
    h.correlation_symmetric u t hu.1 ht, clampedCorrelation_eq ht hu.1,
    show (p-1)-1=p-2 from by omega]
  ring

/-- Along the actual CK realization, the genuine polynomial gradient equals its causal memory. -/
theorem gradient_along_tree {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    β • TreePolynomialDrift.gradient p (ckTreeState h t) =
      (β * Real.sqrt p) • graftPower (ckTreeState h t) +
        ∫ u in (0 : ℝ)..t, clampedMemory p β d t u • ckTreeState h (max 0 u) := by
  have hc : Continuous (fun u => clampedMemory p β d t u • ckTreeState h (max 0 u)) :=
    ((clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      (ckTreeState_clamped_continuous h hb)
  apply ext_inner_right ℝ
  intro w
  rw [real_inner_smul_left, TreePolynomialDrift.gradient_pairing, inner_add_left,
    real_inner_smul_left, WeightedHilbertKernel.intervalIntegral_inner w (hc.intervalIntegrable 0 t)]
  simp_rw [root_frame_inner_updated h hb ht]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [real_inner_comm (graftPower (ckTreeState h t)) w]
  have hk : (∫ u in (0 : ℝ)..t, inner ℝ (clampedMemory p β d t u • ckTreeState h (max 0 u)) w) =
      β ^ 2 * (p : ℝ) * ((p : ℝ)-1) * (∫ u in (0 : ℝ)..t,
        clampedResponse d t u * clampedCorrelation d t u ^ (p-2) *
          inner ℝ (ckTreeState h (max 0 u)) w) := by
    simp only [real_inner_smul_left, clampedMemory, xiDoublePrime]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  rw [hk, Nat.cast_sub (show 1 ≤ p from by have hp:=h.spin_ge_three; omega)]
  have hs : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  norm_num only [Nat.cast_one]
  ring_nf
  rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  ring


/-- Every actual projected CK curve is C¹ on the post-cutoff open ray. -/
theorem projectedTree_contDiffOn_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T : ℝ} (hT : 0 ≤ T) :
    ContDiffOn ℝ 1 (fun x => timePrefix T (ckTreeState h x)) (Ioi T) := by
  rw [show (1 : WithTop ℕ∞) = 0+1 from by simp,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (uniqueDiffOn_Ioi T)]
  refine ⟨by simp, fun t => ContinuousLinearMap.toSpanSingleton ℝ (projectedDerivative h T t), ?_, ?_⟩
  · rw [contDiffOn_zero]
    exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (CausalTree.Space (p-1))).continuous.comp
      (projectedDerivative_continuous h hb hT)).continuousOn
  · intro t ht
    exact (projectedTree_hasDerivAt h hb hT ht).hasFDerivAt.hasFDerivWithinAt


/-- The projected leaf response is an actual strong Hilbert solution of the linear CK equation. -/
theorem stoppedLeaf_slope_memory {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) :
    stoppedLeaf T (clampedResponseSlope p β d) (clampedResponseSlope_continuous h) t =
      -d.multiplier t • stoppedLeaf T (clampedResponse d) (clampedResponse_continuous h) t +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
          leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z) := by
  have htc := hT.trans ht
  have hc : Continuous (fun z => clampedMemory p β d t z •
      leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)) :=
    ((clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      ((leafPrefix T).continuous.comp (leafResponseFeature_continuous _ (clampedResponse_continuous h)))
  have hfst : (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
      leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)).fst =
      ∫ z in (0 : ℝ)..t, clampedMemory p β d t z * clampedResponse d (max 0 z) 0 := by
    exact ((WithLp.fstL 2 ℝ ℝ NoiseSpace).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)).symm
  have hsnd : (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
      leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)).snd =
      Real.sqrt 2 • (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
        noisePrefix T (noiseFeature (clampedResponse d) (clampedResponse_continuous h) (max 0 z))) := by
    have hi := ((WithLp.sndL 2 ℝ ℝ NoiseSpace).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)).symm
    change (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
      leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)).snd =
      ∫ z in (0 : ℝ)..t, (clampedMemory p β d t z •
        leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)).snd at hi
    rw [hi, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro z _
    change clampedMemory p β d t z • noisePrefix T (Real.sqrt 2 •
        noiseFeature (clampedResponse d) (clampedResponse_continuous h) (max 0 z)) = _
    rw [noisePrefix_smul, smul_comm]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change clampedResponseSlope p β d t 0 =
      -d.multiplier t * clampedResponse d t 0 +
        (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
          leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)).fst
    rw [hfst, clampedResponseSlope_eq le_rfl htc,
      responseSlope_linear_memory le_rfl htc]
    congr 1
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le htc] at hz
    dsimp only
    rw [max_eq_right hz.1]
  · change Real.sqrt 2 • fixedNoiseRow T (clampedResponseSlope p β d)
        (clampedResponseSlope_continuous h) t =
      (-d.multiplier t) • (Real.sqrt 2 • fixedNoiseRow T (clampedResponse d)
        (clampedResponse_continuous h) t) +
        (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
          leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)).snd
    rw [hsnd, fixedNoiseRow_slope_memory h hT ht, smul_add, smul_comm (Real.sqrt 2)]


/-- The actual direct-sum projection acts on the one-leaf summand by the actual leaf projection. -/
theorem timePrefix_baseVector (m : ℕ) (T : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (x : ℝ) :
    timePrefix T (baseVector m r hr x) =
      lp.single 2 CausalTree.Tree.leaf (leafPrefix T (leafResponseFeature r hr x)) := by
  apply lp.ext
  funext τ
  by_cases hτ : τ = CausalTree.Tree.leaf
  · subst τ
    simp only [timePrefix_apply, fiberPrefix_leaf, baseVector, lp.single_apply_self]
  · simp only [timePrefix_apply, baseVector, lp.single_apply_ne _ _ _ hτ, map_zero]

/-- The actual projected base vector satisfies the full linear CK memory equation. -/
theorem projectedBase_slope_memory {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) :
    lp.single 2 CausalTree.Tree.leaf
      (stoppedLeaf T (clampedResponseSlope p β d) (clampedResponseSlope_continuous h) t) =
      -d.multiplier t • timePrefix T
        (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t) +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z • timePrefix T
          (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) z) := by
  let L := lp.singleContinuousLinearMap ℝ (fun τ : CausalTree.Tree (p-1) => (fiber τ).Carrier)
    2 CausalTree.Tree.leaf
  have hc : Continuous (fun z => clampedMemory p β d t z •
      leafPrefix T (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) z)) :=
    ((clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      ((leafPrefix T).continuous.comp (leafResponseFeature_continuous _ (clampedResponse_continuous h)))
  have hi := congrArg L (stoppedLeaf_slope_memory h hT ht)
  rw [map_add, map_smul, ← L.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)] at hi
  change lp.single 2 CausalTree.Tree.leaf _ =
    (-d.multiplier t) • lp.single 2 CausalTree.Tree.leaf _ + ∫ z in (0 : ℝ)..t, L _ at hi
  rw [hi, timePrefix_baseVector, leafPrefix_leafResponseFeature hT ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro z _
  dsimp only
  rw [map_smul, timePrefix_baseVector]
  rfl

/-- The actual tree-valued response convolution, with a continuous full-line extension. -/
@[expose] def treeMemory {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (x : ℝ) :
    CausalTree.Space (p-1) :=
  ∫ u in (0 : ℝ)..x, clampedResponse d x u • graftPower (ckTreeState h (max 0 u))

theorem treeMemory_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) : Continuous (treeMemory h) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    ((clampedResponse_continuous h).smul (((graftPower_continuous (p-1)).comp
      (ckTreeState_clamped_continuous h hb)).comp continuous_snd)) continuous_id

theorem treeMemory_volterra {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    ckTreeState h t = baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t +
      (β * Real.sqrt p) • treeMemory h t := by
  rw [ckTreeState_volterra_clamped h hb ht]
  congr 2
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only [treeMemory]
  rw [max_eq_right hu.1]

/-- The differentiated tree memory is the genuine CK memory operator applied to that memory. -/
theorem treeMemory_slope {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, clampedResponseSlope p β d t u • graftPower (ckTreeState h (max 0 u))) =
      (-d.multiplier t) • treeMemory h t +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z • treeMemory h z :=
  responseSlope_integral_identity h
    ((graftPower_continuous (p-1)).comp (ckTreeState_clamped_continuous h hb)) ht


/-- Recombination of the actual Brownian and grafted components gives the full projected CK drift. -/
theorem projectedDerivative_linear {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) :
    projectedDerivative h T t = timePrefix T
      ((-d.multiplier t) • ckTreeState h t + (β * Real.sqrt p) • graftPower (ckTreeState h t) +
        ∫ z in (0 : ℝ)..t, clampedMemory p β d t z • ckTreeState h (max 0 z)) := by
  have htc := hT.trans ht
  have hK : Continuous (fun z => clampedMemory p β d t z) :=
    (clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
  have hbase : IntervalIntegrable (fun z => clampedMemory p β d t z •
      baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) z) volume 0 t :=
    (hK.smul (baseVector_continuous _ _ _)).intervalIntegrable 0 t
  have hmem : IntervalIntegrable (fun z => clampedMemory p β d t z • treeMemory h z) volume 0 t :=
    (hK.smul (treeMemory_continuous h hb)).intervalIntegrable 0 t
  have hs : (∫ z in (0 : ℝ)..t, clampedMemory p β d t z • ckTreeState h (max 0 z)) =
      (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
        baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) z) +
      (β * Real.sqrt p) • (∫ z in (0 : ℝ)..t, clampedMemory p β d t z • treeMemory h z) := by
    calc
      _ = ∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
          baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) z +
          (β * Real.sqrt p) • (clampedMemory p β d t z • treeMemory h z) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [uIcc_of_le htc] at hz
        dsimp only
        rw [max_eq_right hz.1, treeMemory_volterra h hb hz.1, smul_add, smul_comm]
      _ = _ := by
        rw [intervalIntegral.integral_add
          (f := fun z => clampedMemory p β d t z • baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) z)
          (g := fun z => (β * Real.sqrt p) • (clampedMemory p β d t z • treeMemory h z))
          hbase ((hmem.smul (β * Real.sqrt p)).congr (fun z _ => by rfl)),
          intervalIntegral.integral_smul]
  have hbaseP : (∫ z in (0 : ℝ)..t, clampedMemory p β d t z • timePrefix T
      (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) z)) =
      timePrefix T (∫ z in (0 : ℝ)..t, clampedMemory p β d t z •
        baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) z) := by
    rw [timePrefix_intervalIntegral T hbase]
    simp_rw [timePrefix_smul]
  rw [projectedDerivative, projectedBase_slope_memory h hT ht,
    treeMemory_slope h hb htc, max_eq_right htc, hbaseP, hs, treeMemory_volterra h hb htc]
  simp only [timePrefix_add, timePrefix_smul]
  module

/-- The exact manuscript polynomial drift, proved for the actual tree curve. -/
theorem projectedDerivative_eq_drift {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) :
    projectedDerivative h T t = timePrefix T (TreePolynomialDrift.drift p β (ckTreeState h t)) := by
  rw [projectedDerivative_linear h hb hT ht]
  apply congrArg (timePrefix T)
  rw [add_assoc, ← gradient_along_tree h hb (hT.trans ht), ckTreeState_multiplier h hb (hT.trans ht)]
  unfold TreePolynomialDrift.drift
  module

/-- The exact local polynomial evolution after every causal projection. -/
theorem projectedTree_hasDerivAt_drift {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t : ℝ} (hT : 0 ≤ T) (ht : T < t) :
    HasDerivAt (fun x => timePrefix T (ckTreeState h x))
      (timePrefix T (TreePolynomialDrift.drift p β (ckTreeState h t))) t := by
  rw [← projectedDerivative_eq_drift h hb hT ht.le]
  exact projectedTree_hasDerivAt h hb hT ht


/-- The actual tree distance is exactly the physical correlation deficit. -/
theorem tree_distance_sq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ‖ckTreeState h t - ckTreeState h s‖ ^ 2 = 2 * (1 - d.C t s) := by
  rw [norm_sub_sq_real, ckTreeState_norm h hb ht, ckTreeState_norm h hb hs,
    ckTreeState_gram h hb ht hs]
  ring

/-- The conditional half-Hölder modulus has the exact source constant, uniformly in the cutoff. -/
theorem projected_derivative_holder {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {K : ℝ}
    (hK : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → 1-d.C t s ≤ K*|t-s|)
    {T t s : ℝ} (hT : 0 ≤ T) (ht : T < t) (hs : T < s) :
    ‖deriv (fun x => timePrefix T (ckTreeState h x)) t -
        deriv (fun x => timePrefix T (ckTreeState h x)) s‖ ≤
      ((1+2*β*(p : ℝ)^2*Real.sqrt p)*Real.sqrt (2*K))*Real.sqrt |t-s| := by
  have hK0 : 0 ≤ K := by
    have hi := hK 1 0 (by norm_num) le_rfl
    have hc := (hb.1 1 0 (by norm_num) le_rfl).2
    norm_num at hi
    linarith
  have hd : ‖ckTreeState h t - ckTreeState h s‖ ≤ Real.sqrt (2*K)*Real.sqrt |t-s| := by
    have hi := mul_le_mul_of_nonneg_left (hK t s (hT.trans_lt ht).le (hT.trans_lt hs).le)
      (show (0 : ℝ) ≤ 2 from by norm_num)
    rw [← tree_distance_sq h hb (hT.trans_lt ht).le (hT.trans_lt hs).le] at hi
    have hh := Real.sqrt_le_sqrt hi
    rw [Real.sqrt_sq (norm_nonneg _)] at hh
    convert hh using 1
    rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2*K)]
  rw [(projectedTree_hasDerivAt_drift h hb hT ht).deriv,
    (projectedTree_hasDerivAt_drift h hb hT hs).deriv]
  change ‖timePrefixL (p-1) T _ - timePrefixL (p-1) T _‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖TreePolynomialDrift.drift p β (ckTreeState h t) -
        TreePolynomialDrift.drift p β (ckTreeState h s)‖ := timePrefix_norm_le T _
    _ ≤ (1+2*β*(p : ℝ)^2*Real.sqrt p)*‖ckTreeState h t-ckTreeState h s‖ :=
      TreePolynomialDrift.drift_lipschitz_unit (by have hp:=h.spin_ge_three; omega) h.beta_pos.le _ _
        (ckTreeState_norm h hb (hT.trans_lt ht).le).le (ckTreeState_norm h hb (hT.trans_lt hs).le).le
    _ ≤ _ := by
      have hβ := h.beta_pos.le
      have hL : 0 ≤ 1+2*β*(p : ℝ)^2*Real.sqrt p := by positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd hL


/-- Complete source Lemma 7.2 on the actual causal-tree Hilbert space. -/
theorem local_polynomial_drift {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) :
    (∀ v : CausalTree.Space (p-1), HasFDerivAt (treeEnergy p)
      (innerSL ℝ (TreePolynomialDrift.gradient p v)) v) ∧
    (∀ T : ℝ, 0 ≤ T →
      ContDiffOn ℝ 1 (fun x => timePrefix T (ckTreeState h x)) (Ioi T) ∧
      ∀ t : ℝ, T < t → HasDerivAt (fun x => timePrefix T (ckTreeState h x))
        (timePrefix T (TreePolynomialDrift.drift p β (ckTreeState h t))) t) ∧
    (∀ v w : CausalTree.Space (p-1), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖TreePolynomialDrift.drift p β v-TreePolynomialDrift.drift p β w‖ ≤
        (1+2*β*(p : ℝ)^2*Real.sqrt p)*‖v-w‖) ∧
    (∀ K : ℝ, (∀ t s : ℝ, 0 ≤ t → 0 ≤ s → 1-d.C t s ≤ K*|t-s|) →
      ∀ T t s : ℝ, 0 ≤ T → T < t → T < s →
        ‖deriv (fun x => timePrefix T (ckTreeState h x)) t -
          deriv (fun x => timePrefix T (ckTreeState h x)) s‖ ≤
          ((1+2*β*(p : ℝ)^2*Real.sqrt p)*Real.sqrt (2*K))*Real.sqrt |t-s|) := by
  refine ⟨TreePolynomialDrift.energy_hasFDerivAt_gradient p, ?_, ?_, ?_⟩
  · intro T hT
    exact ⟨projectedTree_contDiffOn_one h hb hT,
      fun t ht => projectedTree_hasDerivAt_drift h hb hT ht⟩
  · intro v w hv hw
    exact TreePolynomialDrift.drift_lipschitz_unit (by have hp:=h.spin_ge_three; omega)
      h.beta_pos.le v w hv hw
  · intro K hK T t s hT ht hs
    exact projected_derivative_holder h hb hK hT ht hs

/-- The standing CK equations already prove the physical inputs used by the source receipt. -/
theorem local_polynomial_drift_of_equations {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    (∀ T : ℝ, 0 ≤ T →
      ContDiffOn ℝ 1 (fun x => timePrefix T (ckTreeState h x)) (Ioi T) ∧
      ∀ t : ℝ, T < t → HasDerivAt (fun x => timePrefix T (ckTreeState h x))
        (timePrefix T (TreePolynomialDrift.drift p β (ckTreeState h t))) t) :=
  (local_polynomial_drift h (CKPhysicalConsequences.physical_bounds_of_equations h)).2.1

end SphericalAging.ProjectedTreeDrift
