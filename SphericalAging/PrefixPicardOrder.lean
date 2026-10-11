module

public import SphericalAging.PrefixReflection

public section

/-! Actual entrywise order of projected Picard Gram kernels and their strong limits. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory Filter
namespace SphericalAging.PrefixPicardOrder
open CausalTree CausalTreeRealization ProjectedTreeDrift PrefixReflection
  CKSpecification GreenCovariance WeightedHilbertKernel
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- Exact Gram kernel of two stopped causal Brownian rows at arbitrary nonnegative times. -/
theorem projectedNoise_inner {T t s : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) :
    inner ℝ (noisePrefix T (noiseFeature r hr t)) (noisePrefix T (noiseFeature r hr s)) =
      ∫ u in (0 : ℝ)..min T (min t s), r t u*r s u := by
  rw [L2.inner_def]
  calc
    _ = ∫ u, (Iic T).indicator ((Ioc 0 (min t s)).indicator (fun u => r t u*r s u)) u
        ∂volume.restrict (Ioi (0 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [noisePrefix_coe T (noiseFeature r hr t), noisePrefix_coe T (noiseFeature r hr s),
        noiseFeature_coe r hr t, noiseFeature_coe r hr s] with u hpt hps hft hfs
      rw [hpt, hps]
      by_cases hu : u ∈ Iic T
      · rw [indicator_of_mem hu, indicator_of_mem hu, indicator_of_mem hu, hft, hfs]
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        rw [mul_comm]
        exact WhiteCovarianceKernel.rowCut_mul r t s u
      · simp only [indicator_of_notMem hu, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_zero]
    _ = ∫ u, (Ioc 0 (min T (min t s))).indicator (fun u => r t u*r s u) u
        ∂volume.restrict (Ioi (0 : ℝ)) := by
      have he : Iic T ∩ Ioc (0 : ℝ) (min t s) = Ioc 0 (min T (min t s)) := by
        ext u
        simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
        tauto
      simp_rw [Set.indicator_indicator, he]
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (show Ioc (0 : ℝ) (min T (min t s)) ⊆ Ioi 0 from fun _ h => h.1),
        ← intervalIntegral.integral_of_le (le_min hT (le_min ht hs))]

/-- The complete projected leaf Gram kernel has exactly the minimum of all three cutoffs. -/
theorem projectedBase_inner_general {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t s : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s)) =
      clampedResponse d t 0*clampedResponse d s 0 +
        2*(∫ u in (0 : ℝ)..min T (min t s), clampedResponse d t u*clampedResponse d s u) := by
  rw [timePrefix_baseVector, timePrefix_baseVector, lp.inner_single_left, lp.single_apply_self]
  rw [WithLp.prod_inner_apply]
  change (leafPrefix T (leafResponseFeature _ _ s)).fst *
      (leafPrefix T (leafResponseFeature _ _ t)).fst +
      inner ℝ (leafPrefix T (leafResponseFeature _ _ t)).snd
        (leafPrefix T (leafResponseFeature _ _ s)).snd = _
  rw [leafPrefix_fst, leafPrefix_fst, leafPrefix_snd, leafPrefix_snd]
  simp only [leafResponseFeature, max_eq_right ht, max_eq_right hs,
    WithLp.fst, WithLp.snd, WithLp.ofLp_toLp]
  rw [noisePrefix_smul, noisePrefix_smul, real_inner_smul_left, real_inner_smul_right,
    projectedNoise_inner hT ht hs]
  rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The actual stopped leaf kernel is nonnegative and no larger than the actual full leaf kernel. -/
theorem projectedBase_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ inner ℝ (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s)) ∧
    inner ℝ (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s)) ≤
      inner ℝ (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t)
        (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s) := by
  rw [projectedBase_inner_general h hT ht hs, baseVector_inner, leafResponseFeature_inner,
    max_eq_right ht, max_eq_right hs]
  have hc : Continuous (fun u => clampedResponse d t u*clampedResponse d s u) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).mul
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))
  have hn (u : ℝ) (hu : u ∈ Icc 0 (min t s)) :
      0 ≤ clampedResponse d t u*clampedResponse d s u := by
    rw [clampedResponse_eq hu.1 (hu.2.trans (min_le_left _ _)),
      clampedResponse_eq hu.1 (hu.2.trans (min_le_right _ _))]
    exact mul_nonneg (hb.2 t u hu.1 (hu.2.trans (min_le_left _ _)))
      (hb.2 s u hu.1 (hu.2.trans (min_le_right _ _)))
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..min T (min t s), clampedResponse d t u*clampedResponse d s u :=
    intervalIntegral.integral_nonneg (le_min hT (le_min ht hs))
      (fun u hu => hn u ⟨hu.1,hu.2.trans (min_le_right _ _)⟩)
  have hle : (∫ u in (0 : ℝ)..min T (min t s), clampedResponse d t u*clampedResponse d s u) ≤
      ∫ u in (0 : ℝ)..min t s, clampedResponse d t u*clampedResponse d s u := by
    apply intervalIntegral.integral_mono_interval le_rfl (le_min hT (le_min ht hs))
      (min_le_right _ _)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _
        (fun u hu => hn u (Ioc_subset_Icc_self hu)))
    · exact hc.intervalIntegrable 0 (min t s)
  rw [clampedResponse_eq le_rfl ht, clampedResponse_eq le_rfl hs] at *
  constructor
  · exact add_nonneg (mul_nonneg (hb.2 t 0 le_rfl ht) (hb.2 s 0 le_rfl hs))
      (mul_nonneg (by norm_num) h0)
  · linarith

/-- Actual projected finite-height Picard stage. -/
@[expose] def projectedStage {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T : ℝ) (n : ℕ) (t : ℝ) : CausalTree.Space (p-1) :=
  timePrefix T (ckTreeIterate p β d (clampedResponse_continuous h) n t)

@[expose] def stageKernel {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T : ℝ) (n : ℕ) (t s : ℝ) := inner ℝ (projectedStage h T n t) (projectedStage h T n s)

theorem projectedStage_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (n : ℕ) : Continuous (projectedStage h T n) :=
  (timePrefixL (p-1) T).continuous.comp
    (treeIterate_continuous (p-1) (β*Real.sqrt p) _ (clampedResponse_continuous h) n)

theorem stageKernel_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (n : ℕ) : Continuous (Function.uncurry (stageKernel h T n)) :=
  ((projectedStage_continuous h T n).comp continuous_fst).inner
    ((projectedStage_continuous h T n).comp continuous_snd)

/-- Actual projected response memory of a finite Picard stage. -/
@[expose] def projectedStageMemory {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T : ℝ) (n : ℕ) (t : ℝ) : CausalTree.Space (p-1) :=
  ∫ u in (0 : ℝ)..t, clampedResponse d t u • graftPower (projectedStage h T n u)

theorem projectedStageMemory_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (n : ℕ) (t a b : ℝ) :
    IntervalIntegrable (fun u => clampedResponse d t u • graftPower (projectedStage h T n u))
      volume a b :=
  (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
    ((graftPower_continuous (p-1)).comp (projectedStage_continuous h T n))).intervalIntegrable a b

theorem projectedStage_succ {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    projectedStage h T (n+1) t =
      timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t) +
      (β*Real.sqrt p) • projectedStageMemory h T n t := by
  unfold projectedStage ckTreeIterate
  rw [treeIterate, max_eq_right ht, timePrefix_add, timePrefix_smul,
    timePrefix_intervalIntegral T (treeIterate_integrable (p-1) (β*Real.sqrt p) _
      (clampedResponse_continuous h) n t 0 t)]
  simp_rw [timePrefix_smul, timePrefix_graftPower]
  rfl

theorem projectedStageMemory_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (n : ℕ) (t s : ℝ) :
    inner ℝ (projectedStageMemory h T n t) (projectedStageMemory h T n s) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u*clampedResponse d s v*stageKernel h T n u v^(p-1) := by
  rw [projectedStageMemory, intervalIntegral_inner _ (projectedStageMemory_integrable h T n t 0 t)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [projectedStageMemory, inner_intervalIntegral _ (projectedStageMemory_integrable h T n s 0 s)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [real_inner_smul_left, real_inner_smul_right, graftPower_inner]
  unfold stageKernel
  ring

theorem projectedBase_inner_stageMemory {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (n : ℕ) (t s : ℝ) :
    inner ℝ (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (projectedStageMemory h T n s) = 0 := by
  rw [projectedStageMemory, inner_intervalIntegral _ (projectedStageMemory_integrable h T n s 0 s)]
  have he (u : ℝ) : inner ℝ
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (clampedResponse d s u • graftPower (projectedStage h T n u)) = 0 := by
    rw [real_inner_smul_right]
    exact mul_eq_zero_of_right _ (projectedBase_inner_graft T _ _ t _)
  simp_rw [he]
  simp

/-- The stopped stages obey the same genuine nonlinear Gram recursion as full stages. -/
theorem stageKernel_succ {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (n : ℕ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    stageKernel h T (n+1) t s =
      inner ℝ (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
        (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s)) +
      (β*Real.sqrt p)^2*(∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u*clampedResponse d s v*stageKernel h T n u v^(p-1)) := by
  unfold stageKernel
  rw [projectedStage_succ h T n ht, projectedStage_succ h T n hs]
  have he : inner ℝ (projectedStageMemory h T n t)
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s)) = 0 :=
    (real_inner_comm _ _).trans (projectedBase_inner_stageMemory h T n s t)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    projectedBase_inner_stageMemory, he, mul_zero, zero_mul, add_zero, zero_add,
    projectedStageMemory_inner, stageKernel]
  ring

/-- The full Picard Gram integrand is an actual continuous real kernel. -/
theorem fullStageKernel_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (n : ℕ) :
    Continuous (fun z : ℝ×ℝ => inner ℝ (ckTreeIterate p β d (clampedResponse_continuous h) n z.1)
      (ckTreeIterate p β d (clampedResponse_continuous h) n z.2)) :=
  ((treeIterate_continuous (p-1) (β*Real.sqrt p) _ (clampedResponse_continuous h) n).comp continuous_fst).inner
    ((treeIterate_continuous (p-1) (β*Real.sqrt p) _ (clampedResponse_continuous h) n).comp continuous_snd)

/-- Entrywise projected/full Picard Gram order, proved from the stopped Brownian
base and the actual monotone nonlinear convolution, without a cone-complement hypothesis. -/
theorem stageKernel_order {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → 0 ≤ stageKernel h T n t s ∧
      stageKernel h T n t s ≤ inner ℝ (ckTreeIterate p β d (clampedResponse_continuous h) n t)
        (ckTreeIterate p β d (clampedResponse_continuous h) n s) := by
  induction n with
  | zero =>
    intro t s ht hs
    exact projectedBase_bounds h hb hT ht hs
  | succ n ih =>
    intro t s ht hs
    have hbase := projectedBase_bounds h hb hT ht hs
    have hr (u v : ℝ) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 s) :
        0 ≤ clampedResponse d t u*clampedResponse d s v := by
      rw [clampedResponse_eq hu.1 hu.2, clampedResponse_eq hv.1 hv.2]
      exact mul_nonneg (hb.2 t u hu.1 hu.2) (hb.2 s v hv.1 hv.2)
    let F : ℝ → ℝ → ℝ := fun u v =>
      clampedResponse d t u*clampedResponse d s v*stageKernel h T n u v^(p-1)
    let G : ℝ → ℝ → ℝ := fun u v =>
      clampedResponse d t u*clampedResponse d s v*
        inner ℝ (ckTreeIterate p β d (clampedResponse_continuous h) n u)
          (ckTreeIterate p β d (clampedResponse_continuous h) n v)^(p-1)
    have hR : Continuous (fun z : ℝ×ℝ => clampedResponse d t z.1*clampedResponse d s z.2) :=
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_fst)).mul
        ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_snd))
    have hF : Continuous (Function.uncurry F) := hR.mul ((stageKernel_continuous h T n).pow (p-1))
    have hG : Continuous (Function.uncurry G) := hR.mul ((fullStageKernel_continuous h n).pow (p-1))
    have hnon : 0 ≤ ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v := by
      have hz := CovarianceIteration.rectangle_integral_mono
        (F := fun _ _ => 0) continuous_const hF ht hs
        (fun u hu v hv => mul_nonneg (hr u v hu hv) (pow_nonneg (ih u v hu.1 hv.1).1 _))
      simpa only [intervalIntegral.integral_zero] using hz
    have hle : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v) ≤
        ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, G u v := by
      apply CovarianceIteration.rectangle_integral_mono hF hG ht hs
      intro u hu v hv
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (ih u v hu.1 hv.1).1 (ih u v hu.1 hv.1).2 _) (hr u v hu hv)
    rw [stageKernel_succ h T n ht hs]
    change 0 ≤ _ + (β*Real.sqrt p)^2*(∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v) ∧ _
    constructor
    · exact add_nonneg hbase.1 (mul_nonneg (sq_nonneg _) hnon)
    · have hrec := treeIterate_gram_succ (p-1) (β*Real.sqrt p) (clampedResponse d)
        (clampedResponse_continuous h) n t s
      rw [max_eq_right ht, max_eq_right hs] at hrec
      change inner ℝ (ckTreeIterate p β d (clampedResponse_continuous h) (n+1) t)
        (ckTreeIterate p β d (clampedResponse_continuous h) (n+1) s) = _ at hrec
      rw [hrec]
      exact add_le_add hbase.2 (mul_le_mul_of_nonneg_left hle (sq_nonneg _))

/-- The actual projected stages converge strongly, by continuity of the genuine cutoff projection. -/
theorem projectedStage_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => projectedStage h T n t) atTop (nhds (prefixVector h T t)) :=
  ((timePrefixL (p-1) T).continuous.tendsto (ckTreeState h t)).comp (ckTreeIterate_tendsto h hb ht)

theorem stageKernel_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Tendsto (fun n => stageKernel h T n t s) atTop (nhds (prefixKernel h T t s)) :=
  (projectedStage_tendsto h hb T ht).inner (projectedStage_tendsto h hb T hs)

/-- Physical entrywise bounds on the actual prefix kernel, obtained from proved finite-stage order. -/
theorem prefixKernel_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ prefixKernel h T t s ∧ prefixKernel h T t s ≤ d.C t s := by
  have htend := stageKernel_tendsto h hb T ht hs
  constructor
  · exact ge_of_tendsto' htend (fun n => (stageKernel_order h hb hT n t s ht hs).1)
  · apply le_of_tendsto' htend
    intro n
    have hord := (stageKernel_order h hb hT n t s ht hs).2
    rw [ckTreeIterate_gram p β d (clampedResponse_continuous h) n ht hs] at hord
    exact hord.trans (GlobalCKExtension.global_covarianceIterate_bounds h hb n ht hs).2

/-- The finite future-prefix kernels lie in the actual physical interval [0,C]⊆[0,1]. -/
theorem futureKernel_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T a b : ℝ}
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    0 ≤ futureKernel h T a b ∧ futureKernel h T a b ≤ d.C (T+a) (T+b) ∧
      futureKernel h T a b ≤ 1 := by
  have hq := prefixKernel_bounds h hb hT (add_nonneg hT ha) (add_nonneg hT hb')
  exact ⟨hq.1,hq.2,hq.2.trans (hb.1 _ _ (add_nonneg hT ha) (add_nonneg hT hb')).2⟩

end SphericalAging.PrefixPicardOrder
