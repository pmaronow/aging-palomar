module

public import SphericalAging.TreeLeafTensor
public import SphericalAging.WhiteCovarianceKernel
public import SphericalAging.WeightedHilbertKernel
public import SphericalAging.GreenCovarianceClosure
public import SphericalAging.CovarianceIteration
public import SphericalAging.GlobalCKExtension
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual time-dependent tree Volterra iterates and their causal Hilbert realization. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory UniformSpace Filter
namespace SphericalAging.CausalTreeRealization
open CausalTree CKSpecification GreenCovariance ScalarHilbertKernel WeightedHilbertKernel
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The actual causal response row in the Brownian leaf space `L²((0,∞))`. -/
@[expose] def noiseFeature (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    NoiseSpace :=
  ((WhiteCovarianceKernel.rowCut_memLp r hr t).mono_measure Measure.restrict_le_self).toLp
    (WhiteCovarianceKernel.rowCut r t)

theorem noiseFeature_coe (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    (noiseFeature r hr t : ℝ → ℝ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      WhiteCovarianceKernel.rowCut r t :=
  ((WhiteCovarianceKernel.rowCut_memLp r hr t).mono_measure Measure.restrict_le_self).coeFn_toLp

theorem noiseFeature_inner (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (noiseFeature r hr t) (noiseFeature r hr s) =
      ∫ u in (0 : ℝ)..min t s, r t u * r s u := by
  rw [L2.inner_def]
  calc
    _ = ∫ u, WhiteCovarianceKernel.rowCut r t u * WhiteCovarianceKernel.rowCut r s u
        ∂volume.restrict (Ioi (0 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [noiseFeature_coe r hr t, noiseFeature_coe r hr s] with u htu hsu
      rw [htu, hsu]
      simp [RCLike.inner_apply, mul_comm]
    _ = ∫ u, (Ioc 0 (min t s)).indicator (fun u => r t u * r s u) u
        ∂volume.restrict (Ioi (0 : ℝ)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (WhiteCovarianceKernel.rowCut_mul r t s)
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (show Ioc (0 : ℝ) (min t s) ⊆ Ioi 0 from fun _ h => h.1),
        ← intervalIntegral.integral_of_le (le_min ht hs)]

/-- Extend the actual positive-time leaf response curve continuously through zero. -/
@[expose] def leafResponseFeature (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    LeafSpace := WithLp.toLp 2 (r (max 0 t) 0, Real.sqrt 2 • noiseFeature r hr (max 0 t))

theorem leafResponseFeature_inner (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    (t s : ℝ) :
    inner ℝ (leafResponseFeature r hr t) (leafResponseFeature r hr s) =
      r (max 0 t) 0 * r (max 0 s) 0 +
        2 * ∫ u in (0 : ℝ)..min (max 0 t) (max 0 s), r (max 0 t) u * r (max 0 s) u := by
  simp only [leafResponseFeature, WithLp.prod_inner_apply,
    real_inner_smul_left, real_inner_smul_right,
    noiseFeature_inner r hr (le_max_left _ _) (le_max_left _ _), RCLike.inner_apply,
    starRingEnd_apply, star_trivial]
  have h : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rw [← mul_assoc, h]
  ring

/-- Continuity of a concrete Hilbert curve follows from continuity of its Gram kernel. -/
theorem continuous_of_gram {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : X → E)
    (hg : Continuous (fun z : X × X => inner ℝ (f z.1) (f z.2))) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hn (y : X) : ‖f y - f x‖ =
      Real.sqrt (inner ℝ (f y) (f y) - 2 * inner ℝ (f y) (f x) + inner ℝ (f x) (f x)) := by
    rw [real_inner_self_eq_norm_sq (f y), real_inner_self_eq_norm_sq (f x),
      ← norm_sub_sq_real, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hn]
  have hd : Continuous (fun y => inner ℝ (f y) (f y)) :=
    hg.comp (continuous_id.prodMk continuous_id)
  have hc : Continuous (fun y => inner ℝ (f y) (f x)) :=
    hg.comp (continuous_id.prodMk continuous_const)
  have hp : ContinuousAt (fun y => inner ℝ (f y) (f y) -
      2 * inner ℝ (f y) (f x) + inner ℝ (f x) (f x)) x :=
    (hd.continuousAt.sub (hc.continuousAt.const_mul 2)).add continuousAt_const
  have hh := hp.sqrt
  change Tendsto (fun y => Real.sqrt
    (inner ℝ (f y) (f y) - 2 * inner ℝ (f y) (f x) + inner ℝ (f x) (f x)))
      (nhds x) (nhds (Real.sqrt
        (inner ℝ (f x) (f x) - 2 * inner ℝ (f x) (f x) + inner ℝ (f x) (f x)))) at hh
  have hz : inner ℝ (f x) (f x) - 2 * inner ℝ (f x) (f x) + inner ℝ (f x) (f x) = 0 := by ring
  simpa only [hz, Real.sqrt_zero] using hh

theorem leafResponseFeature_continuous (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) : Continuous (leafResponseFeature r hr) := by
  apply continuous_of_gram
  simp_rw [leafResponseFeature_inner]
  have hmax : Continuous (fun t : ℝ => max 0 t) := continuous_const.max continuous_id
  have hw : Continuous (fun z : ℝ × ℝ =>
      ∫ u in (0 : ℝ)..min (max 0 z.1) (max 0 z.2),
        r (max 0 z.1) u * r (max 0 z.2) u) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (hr.comp ((hmax.comp continuous_fst.fst).prodMk continuous_snd)).mul
        (hr.comp ((hmax.comp continuous_fst.snd).prodMk continuous_snd))
    · exact (hmax.comp continuous_fst).min (hmax.comp continuous_snd)
  exact ((hr.comp ((hmax.comp continuous_fst).prodMk continuous_const)).mul
    (hr.comp ((hmax.comp continuous_snd).prodMk continuous_const))).add
      (continuous_const.mul hw)

/-- The one-leaf response vector, in the actual causal tree space. -/
@[expose] def baseVector (m : ℕ) (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    CausalTree.Space m := lp.single 2 CausalTree.Tree.leaf (leafResponseFeature r hr t)

theorem baseVector_continuous (m : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) : Continuous (baseVector m r hr) :=
  (lp.singleContinuousLinearMap ℝ (fun t : CausalTree.Tree m => (fiber t).Carrier) 2
    CausalTree.Tree.leaf).continuous.comp (leafResponseFeature_continuous r hr)

theorem graftPower_inner {m : ℕ} (v w : CausalTree.Space m) :
    inner ℝ (graftPower v) (graftPower w) = (inner ℝ v w) ^ m := by
  rw [← graftTensor_power, ← graftTensor_power, (graftTensor m).inner_map_map]
  change inner ℝ (HilbertDatum.finitePure m (fun _ => spaceDatum m) (fun _ => v))
    (HilbertDatum.finitePure m (fun _ => spaceDatum m) (fun _ => w)) = _
  rw [HilbertDatum.inner_finitePure]
  simp

theorem graftPower_continuous (m : ℕ) : Continuous (@graftPower m) := by
  have hp : Continuous (@standardTensorPower m) :=
    finitePure_continuous m (fun _ => spaceDatum m) (fun _ => id) (fun _ => continuous_id)
  convert (graftTensor m).continuous.comp hp using 1
  funext v
  exact (graftTensor_power v).symm

/-- Actual tree-valued Volterra Picard iterates, with finite height at each stage. -/
@[expose] def treeIterate (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) :
    ℕ → ℝ → CausalTree.Space m
  | 0, t => baseVector m r hr t
  | n + 1, t => baseVector m r hr t + a •
      ∫ u in (0 : ℝ)..max 0 t, r (max 0 t) u • graftPower (treeIterate m a r hr n u)

theorem treeIterate_continuous (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) : Continuous (treeIterate m a r hr n) := by
  induction n with
  | zero => exact baseVector_continuous m r hr
  | succ n ih =>
    apply (baseVector_continuous m r hr).add
    have hi : Continuous (fun t : ℝ =>
        ∫ u in (0 : ℝ)..max 0 t, r (max 0 t) u • graftPower (treeIterate m a r hr n u)) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      · exact (hr.comp ((continuous_const.max continuous_fst).prodMk continuous_snd)).smul
          ((graftPower_continuous m).comp (ih.comp continuous_snd))
      · exact continuous_const.max continuous_id
    exact (show Continuous (fun _ : ℝ => a) from continuous_const).smul hi

theorem treeIterate_integrable (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) (t u v : ℝ) :
    IntervalIntegrable (fun s => r t s • graftPower (treeIterate m a r hr n s)) volume u v :=
  ((hr.comp (continuous_const.prodMk continuous_id)).smul
    ((graftPower_continuous m).comp (treeIterate_continuous m a r hr n))).intervalIntegrable u v

theorem baseVector_inner (m : ℕ) (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    (t s : ℝ) : inner ℝ (baseVector m r hr t) (baseVector m r hr s) =
      inner ℝ (leafResponseFeature r hr t) (leafResponseFeature r hr s) := by
  rw [baseVector, lp.inner_single_left]
  change inner ℝ (leafResponseFeature r hr t)
    (lp.single (E := fun t : CausalTree.Tree m => (fiber t).Carrier) 2
      CausalTree.Tree.leaf (leafResponseFeature r hr s) CausalTree.Tree.leaf) = _
  rw [lp.single_apply_self]

theorem baseVector_inner_graft (m : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) (w : RootTensorSpace m) :
    inner ℝ (baseVector m r hr t) (graft w) = 0 := by
  rw [baseVector, lp.inner_single_left]
  change inner ℝ (leafResponseFeature r hr t) (graft w CausalTree.Tree.leaf) = 0
  rw [graft_leaf, inner_zero_right]

theorem baseVector_heightPrefix (m : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) (j : ℕ) :
    heightPrefix j (baseVector m r hr t) = baseVector m r hr t := by
  ext τ
  by_cases h : τ = CausalTree.Tree.leaf
  · subst τ
    simp
  · have hz : baseVector m r hr t τ = 0 := lp.single_apply_ne _ _ _ h
    rw [heightPrefix_apply, hz]
    split_ifs <;> rfl

@[expose] def heightPrefixL (m j : ℕ) : CausalTree.Space m →L[ℝ] CausalTree.Space m :=
  ({ toFun := heightPrefix j
     map_add' := heightPrefix_add j
     map_smul' := heightPrefix_smul j } : CausalTree.Space m →ₗ[ℝ] CausalTree.Space m).mkContinuous
       1 (fun v => by
         change ‖mask {t | t.height ≤ j} v‖ ≤ 1 * ‖v‖
         simpa only [one_mul] using mask_norm_le {t | t.height ≤ j} v)

theorem heightPrefix_intervalIntegral {m : ℕ} (j : ℕ) {f : ℝ → CausalTree.Space m}
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    heightPrefix j (∫ u in a..b, f u) = ∫ u in a..b, heightPrefix j (f u) :=
  ((heightPrefixL m j).intervalIntegral_comp_comm hf).symm

/-- Every Picard stage agrees exactly with all earlier height truncations. -/
theorem treeIterate_heightPrefix (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n j : ℕ) (t : ℝ) :
    heightPrefix j (treeIterate m a r hr n t) = treeIterate m a r hr (min j n) t := by
  induction n generalizing j t with
  | zero => simpa only [treeIterate, min_zero] using baseVector_heightPrefix m r hr t j
  | succ n ih =>
    cases j with
    | zero =>
      rw [treeIterate, heightPrefix_add, heightPrefix_smul,
        heightPrefix_intervalIntegral 0 (treeIterate_integrable m a r hr n (max 0 t) 0 (max 0 t))]
      simp only [heightPrefix_smul, graftPower_prefix_zero, smul_zero,
        intervalIntegral.integral_zero, zero_smul, add_zero]
      exact baseVector_heightPrefix m r hr t 0
    | succ j =>
      rw [treeIterate, heightPrefix_add, heightPrefix_smul,
        heightPrefix_intervalIntegral (j + 1) (treeIterate_integrable m a r hr n (max 0 t) 0 (max 0 t)),
        baseVector_heightPrefix]
      simp only [heightPrefix_smul, graftPower_heightPrefix, ih, min_add_add_right]
      rfl

theorem treeIterate_heightPrefix_self (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) (t : ℝ) :
    heightPrefix n (treeIterate m a r hr n t) = treeIterate m a r hr n t := by
  rw [treeIterate_heightPrefix, min_self]

theorem treeIterate_consistent (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) {n k : ℕ} (hnk : n ≤ k) (t : ℝ) :
    heightPrefix n (treeIterate m a r hr k t) = treeIterate m a r hr n t := by
  rw [treeIterate_heightPrefix, min_eq_left hnk]

@[expose] def memoryVector (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) (t : ℝ) : CausalTree.Space m :=
  ∫ u in (0 : ℝ)..max 0 t, r (max 0 t) u • graftPower (treeIterate m a r hr n u)

theorem baseVector_inner_memoryVector (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) (t s : ℝ) :
    inner ℝ (baseVector m r hr t) (memoryVector m a r hr n s) = 0 := by
  rw [memoryVector, inner_intervalIntegral _
    (treeIterate_integrable m a r hr n (max 0 s) 0 (max 0 s))]
  have hz (u : ℝ) : inner ℝ (baseVector m r hr t)
      (r (max 0 s) u • graftPower (treeIterate m a r hr n u)) = 0 := by
    rw [real_inner_smul_right]
    exact mul_eq_zero_of_right _ (baseVector_inner_graft m r hr t _)
  simp_rw [hz]
  simp

theorem memoryVector_inner (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) (t s : ℝ) :
    inner ℝ (memoryVector m a r hr n t) (memoryVector m a r hr n s) =
      ∫ u in (0 : ℝ)..max 0 t, ∫ v in (0 : ℝ)..max 0 s,
        r (max 0 t) u * r (max 0 s) v *
          inner ℝ (treeIterate m a r hr n u) (treeIterate m a r hr n v) ^ m := by
  rw [memoryVector, intervalIntegral_inner _
    (treeIterate_integrable m a r hr n (max 0 t) 0 (max 0 t))]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [memoryVector, inner_intervalIntegral _
    (treeIterate_integrable m a r hr n (max 0 s) 0 (max 0 s))]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [real_inner_smul_left, real_inner_smul_right, graftPower_inner]
  ring

/-- The Gram kernel of the genuine tree Picard stage is the covariance Picard stage. -/
theorem treeIterate_gram_succ (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) (t s : ℝ) :
    inner ℝ (treeIterate m a r hr (n + 1) t) (treeIterate m a r hr (n + 1) s) =
      inner ℝ (baseVector m r hr t) (baseVector m r hr s) + a ^ 2 *
        ∫ u in (0 : ℝ)..max 0 t, ∫ v in (0 : ℝ)..max 0 s,
          r (max 0 t) u * r (max 0 s) v *
            inner ℝ (treeIterate m a r hr n u) (treeIterate m a r hr n v) ^ m := by
  change inner ℝ (baseVector m r hr t + a • memoryVector m a r hr n t)
    (baseVector m r hr s + a • memoryVector m a r hr n s) = _
  have hm : inner ℝ (memoryVector m a r hr n t) (baseVector m r hr s) = 0 :=
    (real_inner_comm _ _).trans (baseVector_inner_memoryVector m a r hr n s t)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    baseVector_inner_memoryVector, hm, mul_zero, zero_mul, add_zero, zero_add, memoryVector_inner]
  ring

/-- The tree iterates in the exact manuscript interaction normalization. -/
@[expose] def ckTreeIterate (p : ℕ) (β : ℝ) (d : CKData)
    (hr : Continuous (Function.uncurry (clampedResponse d))) : ℕ → ℝ → CausalTree.Space (p - 1) :=
  treeIterate (p - 1) (β * Real.sqrt p) (clampedResponse d) hr

theorem ck_baseVector_gram (p : ℕ) (β : ℝ) (d : CKData)
    (hr : Continuous (Function.uncurry (clampedResponse d))) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (baseVector (p - 1) (clampedResponse d) hr t)
      (baseVector (p - 1) (clampedResponse d) hr s) = CovarianceIteration.baseCovariance d t s := by
  rw [baseVector_inner, leafResponseFeature_inner, max_eq_right ht, max_eq_right hs]
  rfl

/-- The actual tree stage has exactly the covariance iterate's Gram kernel. -/
theorem ckTreeIterate_gram (p : ℕ) (β : ℝ) (d : CKData)
    (hr : Continuous (Function.uncurry (clampedResponse d))) (n : ℕ) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (ckTreeIterate p β d hr n t) (ckTreeIterate p β d hr n s) =
      CovarianceIteration.covarianceIterate p β d n t s := by
  induction n generalizing t s with
  | zero => exact ck_baseVector_gram p β d hr ht hs
  | succ n ih =>
    change inner ℝ (treeIterate (p - 1) (β * Real.sqrt p) (clampedResponse d) hr (n + 1) t)
      (treeIterate (p - 1) (β * Real.sqrt p) (clampedResponse d) hr (n + 1) s) = _
    rw [treeIterate_gram_succ, max_eq_right ht, max_eq_right hs,
      ck_baseVector_gram p β d hr ht hs]
    have hc : (β * Real.sqrt p) ^ 2 = β ^ 2 * (p : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    rw [hc]
    change CovarianceIteration.baseCovariance d t s + β ^ 2 * (p : ℝ) *
      (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u * clampedResponse d s v *
          inner ℝ (ckTreeIterate p β d hr n u) (ckTreeIterate p β d hr n v) ^ (p - 1)) = _
    congr 2
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hs] at hv
    dsimp only
    rw [ih hu.1 hv.1]

theorem ckTreeIterate_norm_sq (p : ℕ) (β : ℝ) (d : CKData)
    (hr : Continuous (Function.uncurry (clampedResponse d))) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖ckTreeIterate p β d hr n t‖ ^ 2 = CovarianceIteration.covarianceIterate p β d n t t := by
  rw [← real_inner_self_eq_norm_sq, ckTreeIterate_gram p β d hr n ht ht]

theorem heightPrefix_orthogonal_complement {m : ℕ} (j : ℕ) (v w : CausalTree.Space m) :
    inner ℝ (heightPrefix j v) (w - heightPrefix j w) = 0 :=
  idempotent_contraction_orthogonal (heightPrefixL m j)
    (fun x => by
      change heightPrefix j (heightPrefix j x) = heightPrefix j x
      rw [heightPrefix_comp, min_self])
    (fun x => mask_norm_le {t | t.height ≤ j} x) v w

theorem heightPrefix_complement_norm_sq {m : ℕ} (j : ℕ) (v : CausalTree.Space m) :
    ‖v - heightPrefix j v‖ ^ 2 = ‖v‖ ^ 2 - ‖heightPrefix j v‖ ^ 2 := by
  have h := norm_add_sq_real (heightPrefix j v) (v - heightPrefix j v)
  rw [add_sub_cancel, heightPrefix_orthogonal_complement, mul_zero, add_zero] at h
  linarith

/-- Distances between actual tree stages are exactly the unfilled height mass. -/
theorem treeIterate_dist_sq (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) {n k : ℕ} (hnk : n ≤ k) (t : ℝ) :
    dist (treeIterate m a r hr n t) (treeIterate m a r hr k t) ^ 2 =
      ‖treeIterate m a r hr k t‖ ^ 2 - ‖treeIterate m a r hr n t‖ ^ 2 := by
  rw [dist_comm, dist_eq_norm, ← treeIterate_consistent m a r hr hnk t]
  exact heightPrefix_complement_norm_sq n _

/-- Scalar covariance convergence gives strong convergence of the actual coherent tree stages. -/
theorem treeIterate_cauchy (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t L : ℝ)
    (hbound : ∀ n, ‖treeIterate m a r hr n t‖ ^ 2 ≤ L)
    (hlim : Tendsto (fun n => ‖treeIterate m a r hr n t‖ ^ 2) atTop (nhds L)) :
    CauchySeq (fun n => treeIterate m a r hr n t) := by
  apply cauchySeq_of_le_tendsto_0' (fun n => Real.sqrt (L - ‖treeIterate m a r hr n t‖ ^ 2))
  · intro n k hnk
    apply (Real.le_sqrt (dist_nonneg) (sub_nonneg.mpr (hbound n))).mpr
    rw [treeIterate_dist_sq m a r hr hnk t]
    linarith [hbound k]
  · have hc : Tendsto (fun _ : ℕ => L) atTop (nhds L) := tendsto_const_nhds
    simpa only [sub_self, Real.sqrt_zero] using (hc.sub hlim).sqrt

theorem treeIterate_exists_limit (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t L : ℝ)
    (hbound : ∀ n, ‖treeIterate m a r hr n t‖ ^ 2 ≤ L)
    (hlim : Tendsto (fun n => ‖treeIterate m a r hr n t‖ ^ 2) atTop (nhds L)) :
    ∃ v : CausalTree.Space m, Tendsto (fun n => treeIterate m a r hr n t) atTop (nhds v) :=
  cauchySeq_tendsto_of_complete (treeIterate_cauchy m a r hr t L hbound hlim)

/-- The concrete Hilbert limit, uniquely determined whenever the covariance stages converge. -/
@[expose] def treeLimit (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) : CausalTree.Space m :=
  limUnder atTop (fun n => treeIterate m a r hr n t)

theorem treeIterate_tendsto (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t L : ℝ)
    (hbound : ∀ n, ‖treeIterate m a r hr n t‖ ^ 2 ≤ L)
    (hlim : Tendsto (fun n => ‖treeIterate m a r hr n t‖ ^ 2) atTop (nhds L)) :
    Tendsto (fun n => treeIterate m a r hr n t) atTop (nhds (treeLimit m a r hr t)) :=
  (treeIterate_cauchy m a r hr t L hbound hlim).tendsto_limUnder

theorem treeLimit_heightPrefix (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ)
    (hl : Tendsto (fun n => treeIterate m a r hr n t) atTop (nhds (treeLimit m a r hr t))) (j : ℕ) :
    heightPrefix j (treeLimit m a r hr t) = treeIterate m a r hr j t := by
  have hp := ((heightPrefixL m j).continuous.tendsto (treeLimit m a r hr t)).comp hl
  have he : (fun n => heightPrefix j (treeIterate m a r hr n t)) =ᶠ[atTop]
      fun _ => treeIterate m a r hr j t :=
    eventually_atTop.mpr ⟨j, fun n hn => treeIterate_consistent m a r hr hn t⟩
  have hc : Tendsto (fun n => heightPrefix j (treeIterate m a r hr n t)) atTop
      (nhds (treeIterate m a r hr j t)) := tendsto_const_nhds.congr' he.symm
  exact tendsto_nhds_unique hp hc

theorem treeLimit_norm_sq (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t L : ℝ)
    (hl : Tendsto (fun n => treeIterate m a r hr n t) atTop (nhds (treeLimit m a r hr t)))
    (hn : Tendsto (fun n => ‖treeIterate m a r hr n t‖ ^ 2) atTop (nhds L)) :
    ‖treeLimit m a r hr t‖ ^ 2 = L :=
  tendsto_nhds_unique (hl.norm.pow 2) hn

theorem noiseFeature_prefix (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    {T t : ℝ} (ht : 0 ≤ t) (hT : t ≤ T) : noisePrefix T (noiseFeature r hr t) = noiseFeature r hr t := by
  apply Lp.ext
  filter_upwards [noisePrefix_coe T (noiseFeature r hr t), noiseFeature_coe r hr t] with u hp hf
  rw [hp]
  by_cases hTu : u ≤ T
  · rw [indicator_of_mem (show u ∈ Iic T from hTu)]
  · rw [indicator_of_notMem (show u ∉ Iic T from hTu), hf]
    have hu : u ∉ Ioc 0 t := fun h => hTu (h.2.trans hT)
    rw [WhiteCovarianceKernel.rowCut, indicator_of_notMem hu]

theorem leafResponseFeature_prefix (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    {T t : ℝ} (ht : 0 ≤ t) (hT : t ≤ T) :
    leafPrefix T (leafResponseFeature r hr t) = leafResponseFeature r hr t := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact leafPrefix_fst T _
  · change (leafPrefix T (leafResponseFeature r hr t)).snd = (leafResponseFeature r hr t).snd
    rw [leafPrefix_snd]
    change noisePrefix T (Real.sqrt 2 • noiseFeature r hr (max 0 t)) =
      Real.sqrt 2 • noiseFeature r hr (max 0 t)
    rw [max_eq_right ht, noisePrefix_smul, noiseFeature_prefix r hr ht hT]

theorem baseVector_timePrefix (m : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) {T t : ℝ} (ht : 0 ≤ t) (hT : t ≤ T) :
    timePrefix T (baseVector m r hr t) = baseVector m r hr t := by
  ext τ
  by_cases hτ : τ = CausalTree.Tree.leaf
  · subst τ
    simp only [timePrefix_apply, fiberPrefix_leaf, baseVector, lp.single_apply_self]
    exact leafResponseFeature_prefix r hr ht hT
  · have hz : baseVector m r hr t τ = 0 := lp.single_apply_ne _ _ _ hτ
    rw [timePrefix_apply, hz, map_zero]

theorem timePrefix_intervalIntegral {m : ℕ} (T : ℝ) {f : ℝ → CausalTree.Space m}
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    timePrefix T (∫ u in a..b, f u) = ∫ u in a..b, timePrefix T (f u) :=
  ((timePrefixL m T).intervalIntegral_comp_comm hf).symm

/-- Every finite tree stage uses only Brownian noise from times at most its own time. -/
theorem treeIterate_timePrefix (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (n : ℕ) {T t : ℝ} (ht : 0 ≤ t) (hT : t ≤ T) :
    timePrefix T (treeIterate m a r hr n t) = treeIterate m a r hr n t := by
  induction n generalizing t with
  | zero => exact baseVector_timePrefix m r hr ht hT
  | succ n ih =>
    rw [treeIterate, timePrefix_add, timePrefix_smul,
      timePrefix_intervalIntegral T (treeIterate_integrable m a r hr n (max 0 t) 0 (max 0 t)),
      baseVector_timePrefix m r hr ht hT, max_eq_right ht]
    congr 2
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [timePrefix_smul, timePrefix_graftPower, ih hu.1 (hu.2.trans hT)]

theorem treeLimit_timePrefix (m : ℕ) (a : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) {T t : ℝ} (ht : 0 ≤ t) (hT : t ≤ T)
    (hl : Tendsto (fun n => treeIterate m a r hr n t) atTop (nhds (treeLimit m a r hr t))) :
    timePrefix T (treeLimit m a r hr t) = treeLimit m a r hr t := by
  have hp := ((timePrefixL m T).continuous.tendsto (treeLimit m a r hr t)).comp hl
  change Tendsto (fun n => timePrefix T (treeIterate m a r hr n t)) atTop
    (nhds (timePrefix T (treeLimit m a r hr t))) at hp
  have he : (fun n => timePrefix T (treeIterate m a r hr n t)) =
      (fun n => treeIterate m a r hr n t) := by
    funext n
    exact treeIterate_timePrefix m a r hr n ht hT
  rw [he] at hp
  exact tendsto_nhds_unique hp hl

/-- The actual causal tree state attached to a supplied CK solution. -/
@[expose] def ckTreeState {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t : ℝ) :
    CausalTree.Space (p - 1) :=
  treeLimit (p - 1) (β * Real.sqrt p) (clampedResponse d) (clampedResponse_continuous h) t

theorem ckTreeIterate_norm_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖ckTreeIterate p β d (clampedResponse_continuous h) n t‖ ≤ 1 := by
  have hn := (GlobalCKExtension.global_covarianceIterate_bounds h hb n ht ht).2
  rw [h.correlation_diagonal t ht, ← ckTreeIterate_norm_sq p β d (clampedResponse_continuous h) n ht] at hn
  nlinarith [norm_nonneg (ckTreeIterate p β d (clampedResponse_continuous h) n t)]

/-- The actual tree-valued Picard iteration converges strongly at every positive time. -/
theorem ckTreeIterate_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ckTreeIterate p β d (clampedResponse_continuous h) n t) atTop
      (nhds (ckTreeState h t)) := by
  apply treeIterate_tendsto (p - 1) (β * Real.sqrt p) (clampedResponse d)
    (clampedResponse_continuous h) t 1
  · intro n
    have hn := ckTreeIterate_norm_le_one h hb n ht
    change ‖ckTreeIterate p β d (clampedResponse_continuous h) n t‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg (ckTreeIterate p β d (clampedResponse_continuous h) n t)]
  · change Tendsto (fun n => ‖ckTreeIterate p β d (clampedResponse_continuous h) n t‖ ^ 2)
      atTop (nhds (1 : ℝ))
    simp_rw [ckTreeIterate_norm_sq p β d (clampedResponse_continuous h) _ ht]
    simpa only [h.correlation_diagonal t ht] using
      GlobalCKExtension.global_covarianceIterate_tendsto h hb ht ht

/-- The genuine tree path has exactly the original CK correlation as its Gram kernel. -/
theorem ckTreeState_gram {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (ckTreeState h t) (ckTreeState h s) = d.C t s := by
  have hi : Tendsto (fun n => inner ℝ (ckTreeIterate p β d (clampedResponse_continuous h) n t)
      (ckTreeIterate p β d (clampedResponse_continuous h) n s)) atTop
        (nhds (inner ℝ (ckTreeState h t) (ckTreeState h s))) :=
    (ckTreeIterate_tendsto h hb ht).inner (ckTreeIterate_tendsto h hb hs)
  simp_rw [ckTreeIterate_gram p β d (clampedResponse_continuous h) _ ht hs] at hi
  exact tendsto_nhds_unique hi (GlobalCKExtension.global_covarianceIterate_tendsto h hb ht hs)

theorem ckTreeState_norm {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) : ‖ckTreeState h t‖ = 1 := by
  have hn := ckTreeState_gram h hb ht ht
  rw [h.correlation_diagonal t ht, real_inner_self_eq_norm_sq] at hn
  nlinarith [norm_nonneg (ckTreeState h t)]

/-- Norm continuity of the true positive-time tree path. -/
theorem ckTreeState_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) :
    Continuous (fun t : ℝ≥0 => ckTreeState h (t : ℝ)) := by
  apply continuous_of_gram
  simp_rw [ckTreeState_gram h hb (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  exact h.correlation_continuous.comp_continuous
    ((NNReal.continuous_coe.comp continuous_fst).prodMk
      (NNReal.continuous_coe.comp continuous_snd))
    (fun z => ⟨NNReal.coe_nonneg z.1, NNReal.coe_nonneg z.2⟩)

/-- The strong limit remains exactly in its own Brownian noise prefix. -/
theorem ckTreeState_timePrefix {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t : ℝ} (ht : 0 ≤ t) (hT : t ≤ T) :
    timePrefix T (ckTreeState h t) = ckTreeState h t :=
  treeLimit_timePrefix (p - 1) (β * Real.sqrt p) (clampedResponse d)
    (clampedResponse_continuous h) ht hT (ckTreeIterate_tendsto h hb ht)

theorem ckTreeState_heightPrefix {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    heightPrefix j (ckTreeState h t) = ckTreeIterate p β d (clampedResponse_continuous h) j t :=
  treeLimit_heightPrefix (p - 1) (β * Real.sqrt p) (clampedResponse d)
    (clampedResponse_continuous h) t (ckTreeIterate_tendsto h hb ht) j


/-- A continuous full-line extension used only for Bochner integrability. -/
theorem ckTreeState_clamped_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) :
    Continuous (fun u : ℝ => ckTreeState h (max 0 u)) := by
  exact (ckTreeState_continuous h hb).comp
    ((continuous_const.max continuous_id).subtype_mk (fun u => le_max_left 0 u))

theorem ckTreeState_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => clampedResponse d t u • graftPower (ckTreeState h u)) volume 0 t := by
  have hc : Continuous (fun u : ℝ => clampedResponse d t u • graftPower (ckTreeState h (max 0 u))) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      ((graftPower_continuous (p - 1)).comp (ckTreeState_clamped_continuous h hb))
  apply (hc.intervalIntegrable 0 t).congr
  intro u hu
  rw [uIoc_of_le ht] at hu
  dsimp only
  rw [max_eq_right hu.1.le]

theorem graftPower_norm_le_one {m : ℕ} {v : CausalTree.Space m} (hv : ‖v‖ ≤ 1) :
    ‖graftPower v‖ ≤ 1 := by
  have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hp : (‖v‖ ^ 2) ^ m ≤ 1 := pow_le_one₀ (sq_nonneg ‖v‖) hv2
  rw [← norm_graftPower_sq] at hp
  nlinarith [norm_nonneg (graftPower v)]

/-- Dominated Bochner convergence closes the actual tree-valued memory integral. -/
theorem ckTreeIterate_memory_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ u in (0 : ℝ)..t, clampedResponse d t u •
      graftPower (ckTreeIterate p β d (clampedResponse_continuous h) n u)) atTop
      (nhds (∫ u in (0 : ℝ)..t, clampedResponse d t u • graftPower (ckTreeState h u))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => |clampedResponse d t u|)
  · apply Filter.Eventually.of_forall
    intro n
    exact (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      ((graftPower_continuous (p - 1)).comp
        (treeIterate_continuous (p - 1) (β * Real.sqrt p) (clampedResponse d)
          (clampedResponse_continuous h) n))).aestronglyMeasurable.restrict
  · apply Filter.Eventually.of_forall
    intro n
    apply Filter.Eventually.of_forall
    intro u hu
    rw [uIoc_of_le ht] at hu
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (graftPower_norm_le_one (ckTreeIterate_norm_le_one h hb n hu.1.le))
  · exact ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).abs.intervalIntegrable 0 t
  · apply Filter.Eventually.of_forall
    intro u hu
    rw [uIoc_of_le ht] at hu
    exact tendsto_const_nhds.smul
      (((graftPower_continuous (p - 1)).tendsto (ckTreeState h u)).comp
        (ckTreeIterate_tendsto h hb hu.1.le))

/-- The genuine strong limit solves the Hilbert-valued Volterra equation. -/
theorem ckTreeState_volterra_clamped {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    ckTreeState h t = baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t +
      (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t, clampedResponse d t u • graftPower (ckTreeState h u) := by
  have hrhs : Tendsto (fun n =>
      baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t +
        (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t, clampedResponse d t u •
          graftPower (ckTreeIterate p β d (clampedResponse_continuous h) n u)) atTop
      (nhds (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t +
        (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t, clampedResponse d t u • graftPower (ckTreeState h u))) :=
    tendsto_const_nhds.add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => β * Real.sqrt p) atTop (nhds (β * Real.sqrt p))).smul
        (ckTreeIterate_memory_tendsto h hb ht))
  have hsucc := (ckTreeIterate_tendsto h hb ht).comp (tendsto_add_atTop_nat 1)
  have he : (fun n => ckTreeIterate p β d (clampedResponse_continuous h) (n + 1) t) =
      (fun n => baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t +
        (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t, clampedResponse d t u •
          graftPower (ckTreeIterate p β d (clampedResponse_continuous h) n u)) := by
    funext n
    simp only [ckTreeIterate, treeIterate, max_eq_right ht]
  change Tendsto (fun n => ckTreeIterate p β d (clampedResponse_continuous h) (n + 1) t)
    atTop (nhds (ckTreeState h t)) at hsucc
  rw [he] at hsucc
  exact tendsto_nhds_unique hsucc hrhs

/-- Exact manuscript realization, using the original response on its causal domain. -/
theorem ckTreeState_volterra {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    ckTreeState h t = baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t +
      (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t, d.R t u • graftTensor (p - 1)
        (standardTensorPower (ckTreeState h u)) := by
  rw [ckTreeState_volterra_clamped h hb ht]
  congr 2
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [clampedResponse_eq hu.1 hu.2, graftTensor_power]


/-- Actual source tree energy. -/
@[expose] def treeEnergy (p : ℕ) (v : CausalTree.Space (p - 1)) : ℝ :=
  Real.sqrt p * inner ℝ v (graftPower v)

theorem ckTreeState_energy {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    treeEnergy p (ckTreeState h t) = energy p β d t := by
  have hz : inner ℝ (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t)
      (graftPower (ckTreeState h t)) = 0 :=
    baseVector_inner_graft (p - 1) (clampedResponse d) (clampedResponse_continuous h) t
      (tensorPower (ckTreeState h t))
  have hi := congrArg (fun v => inner ℝ v (graftPower (ckTreeState h t)))
    (ckTreeState_volterra_clamped h hb ht)
  rw [inner_add_left, hz, zero_add, real_inner_smul_left,
    intervalIntegral_inner _ (ckTreeState_integrable h hb ht)] at hi
  have he : (∫ u in (0 : ℝ)..t, inner ℝ
      (clampedResponse d t u • graftPower (ckTreeState h u)) (graftPower (ckTreeState h t))) =
      memoryMass p d t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [real_inner_smul_left, graftPower_inner, ckTreeState_gram h hb hu.1 ht,
      clampedResponse_eq hu.1 hu.2, h.correlation_symmetric u t hu.1 ht]
    exact mul_comm _ _
  rw [he] at hi
  unfold treeEnergy energy
  rw [hi]
  have hp := Real.sq_sqrt (Nat.cast_nonneg p)
  calc
    _ = β * (Real.sqrt p) ^ 2 * memoryMass p d t := by ring
    _ = _ := by rw [hp]

theorem ckTreeState_multiplier {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    d.multiplier t = 1 + (p : ℝ) * β * treeEnergy p (ckTreeState h t) := by
  rw [ckTreeState_energy h hb ht]
  exact multiplier_energy_identity h t ht

/-- The actual tensor adjoint vanishes on the one-leaf response vector. -/
theorem graftTensorAdjoint_baseVector (m : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    graftTensorAdjoint m (baseVector m r hr t) = 0 := by
  change (tensorDomainEquiv m).symm (ungraft (baseVector m r hr t)) = 0
  have hz : ungraft (baseVector m r hr t) = 0 := by
    ext ts
    rw [ungraft_apply]
    change lp.single (E := fun τ : CausalTree.Tree m => (fiber τ).Carrier) 2 CausalTree.Tree.leaf
      (leafResponseFeature r hr t) (CausalTree.Tree.graft ts) = 0
    exact lp.single_apply_ne _ _ _ (by simp)
  rw [hz, map_zero]

/-- Exact prefix root frame in the full completed tensor domain. -/
theorem ckTreeState_prefix_root_frame {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) (T : ℝ) :
    graftTensorAdjoint (p - 1) (timePrefix T (ckTreeState h t)) =
      (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t,
        clampedResponse d t u • standardTensorPower (timePrefix T (ckTreeState h u)) := by
  have hpt : IntervalIntegrable
      (fun u => timePrefix T (clampedResponse d t u • graftPower (ckTreeState h u))) volume 0 t := by
    have hc : Continuous (fun u : ℝ => timePrefix T
        (clampedResponse d t u • graftPower (ckTreeState h (max 0 u)))) :=
      (timePrefixL (p - 1) T).continuous.comp
        (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
          ((graftPower_continuous (p - 1)).comp (ckTreeState_clamped_continuous h hb)))
    apply (hc.intervalIntegrable 0 t).congr
    intro u hu
    rw [uIoc_of_le ht] at hu
    dsimp only
    rw [max_eq_right hu.1.le]
  have hv := congrArg (fun v => graftTensorAdjoint (p - 1) (timePrefix T v))
    (ckTreeState_volterra_clamped h hb ht)
  rw [timePrefix_add, timePrefix_smul,
    timePrefix_intervalIntegral T (ckTreeState_integrable h hb ht), map_add, map_smul,
    ← (graftTensorAdjoint (p - 1)).intervalIntegral_comp_comm hpt] at hv
  have hz : graftTensorAdjoint (p - 1)
      (timePrefix T (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t)) = 0 := by
    change (tensorDomainEquiv (p - 1)).symm
      (ungraft (timePrefix T (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t))) = 0
    have hz' : ungraft (timePrefix T
        (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t)) = 0 := by
      ext ts
      rw [ungraft_apply, timePrefix_apply]
      have hb' : baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t
          (CausalTree.Tree.graft ts) = 0 := lp.single_apply_ne _ _ _ (by simp)
      rw [hb', map_zero]
      rfl
    rw [hz', map_zero]
  rw [hz, zero_add] at hv
  rw [hv]
  congr 2
  funext u
  rw [timePrefix_smul, timePrefix_graftPower, map_smul, ← graftTensor_power,
    graftTensorAdjoint_graftTensor]


/-- Original-response form of the prefix root frame from Proposition 7.1. -/
theorem ckTreeState_prefix_root_frame_original {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) (T : ℝ) :
    graftTensorAdjoint (p - 1) (timePrefix T (ckTreeState h t)) =
      (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t,
        d.R t u • standardTensorPower (timePrefix T (ckTreeState h u)) := by
  rw [ckTreeState_prefix_root_frame h hb ht T]
  apply congrArg (fun z => (β * Real.sqrt p) • z)
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [clampedResponse_eq hu.1 hu.2]

theorem noiseFeature_zero (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) :
    noiseFeature r hr 0 = 0 := by
  apply Lp.ext
  filter_upwards [noiseFeature_coe r hr 0, Lp.coeFn_zero ℝ 2 (volume.restrict (Ioi (0 : ℝ)))] with u hu hz
  rw [hu, hz]
  simp [WhiteCovarianceKernel.rowCut]

/-- The true realized path starts at the distinguished one-leaf initial vector. -/
theorem ckTreeState_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) : ckTreeState h 0 = initialVector (p - 1) := by
  rw [ckTreeState_volterra_clamped h hb (le_refl 0), intervalIntegral.integral_same, smul_zero, add_zero]
  unfold baseVector initialVector
  congr 1
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change clampedResponse d (max 0 0) 0 = 1
    rw [max_self, clampedResponse_eq (le_refl 0) (le_refl 0), h.response_diagonal 0 (le_refl 0)]
  · change Real.sqrt 2 • noiseFeature (clampedResponse d) (clampedResponse_continuous h) (max 0 0) = 0
    rw [max_self, noiseFeature_zero, smul_zero]

end SphericalAging.CausalTreeRealization
