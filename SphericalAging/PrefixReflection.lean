module

public import SphericalAging.ProjectedTreeDrift

public section

/-! Exact finite-time prefix Gram and energy identities on the actual causal tree. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory Filter
namespace SphericalAging.PrefixReflection
open CausalTree CausalTreeRealization ProjectedTreeDrift CKSpecification GreenCovariance WeightedHilbertKernel
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The actual prefix center at an absolute time. -/
@[expose] def prefixVector {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T t : ℝ) : CausalTree.Space (p-1) := timePrefix T (ckTreeState h t)

/-- The actual Gram kernel of the prefix centers. -/
@[expose] def prefixKernel {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T t s : ℝ) : ℝ := inner ℝ (prefixVector h T t) (prefixVector h T s)

/-- The actual future-offset prefix Gram kernel. -/
@[expose] def futureKernel {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T a b : ℝ) : ℝ := prefixKernel h T (T+a) (T+b)

theorem prefixKernel_symmetric {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T t s : ℝ) : prefixKernel h T t s = prefixKernel h T s t :=
  real_inner_comm _ _

theorem prefixVector_clamped_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) :
    Continuous (fun t => prefixVector h T (max 0 t)) :=
  (timePrefixL (p-1) T).continuous.comp (ckTreeState_clamped_continuous h hb)

theorem prefixKernel_clamped_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) :
    Continuous (fun z : ℝ × ℝ => prefixKernel h T (max 0 z.1) (max 0 z.2)) :=
  ((prefixVector_clamped_continuous h hb T).comp continuous_fst).inner
    ((prefixVector_clamped_continuous h hb T).comp continuous_snd)

theorem prefixVector_norm_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖prefixVector h T t‖ ≤ 1 :=
  (timePrefix_norm_le T _).trans_eq (ckTreeState_norm h hb ht)

theorem prefixKernel_abs_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) : |prefixKernel h T t s| ≤ 1 := by
  calc
    _ ≤ ‖prefixVector h T t‖*‖prefixVector h T s‖ := abs_real_inner_le_norm _ _
    _ ≤ 1*1 := mul_le_mul (prefixVector_norm_le_one h hb T ht)
      (prefixVector_norm_le_one h hb T hs) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- No prefix information is lost when either argument lies in the past. -/
theorem prefixKernel_eq_correlation_of_past_left {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) (htT : t ≤ T) : prefixKernel h T t s = d.C t s := by
  unfold prefixKernel prefixVector
  rw [timePrefix_selfAdjoint, timePrefix_idempotent,
    ← timePrefix_selfAdjoint, ckTreeState_timePrefix h hb ht htT,
    ckTreeState_gram h hb ht hs]

theorem prefixKernel_eq_correlation_of_past_right {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hsT : s ≤ T) : prefixKernel h T t s = d.C t s := by
  rw [prefixKernel_symmetric, prefixKernel_eq_correlation_of_past_left h hb hs ht hsT,
    h.correlation_symmetric s t hs ht]

/-- The projected leaf Gram kernel stops exactly at T. -/
theorem projectedBase_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t s : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) (hs : T ≤ s) :
    inner ℝ (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s)) =
      d.R t 0*d.R s 0 + 2*(∫ u in (0 : ℝ)..T, d.R t u*d.R s u) := by
  rw [timePrefix_baseVector, timePrefix_baseVector, lp.inner_single_left, lp.single_apply_self,
    leafPrefix_leafResponseFeature hT ht, leafPrefix_leafResponseFeature hT hs]
  simp only [stoppedLeaf, WithLp.prod_inner_apply, real_inner_smul_left, real_inner_smul_right,
    fixedNoiseRow_inner hT, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    clampedResponse_eq le_rfl (hT.trans ht), clampedResponse_eq le_rfl (hT.trans hs)]
  have hi : (∫ u in (0 : ℝ)..T, clampedResponse d t u*clampedResponse d s u) =
      ∫ u in (0 : ℝ)..T, d.R t u*d.R s u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT] at hu
    dsimp only
    rw [clampedResponse_eq hu.1 (hu.2.trans ht), clampedResponse_eq hu.1 (hu.2.trans hs)]
  rw [hi]
  ring

/-- The projected leaf component is orthogonal to every actual graft. -/
theorem projectedBase_inner_graft {m : ℕ} (T : ℝ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) (w : RootTensorSpace m) :
    inner ℝ (timePrefix T (baseVector m r hr t)) (graft w) = 0 := by
  rw [timePrefix_baseVector, lp.inner_single_left]
  change inner ℝ _ (graft w CausalTree.Tree.leaf) = 0
  rw [graft_leaf, inner_zero_right]

/-- The actual projected response convolution. -/
@[expose] def projectedMemory {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T t : ℝ) : CausalTree.Space (p-1) :=
  ∫ u in (0 : ℝ)..t, clampedResponse d t u • graftPower (prefixVector h T (max 0 u))

theorem projectedMemory_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T t a b : ℝ) :
    IntervalIntegrable (fun u => clampedResponse d t u • graftPower (prefixVector h T (max 0 u))) volume a b :=
  (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
    ((graftPower_continuous (p-1)).comp (prefixVector_clamped_continuous h hb T))).intervalIntegrable a b

theorem prefixVector_volterra {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    prefixVector h T t = timePrefix T
        (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t) +
      (β * Real.sqrt p) • projectedMemory h T t := by
  unfold prefixVector
  rw [treeMemory_volterra h hb ht, timePrefix_add, timePrefix_smul, treeMemory,
    timePrefix_intervalIntegral T (by
      exact (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
        ((graftPower_continuous (p-1)).comp (ckTreeState_clamped_continuous h hb))).intervalIntegrable (μ := volume) 0 t)]
  simp_rw [timePrefix_smul, timePrefix_graftPower]
  rfl

/-- The actual projected memory has its exact double-convolution Gram kernel. -/
theorem projectedMemory_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T t s : ℝ) :
    inner ℝ (projectedMemory h T t) (projectedMemory h T s) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, clampedResponse d t u*clampedResponse d s v*
        prefixKernel h T (max 0 u) (max 0 v)^(p-1) := by
  rw [projectedMemory, intervalIntegral_inner _ (projectedMemory_integrable h hb T t 0 t)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [projectedMemory, inner_intervalIntegral _ (projectedMemory_integrable h hb T s 0 s)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [real_inner_smul_left, real_inner_smul_right, graftPower_inner]
  unfold prefixKernel
  ring

/-- The actual projected base and memory are orthogonal. -/
theorem projectedBase_inner_memory {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T t s : ℝ) :
    inner ℝ (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (projectedMemory h T s) = 0 := by
  rw [projectedMemory, inner_intervalIntegral _ (projectedMemory_integrable h hb T s 0 s)]
  have he (u : ℝ) : inner ℝ
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t))
      (clampedResponse d s u • graftPower (prefixVector h T (max 0 u))) = 0 := by
    rw [real_inner_smul_right]
    exact mul_eq_zero_of_right _ (projectedBase_inner_graft T _ _ t _)
  simp_rw [he]
  simp

/-- The exact finite-time projected Green equation, before any stationary limit. -/
theorem projected_green_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (hT : 0 ≤ T) (ht : T ≤ t) (hs : T ≤ s) :
    prefixKernel h T t s = d.R t 0*d.R s 0 + 2*(∫ u in (0 : ℝ)..T, d.R t u*d.R s u) +
      β^2*(p : ℝ)*(∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        d.R t u*d.R s v*prefixKernel h T u v^(p-1)) := by
  unfold prefixKernel
  rw [prefixVector_volterra h hb T (hT.trans ht), prefixVector_volterra h hb T (hT.trans hs)]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    projectedBase_inner_memory h hb T t s]
  have he : inner ℝ (projectedMemory h T t)
      (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) s)) = 0 :=
    (real_inner_comm _ _).trans (projectedBase_inner_memory h hb T s t)
  rw [he, projectedBase_inner h hT ht hs, projectedMemory_inner h hb T t s]
  have hi : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
      clampedResponse d t u*clampedResponse d s v*prefixKernel h T (max 0 u) (max 0 v)^(p-1)) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*prefixKernel h T u v^(p-1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (hT.trans ht)] at hu
    dsimp only
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (hT.trans hs)] at hv
    dsimp only
    rw [max_eq_right hu.1, max_eq_right hv.1,
      clampedResponse_eq hu.1 hu.2, clampedResponse_eq hv.1 hv.2]
  rw [hi]
  have hp := Real.sq_sqrt (Nat.cast_nonneg p)
  unfold prefixKernel
  ring_nf
  rw [hp]
  ring


/-- Exact tensor-root formula for the energy of an actual prefix center. -/
theorem prefix_energy_formula {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    treeEnergy p (prefixVector h T t) = β*(p : ℝ)*
      (∫ u in (0 : ℝ)..t, d.R t u*prefixKernel h T t u^(p-1)) := by
  have hc : Continuous (fun u => clampedResponse d t u • standardTensorPower (prefixVector h T (max 0 u))) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      ((ScalarHilbertKernel.finitePure_continuous (p-1) (fun _ => spaceDatum (p-1)) (fun _ => id)
        (fun _ => continuous_id)).comp (prefixVector_clamped_continuous h hb T))
  have hi : IntervalIntegrable (fun u => clampedResponse d t u •
      standardTensorPower (prefixVector h T u)) volume 0 t := by
    apply (hc.intervalIntegrable (μ := volume) 0 t).congr
    intro u hu
    rw [uIoc_of_le ht] at hu
    dsimp only
    rw [max_eq_right hu.1.le]
  have hf : inner ℝ (prefixVector h T t) (graftPower (prefixVector h T t)) =
      inner ℝ (graftTensorAdjoint (p-1) (prefixVector h T t))
        (standardTensorPower (prefixVector h T t)) := by
    rw [← graftTensor_power]
    exact (real_inner_comm _ _).trans
      ((graftTensor_adjoint_identity _ _).trans (real_inner_comm _ _))
  unfold treeEnergy
  rw [hf]
  change Real.sqrt p * inner ℝ (graftTensorAdjoint (p-1) (timePrefix T (ckTreeState h t)))
    (standardTensorPower (prefixVector h T t)) = _
  rw [ckTreeState_prefix_root_frame h hb ht T, real_inner_smul_left]
  change Real.sqrt p * ((β * Real.sqrt p) * inner ℝ
    (∫ u in (0 : ℝ)..t, clampedResponse d t u • standardTensorPower (prefixVector h T u))
    (standardTensorPower (prefixVector h T t))) = _
  rw [intervalIntegral_inner _ hi]
  have he : (∫ u in (0 : ℝ)..t, inner ℝ
      (clampedResponse d t u • standardTensorPower (prefixVector h T u))
      (standardTensorPower (prefixVector h T t))) =
      ∫ u in (0 : ℝ)..t, d.R t u*prefixKernel h T t u^(p-1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [real_inner_smul_left, standardTensorPower, standardTensorPower, HilbertDatum.inner_finitePure]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [clampedResponse_eq hu.1 hu.2]
    unfold prefixKernel
    rw [real_inner_comm (prefixVector h T t) (prefixVector h T u)]
  rw [he]
  ring_nf
  rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  ring

/-- Genuine continuous rectangle integrals cancel whenever either coordinate lies in the past. -/
theorem rectangle_past_cancellation {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    {T t s : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) (hs : T ≤ s)
    (hleft : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 s, F u v = 0)
    (hright : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 T, F u v = 0) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v) =
      ∫ u in T..t, ∫ v in T..s, F u v := by
  have hrow (u : ℝ) : Continuous (F u) := hF.comp (continuous_const.prodMk continuous_id)
  have hinner (u : ℝ) (hu : u ∈ Icc 0 t) :
      (∫ v in (0 : ℝ)..s, F u v) = ∫ v in T..s, F u v := by
    have hz : (∫ v in (0 : ℝ)..T, F u v) = 0 := by
      apply intervalIntegral.integral_zero_ae
      apply Filter.Eventually.of_forall
      intro v hv
      rw [uIoc_of_le hT] at hv
      exact hright u hu v (Ioc_subset_Icc_self hv)
    have ha := intervalIntegral.integral_add_adjacent_intervals
      ((hrow u).intervalIntegrable (μ := volume) 0 T) ((hrow u).intervalIntegrable (μ := volume) T s)
    rw [hz, zero_add] at ha
    exact ha.symm
  have houter : Continuous (fun u => ∫ v in T..s, F u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF T s
  have hz : (∫ u in (0 : ℝ)..T, ∫ v in T..s, F u v) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro u hu
    rw [uIoc_of_le hT] at hu
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro v hv
    rw [uIoc_of_le hs] at hv
    exact hleft u (Ioc_subset_Icc_self hu) v ⟨hT.trans hv.1.le, hv.2⟩
  calc
    _ = ∫ u in (0 : ℝ)..t, ∫ v in T..s, F u v := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (hT.trans ht)] at hu
      exact hinner u hu
    _ = _ := by
      have ha := intervalIntegral.integral_add_adjacent_intervals
        (houter.intervalIntegrable (μ := volume) 0 T) (houter.intervalIntegrable (μ := volume) T t)
      rw [hz, zero_add] at ha
      exact ha.symm


/-- Exact cancellation of the entire past in the prefix energy, at a finite time. -/
theorem prefix_energy_subtraction {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) :
    treeEnergy p (prefixVector h T t) = energy p β d t + β*(p : ℝ)*
      (∫ u in T..t, d.R t u*(prefixKernel h T t u^(p-1)-d.C t u^(p-1))) := by
  have htc := hT.trans ht
  let F : ℝ → ℝ := fun u => clampedResponse d t u*prefixKernel h T t (max 0 u)^(p-1)
  let G : ℝ → ℝ := fun u => clampedResponse d t u*clampedCorrelation d t u^(p-1)
  have hR : Continuous (fun u => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hK : Continuous (fun u => prefixKernel h T t (max 0 u)) :=
    continuous_const.inner (prefixVector_clamped_continuous h hb T)
  have hF : Continuous F := hR.mul (hK.pow (p-1))
  have hG : Continuous G := hR.mul
    (((clampedCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)).pow (p-1))
  have hf : (∫ u in (0 : ℝ)..t, F u) =
      ∫ u in (0 : ℝ)..t, d.R t u*prefixKernel h T t u^(p-1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le htc] at hu
    dsimp only [F]
    rw [clampedResponse_eq hu.1 hu.2, max_eq_right hu.1]
  have hg : (∫ u in (0 : ℝ)..t, G u) = memoryMass p d t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le htc] at hu
    dsimp only [G, memoryMass]
    rw [clampedResponse_eq hu.1 hu.2, clampedCorrelation_eq htc hu.1]
    ring
  have hz : (∫ u in (0 : ℝ)..T, F u-G u) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro u hu
    rw [uIoc_of_le hT] at hu
    dsimp only [F, G]
    rw [max_eq_right hu.1.le, prefixKernel_eq_correlation_of_past_right h hb htc hu.1.le hu.2,
      clampedCorrelation_eq htc hu.1.le, sub_self]
  have hs := intervalIntegral.integral_add_adjacent_intervals
    ((hF.sub hG).intervalIntegrable (μ := volume) 0 T)
    ((hF.sub hG).intervalIntegrable (μ := volume) T t)
  change (∫ u in (0 : ℝ)..T, F u-G u) + (∫ u in T..t, F u-G u) =
    ∫ u in (0 : ℝ)..t, F u-G u at hs
  rw [hz, zero_add, intervalIntegral.integral_sub
    (hF.intervalIntegrable (μ := volume) 0 t) (hG.intervalIntegrable (μ := volume) 0 t), hf, hg] at hs
  have hfuture : (∫ u in T..t, F u-G u) =
      ∫ u in T..t, d.R t u*(prefixKernel h T t u^(p-1)-d.C t u^(p-1)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only [F, G]
    rw [max_eq_right (hT.trans hu.1), clampedResponse_eq (hT.trans hu.1) hu.2,
      clampedCorrelation_eq htc (hT.trans hu.1)]
    ring
  rw [hfuture] at hs
  rw [prefix_energy_formula h hb T htc]
  unfold energy
  rw [hs]
  ring

/-- The source's exact fixed-length future energy subtraction, before taking a cluster limit. -/
theorem exact_prefix_energy_subtraction {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) :
    treeEnergy p (prefixVector h T (T+L)) = energy p β d (T+L) + β*(p : ℝ)*
      (∫ u in T..T+L, d.R (T+L) u*(futureKernel h T (u-T) L^(p-1)-d.C (T+L) u^(p-1))) := by
  rw [prefix_energy_subtraction h hb hT (by linarith)]
  congr 2
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [futureKernel]
  rw [show T+(u-T)=u from by ring, prefixKernel_symmetric h T (T+L) u]


/-- A double scalar interval integral commutes with subtraction of actual continuous kernels. -/
theorem double_integral_sub {F G : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G)) (a b c d : ℝ) :
    (∫ u in a..b, ∫ v in c..d, F u v-G u v) =
      (∫ u in a..b, ∫ v in c..d, F u v)-(∫ u in a..b, ∫ v in c..d, G u v) := by
  have hFo : Continuous (fun u => ∫ v in c..d, F u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF c d
  have hGo : Continuous (fun u => ∫ v in c..d, G u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG c d
  rw [← intervalIntegral.integral_sub (hFo.intervalIntegrable (μ := volume) a b)
    (hGo.intervalIntegrable (μ := volume) a b)]
  apply intervalIntegral.integral_congr
  intro u _
  exact intervalIntegral.integral_sub
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d)
    ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d)

/-- Equality of actual rectangular integrals from equality on their closed rectangles. -/
theorem double_integral_congr {F G : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (he : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, F u v=G u v) :
    (∫ u in a..b, ∫ v in c..d, F u v) = ∫ u in a..b, ∫ v in c..d, G u v := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hcd] at hv
  exact he u hu v hv

/-- A continuous extension of the actual difference of the full and projected Green integrands. -/
@[expose] def differenceIntegrand {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T t s u v : ℝ) := clampedResponse d t u*clampedResponse d s v*
      (clampedCorrelation d u v^(p-1)-prefixKernel h T (max 0 u) (max 0 v)^(p-1))

theorem differenceIntegrand_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T t s : ℝ) :
    Continuous (Function.uncurry (differenceIntegrand h T t s)) :=
  (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_fst)).mul
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_snd))).mul
      (((clampedCorrelation_continuous h).pow (p-1)).sub
        ((prefixKernel_clamped_continuous h hb T).pow (p-1)))

theorem differenceIntegrand_eq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t s u v : ℝ} (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 s) :
    differenceIntegrand h T t s u v = d.R t u*d.R s v*
      (d.C u v^(p-1)-prefixKernel h T u v^(p-1)) := by
  unfold differenceIntegrand
  rw [clampedResponse_eq hu.1 hu.2, clampedResponse_eq hv.1 hv.2,
    clampedCorrelation_eq hu.1 hv.1, max_eq_right hu.1, max_eq_right hv.1]

/-- The past cancels exactly in the actual colored memory difference. -/
theorem colored_past_cancellation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (hT : 0 ≤ T) (ht : T ≤ t) (hs : T ≤ s) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*
      (d.C u v^(p-1)-prefixKernel h T u v^(p-1))) =
      ∫ u in T..t, ∫ v in T..s, d.R t u*d.R s v*
        (d.C u v^(p-1)-prefixKernel h T u v^(p-1)) := by
  calc
    _ = ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, differenceIntegrand h T t s u v :=
      double_integral_congr (hT.trans ht) (hT.trans hs)
        (fun _ hu _ hv => (differenceIntegrand_eq h hu hv).symm)
    _ = ∫ u in T..t, ∫ v in T..s, differenceIntegrand h T t s u v := by
      apply rectangle_past_cancellation (differenceIntegrand_continuous h hb T t s) hT ht hs
      · intro u hu v hv
        rw [differenceIntegrand_eq h ⟨hu.1,hu.2.trans ht⟩ hv,
          prefixKernel_eq_correlation_of_past_left h hb hu.1 hv.1 hu.2, sub_self, mul_zero]
      · intro u hu v hv
        rw [differenceIntegrand_eq h hu ⟨hv.1,hv.2.trans hs⟩,
          prefixKernel_eq_correlation_of_past_right h hb hu.1 hv.1 hv.2, sub_self, mul_zero]
    _ = _ := double_integral_congr ht hs (fun _ hu _ hv =>
      differenceIntegrand_eq h ⟨hT.trans hu.1,hu.2⟩ ⟨hT.trans hv.1,hv.2⟩)


/-- Subtraction of the two actual colored Green terms is the actual difference integral. -/
theorem colored_difference_integral {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*
      (d.C u v^(p-1)-prefixKernel h T u v^(p-1))) =
      (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*d.C u v^(p-1)) -
      (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*prefixKernel h T u v^(p-1)) := by
  let F : ℝ → ℝ → ℝ := fun u v => clampedResponse d t u*clampedResponse d s v*clampedCorrelation d u v^(p-1)
  let G : ℝ → ℝ → ℝ := fun u v => clampedResponse d t u*clampedResponse d s v*
    prefixKernel h T (max 0 u) (max 0 v)^(p-1)
  have hR : Continuous (fun z : ℝ × ℝ => clampedResponse d t z.1*clampedResponse d s z.2) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_fst)).mul
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_snd))
  have hF : Continuous (Function.uncurry F) := hR.mul ((clampedCorrelation_continuous h).pow (p-1))
  have hG : Continuous (Function.uncurry G) := hR.mul ((prefixKernel_clamped_continuous h hb T).pow (p-1))
  have hf : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*d.C u v^(p-1) := by
    apply double_integral_congr ht hs
    intro u hu v hv
    dsimp only [F]
    rw [clampedResponse_eq hu.1 hu.2, clampedResponse_eq hv.1 hv.2, clampedCorrelation_eq hu.1 hv.1]
  have hg : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, G u v) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, d.R t u*d.R s v*prefixKernel h T u v^(p-1) := by
    apply double_integral_congr ht hs
    intro u hu v hv
    dsimp only [G]
    rw [clampedResponse_eq hu.1 hu.2, clampedResponse_eq hv.1 hv.2, max_eq_right hu.1, max_eq_right hv.1]
  calc
    _ = ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v-G u v := by
      apply double_integral_congr ht hs
      intro u hu v hv
      dsimp only [F, G]
      rw [clampedResponse_eq hu.1 hu.2, clampedResponse_eq hv.1 hv.2,
        clampedCorrelation_eq hu.1 hv.1, max_eq_right hu.1, max_eq_right hv.1]
      ring
    _ = _ := by rw [double_integral_sub hF hG, hf, hg]

/-- The exact closed future rectangle, with the complete older memory canceled before taking limits. -/
theorem closed_absolute_rectangle {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (hT : 0 ≤ T) (ht : T ≤ t) (hs : T ≤ s) :
    prefixKernel h T t s = d.C t s - 2*(∫ u in T..min t s, d.R t u*d.R s u) -
      β^2*(p : ℝ)*(∫ u in T..t, ∫ v in T..s, d.R t u*d.R s v*
        (d.C u v^(p-1)-prefixKernel h T u v^(p-1))) := by
  have htc := hT.trans ht
  have hsc := hT.trans hs
  have hC := GreenCovarianceClosure.green_covariance_identity h htc hsc
  unfold greenCovariance at hC
  have hK := projected_green_identity h hb hT ht hs
  have hc := colored_difference_integral h hb T htc hsc
  rw [colored_past_cancellation h hb hT ht hs] at hc
  have hcoef := congrArg (fun x => β^2*(p : ℝ)*x) hc
  have hn : Continuous (fun u => clampedResponse d t u*clampedResponse d s u) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).mul
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))
  have hi1 : IntervalIntegrable (fun u => d.R t u*d.R s u) volume 0 T := by
    apply (hn.intervalIntegrable 0 T).congr
    intro u hu
    rw [uIoc_of_le hT] at hu
    dsimp only
    rw [clampedResponse_eq hu.1.le (hu.2.trans ht), clampedResponse_eq hu.1.le (hu.2.trans hs)]
  have hi2 : IntervalIntegrable (fun u => d.R t u*d.R s u) volume T (min t s) := by
    apply (hn.intervalIntegrable T (min t s)).congr
    intro u hu
    rw [uIoc_of_le (le_min ht hs)] at hu
    dsimp only
    rw [clampedResponse_eq (hT.trans hu.1.le) (hu.2.trans (min_le_left _ _)),
      clampedResponse_eq (hT.trans hu.1.le) (hu.2.trans (min_le_right _ _))]
  have hnoise := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  linarith [hC, hK, hcoef, hnoise]

/-- Translation of an actual interval integral by its lower endpoint. -/
theorem integral_translate (F : ℝ → ℝ) (T a : ℝ) :
    (∫ u in T..T+a, F u) = ∫ u in (0 : ℝ)..a, F (T+u) := by
  simpa only [add_zero] using (intervalIntegral.integral_comp_add_left F T (a := 0) (b := a)).symm

/-- The source's exact closed rectangle in future-offset coordinates. -/
theorem closed_future_rectangle {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T a b : ℝ}
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hb' : 0 ≤ b) :
    futureKernel h T a b = d.C (T+a) (T+b) -
      2*(∫ u in (0 : ℝ)..min a b, d.R (T+a) (T+u)*d.R (T+b) (T+u)) -
      β^2*(p : ℝ)*(∫ u in (0 : ℝ)..a, ∫ v in (0 : ℝ)..b,
        d.R (T+a) (T+u)*d.R (T+b) (T+v)*
          (d.C (T+u) (T+v)^(p-1)-futureKernel h T u v^(p-1))) := by
  unfold futureKernel
  rw [closed_absolute_rectangle h hb hT (by linarith) (by linarith), ← add_min,
    integral_translate]
  congr 2
  rw [integral_translate]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [integral_translate]

end SphericalAging.PrefixReflection
