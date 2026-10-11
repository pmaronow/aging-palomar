module

public import SphericalAging.CausalTree
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Tactic.Linarith

public section

/-! Brownian leaf-time prefixes and their actual completed tensor extensions.
The noise cutoff multiplies representatives by `1_{(-∞,T]}` inside
`L²((0,∞),du)` and leaves the initial real direction fixed.
-/
noncomputable section
open MeasureTheory UniformSpace
open scoped InnerProductSpace TensorProduct ENNReal
namespace SphericalAging.CausalTree

/-- Actual noise-leaf cutoff, defined on almost-everywhere equivalence classes. -/
@[expose] def noisePrefix (T : ℝ) (f : NoiseSpace) : NoiseSpace :=
  ((Lp.memLp f).indicator measurableSet_Iic).toLp ((Set.Iic T).indicator f)

theorem noisePrefix_coe (T : ℝ) (f : NoiseSpace) :
    ⇑(noisePrefix T f) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (Set.Iic T).indicator f :=
  MemLp.coeFn_toLp _

theorem noisePrefix_norm_le (T : ℝ) (f : NoiseSpace) : ‖noisePrefix T f‖ ≤ ‖f‖ := by
  rw [noisePrefix, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_indicator_le _ measurableSet_Iic)

theorem noisePrefix_add (T : ℝ) (f g : NoiseSpace) :
    noisePrefix T (f + g) = noisePrefix T f + noisePrefix T g := by
  apply Lp.ext
  filter_upwards [noisePrefix_coe T (f + g), noisePrefix_coe T f, noisePrefix_coe T g,
    Lp.coeFn_add f g, Lp.coeFn_add (noisePrefix T f) (noisePrefix T g)] with x hfg hf hg ha hb
  rw [hfg, hb, Pi.add_apply, hf, hg]
  by_cases hx : x ≤ T
  · simpa only [Set.indicator, Set.mem_Iic, ite_eq_left hx, Pi.add_apply] using ha
  · simp only [Set.indicator, Set.mem_Iic, ite_eq_right hx, zero_add]

theorem noisePrefix_smul (T a : ℝ) (f : NoiseSpace) :
    noisePrefix T (a • f) = a • noisePrefix T f := by
  apply Lp.ext
  filter_upwards [noisePrefix_coe T (a • f), noisePrefix_coe T f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (noisePrefix T f)] with x haf hf ha hb
  rw [haf, hb, Pi.smul_apply, hf]
  by_cases hx : x ≤ T
  · simpa only [Set.indicator, Set.mem_Iic, ite_eq_left hx, Pi.smul_apply] using ha
  · simp only [Set.indicator, Set.mem_Iic, ite_eq_right hx, smul_zero]

/-- The cutoff is a real bounded linear contraction. -/
@[expose] def noisePrefixL (T : ℝ) : NoiseSpace →L[ℝ] NoiseSpace :=
  ({ toFun := noisePrefix T, map_add' := noisePrefix_add T, map_smul' := noisePrefix_smul T } :
    NoiseSpace →ₗ[ℝ] NoiseSpace).mkContinuous 1 (fun f => by simpa using noisePrefix_norm_le T f)

@[simp] theorem noisePrefixL_apply (T : ℝ) (f : NoiseSpace) : noisePrefixL T f = noisePrefix T f := rfl

theorem noisePrefix_comp (T S : ℝ) (f : NoiseSpace) :
    noisePrefix T (noisePrefix S f) = noisePrefix (min T S) f := by
  apply Lp.ext
  filter_upwards [noisePrefix_coe T (noisePrefix S f), noisePrefix_coe S f,
    noisePrefix_coe (min T S) f] with x hts hs hm
  rw [hts, hm]
  by_cases ht : x ≤ T <;> by_cases hS : x ≤ S <;>
    simp_all [Set.indicator, le_min_iff]

/-- The initial real coordinate is always retained. -/
@[expose] def leafPrefix (T : ℝ) : LeafSpace →L[ℝ] LeafSpace :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ NoiseSpace).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ ℝ).prodMap (noisePrefixL T) |>.comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ NoiseSpace).toContinuousLinearMap)

@[simp] theorem leafPrefix_fst (T : ℝ) (f : LeafSpace) : (leafPrefix T f).fst = f.fst := rfl
@[simp] theorem leafPrefix_snd (T : ℝ) (f : LeafSpace) :
    (leafPrefix T f).snd = noisePrefix T f.snd := rfl

@[simp] theorem leafPrefix_initial (T : ℝ) : leafPrefix T initialLeaf = initialLeaf := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · simp [initialLeaf, ← noisePrefixL_apply]

theorem leafPrefix_norm_le (T : ℝ) (f : LeafSpace) : ‖leafPrefix T f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, leafPrefix_fst, leafPrefix_snd]
  nlinarith [noisePrefix_norm_le T f.snd, norm_nonneg (noisePrefix T f.snd), norm_nonneg f.snd]

set_option maxHeartbeats 2400000 in
theorem leafPrefix_comp (T S : ℝ) (f : LeafSpace) : leafPrefix T (leafPrefix S f) = leafPrefix (min T S) f := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · exact noisePrefix_comp T S f.snd

namespace HilbertDatum
/-- Canonical bounded map on actual completed binary Hilbert tensors. -/
@[expose, reducible] def tensorMap (A B : HilbertDatum) (f : A.Carrier →L[ℝ] A.Carrier)
    (g : B.Carrier →L[ℝ] B.Carrier) : (tensor A B).Carrier →L[ℝ] (tensor A B).Carrier :=
  (Completion.toComplL.comp (TensorProduct.mapL f g)).extend Completion.toComplL

@[simp] theorem tensorMap_coe (A B : HilbertDatum) (f : A.Carrier →L[ℝ] A.Carrier)
    (g : B.Carrier →L[ℝ] B.Carrier) (x : A.Carrier ⊗[ℝ] B.Carrier) :
    tensorMap A B f g (x : Completion _) = ((TensorProduct.mapL f g x) : Completion _) := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _) x

@[simp] theorem tensorMap_pure (A B : HilbertDatum) (f : A.Carrier →L[ℝ] A.Carrier)
    (g : B.Carrier →L[ℝ] B.Carrier) (x : A.Carrier) (y : B.Carrier) :
    tensorMap A B f g (pure A B x y) = pure A B (f x) (g y) := by
  calc
    _ = ((TensorProduct.mapL f g (x ⊗ₜ[ℝ] y)) : Completion _) := tensorMap_coe A B f g _
    _ = _ := congrArg (fun w : A.Carrier ⊗[ℝ] B.Carrier => (w : Completion (A.Carrier ⊗[ℝ] B.Carrier)))
      (TensorProduct.mapL_tmul f g x y)

theorem tensorMap_norm_le (A B : HilbertDatum) (f : A.Carrier →L[ℝ] A.Carrier)
    (g : B.Carrier →L[ℝ] B.Carrier) (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (hg : ∀ y, ‖g y‖ ≤ ‖y‖)
    (z : (tensor A B).Carrier) : ‖tensorMap A B f g z‖ ≤ ‖z‖ := by
  have hf1 : ‖f‖ ≤ 1 := f.opNorm_le_bound (by norm_num) (fun x => by simpa using hf x)
  have hg1 : ‖g‖ ≤ 1 := g.opNorm_le_bound (by norm_num) (fun x => by simpa using hg x)
  have hmap : ‖TensorProduct.mapL f g‖ ≤ 1 :=
    le_trans (TensorProduct.norm_mapL_le _ _) (mul_le_one₀ hf1 (norm_nonneg _) hg1)
  refine Completion.induction_on z (isClosed_le ((tensorMap A B f g).continuous.norm) continuous_norm) ?_
  intro x
  rw [tensorMap_coe, Completion.norm_coe, Completion.norm_coe]
  exact le_trans ((TensorProduct.mapL f g).le_opNorm x) (by nlinarith [norm_nonneg x])

/-- Maps on completed tensors are determined by all their pure tensors. -/
theorem tensor_ext (A B C : HilbertDatum)
    {f g : (tensor A B).Carrier →L[ℝ] C.Carrier}
    (h : ∀ x y, f (pure A B x y) = g (pure A B x y)) : f = g := by
  ext z
  refine Completion.induction_on z (isClosed_eq f.continuous g.continuous) ?_
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy => simp only [Completion.coe_add, map_add, hx, hy]

/-- Tensor extensions preserve composition exactly. -/
theorem tensorMap_comp (A B : HilbertDatum)
    (f f' : A.Carrier →L[ℝ] A.Carrier) (g g' : B.Carrier →L[ℝ] B.Carrier) :
    (tensorMap A B f g).comp (tensorMap A B f' g') = tensorMap A B (f.comp f') (g.comp g') := by
  apply tensor_ext A B (tensor A B)
  intro x y
  change tensorMap A B f g (tensorMap A B f' g' (pure A B x y)) = _
  rw [tensorMap_pure A B f' g' x y, tensorMap_pure A B f g (f' x) (g' y),
    tensorMap_pure A B (f.comp f') (g.comp g') x y]
  rfl

/-- Finite ordered completed tensor map. -/
@[expose, reducible] def finiteTensorMap : (n : ℕ) → (A : Fin n → HilbertDatum) →
    ((i : Fin n) → (A i).Carrier →L[ℝ] (A i).Carrier) →
      (finiteTensor n A).Carrier →L[ℝ] (finiteTensor n A).Carrier
  | 0, _, _ => ContinuousLinearMap.id ℝ ℝ
  | n + 1, A, f => tensorMap (A 0) (finiteTensor n (fun i => A i.succ))
      (f 0) (finiteTensorMap n (fun i => A i.succ) (fun i => f i.succ))

theorem finiteTensorMap_norm_le (n : ℕ) (A : Fin n → HilbertDatum)
    (f : (i : Fin n) → (A i).Carrier →L[ℝ] (A i).Carrier)
    (hf : ∀ i x, ‖f i x‖ ≤ ‖x‖) (z : (finiteTensor n A).Carrier) :
    ‖finiteTensorMap n A f z‖ ≤ ‖z‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact tensorMap_norm_le (A 0) (finiteTensor n (fun i => A i.succ)) (f 0)
        (finiteTensorMap n (fun i => A i.succ) (fun i => f i.succ)) (hf 0)
        (ih (fun i => A i.succ) (fun i => f i.succ) (fun i => hf i.succ)) z

@[simp] theorem finiteTensorMap_pure (n : ℕ) (A : Fin n → HilbertDatum)
    (f : (i : Fin n) → (A i).Carrier →L[ℝ] (A i).Carrier)
    (x : (i : Fin n) → (A i).Carrier) :
    finiteTensorMap n A f (finitePure n A x) = finitePure n A (fun i => f i (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        _ = pure (A 0) (finiteTensor n (fun i => A i.succ)) ((f 0) (x 0))
            (finiteTensorMap n (fun i => A i.succ) (fun i => f i.succ)
              (finitePure n (fun i => A i.succ) (fun i => x i.succ))) :=
          tensorMap_pure (A 0) (finiteTensor n (fun i => A i.succ)) (f 0) _ _ _
        _ = _ := by rw [ih]; rfl

end HilbertDatum

theorem HilbertDatum.finiteTensorMap_comp (n : ℕ) (A : Fin n → HilbertDatum)
    (f g : (i : Fin n) → (A i).Carrier →L[ℝ] (A i).Carrier) :
    (HilbertDatum.finiteTensorMap n A f).comp (HilbertDatum.finiteTensorMap n A g) =
      HilbertDatum.finiteTensorMap n A (fun i => (f i).comp (g i)) := by
  induction n with
  | zero => ext x; rfl
  | succ n ih =>
      change (HilbertDatum.tensorMap (A 0) (HilbertDatum.finiteTensor n (fun i => A i.succ))
        (f 0) (HilbertDatum.finiteTensorMap n (fun i => A i.succ) (fun i => f i.succ))).comp
        (HilbertDatum.tensorMap (A 0) (HilbertDatum.finiteTensor n (fun i => A i.succ))
          (g 0) (HilbertDatum.finiteTensorMap n (fun i => A i.succ) (fun i => g i.succ))) = _
      rw [HilbertDatum.tensorMap_comp, ih]

/-- The concrete leaf cutoff in every completed leaf tensor, recursively grafted. -/
@[expose] def fiberPrefix {m : ℕ} (T : ℝ) : (t : Tree m) → (fiber t).Carrier →L[ℝ] (fiber t).Carrier :=
  Tree.rec (leafPrefix T) (fun ts prefixes =>
    HilbertDatum.finiteTensorMap m (fun i => fiber (ts i)) prefixes)

@[simp] theorem fiberPrefix_leaf {m : ℕ} (T : ℝ) : fiberPrefix T (Tree.leaf : Tree m) = leafPrefix T := rfl
@[simp] theorem fiberPrefix_graft {m : ℕ} (T : ℝ) (ts : Fin m → Tree m) :
    fiberPrefix T (Tree.graft ts) =
      HilbertDatum.finiteTensorMap m (fun i => fiber (ts i)) (fun i => fiberPrefix T (ts i)) := rfl

theorem fiberPrefix_norm_le {m : ℕ} (T : ℝ) (t : Tree m) (x : (fiber t).Carrier) :
    ‖fiberPrefix T t x‖ ≤ ‖x‖ := by
  induction t with
  | leaf => exact leafPrefix_norm_le T x
  | graft ts ih => exact HilbertDatum.finiteTensorMap_norm_le _ _ _ ih x

theorem fiberPrefix_comp {m : ℕ} (T S : ℝ) (t : Tree m) :
    (fiberPrefix T t).comp (fiberPrefix S t) = fiberPrefix (min T S) t := by
  induction t with
  | leaf => ext x; exact leafPrefix_comp T S x
  | graft ts ih =>
      simp only [fiberPrefix_graft, HilbertDatum.finiteTensorMap_comp]
      congr 1
      funext i
      exact ih i

/-- Actual leaf-time cutoff on the complete causal-tree Hilbert direct sum. -/
@[expose] def timePrefix {m : ℕ} (T : ℝ) (v : Space m) : Space m :=
  ⟨fun t => fiberPrefix T t (v t), (lp.memℓp v).mono' (fun t => fiberPrefix_norm_le T t (v t))⟩

@[simp] theorem timePrefix_apply {m : ℕ} (T : ℝ) (v : Space m) (t : Tree m) :
    timePrefix T v t = fiberPrefix T t (v t) := rfl

theorem timePrefix_norm_le {m : ℕ} (T : ℝ) (v : Space m) : ‖timePrefix T v‖ ≤ ‖v‖ :=
  lp.norm_mono (by norm_num) (fun t => fiberPrefix_norm_le T t (v t))

theorem timePrefix_add {m : ℕ} (T : ℝ) (v w : Space m) :
    timePrefix T (v + w) = timePrefix T v + timePrefix T w := by
  ext t
  simp only [timePrefix_apply, lp.coeFn_add, Pi.add_apply, map_add]

theorem timePrefix_smul {m : ℕ} (T a : ℝ) (v : Space m) :
    timePrefix T (a • v) = a • timePrefix T v := by
  ext t
  simp only [timePrefix_apply, lp.coeFn_smul, Pi.smul_apply, map_smul]

/-- The actual leaf-time prefix is a bounded real linear contraction. -/
@[expose] def timePrefixL (m : ℕ) (T : ℝ) : Space m →L[ℝ] Space m :=
  ({ toFun := timePrefix T, map_add' := timePrefix_add T, map_smul' := timePrefix_smul T } :
    Space m →ₗ[ℝ] Space m).mkContinuous 1 (fun v => by simpa using timePrefix_norm_le T v)

@[simp] theorem timePrefix_comp {m : ℕ} (T S : ℝ) (v : Space m) :
    timePrefix T (timePrefix S v) = timePrefix (min T S) v := by
  ext t
  exact congrArg (fun f : (fiber t).Carrier →L[ℝ] (fiber t).Carrier => f (v t)) (fiberPrefix_comp T S t)

@[simp] theorem timePrefix_idempotent {m : ℕ} (T : ℝ) (v : Space m) :
    timePrefix T (timePrefix T v) = timePrefix T v := by simp

theorem timePrefix_height_commute {m : ℕ} (T : ℝ) (j : ℕ) (v : Space m) :
    timePrefix T (heightProjection j v) = heightProjection j (timePrefix T v) := by
  ext t
  simp only [timePrefix_apply, heightProjection_apply]
  split_ifs <;> simp

theorem timePrefix_heightPrefix_commute {m : ℕ} (T : ℝ) (j : ℕ) (v : Space m) :
    timePrefix T (heightPrefix j v) = heightPrefix j (timePrefix T v) := by
  ext t
  simp only [timePrefix_apply, heightPrefix_apply]
  split_ifs <;> simp

/-- The distinguished initial direction is retained at every leaf time. -/
@[simp] theorem timePrefix_initialVector (m : ℕ) (T : ℝ) :
    timePrefix T (initialVector m) = initialVector m := by
  classical
  ext t
  cases t <;> simp [timePrefix_apply, initialVector, lp.single_apply]

/-- Actual tensor prefix intertwining for the grafted pure power, in every arity. -/
theorem timePrefix_graftPower {m : ℕ} (T : ℝ) (v : Space m) :
    timePrefix T (graftPower v) = graftPower (timePrefix T v) := by
  ext t
  cases t with
  | leaf => simp
  | graft ts =>
      simp only [timePrefix_apply, graftPower_graft, fiberPrefix_graft]
      exact HilbertDatum.finiteTensorMap_pure m (fun i => fiber (ts i))
        (fun i => fiberPrefix T (ts i)) (fun i => v (ts i))


/-- A linear idempotent contraction on a real Hilbert space is orthogonal. -/
theorem idempotent_contraction_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E) (hid : ∀ x, P (P x) = P x) (hcon : ∀ x, ‖P x‖ ≤ ‖x‖) (v w : E) :
    inner ℝ (P v) (w - P w) = 0 := by
  let x := P v
  let y := w - P w
  have hPx : P x = x := hid v
  have hPy : P y = 0 := by simp only [y, map_sub, hid, sub_self]
  have hn : ∀ a : ℝ, ‖x‖ ^ 2 ≤ ‖x + a • y‖ ^ 2 := by
    intro a
    have hh := hcon (x + a • y)
    rw [map_add, map_smul, hPx, hPy, smul_zero, add_zero] at hh
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
  by_cases hy : y = 0
  · change inner ℝ x y = 0
    simp [hy]
  · have hN : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
    have hh := hn (-inner ℝ x y / ‖y‖ ^ 2)
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hh
    have he : ‖x‖ ^ 2 + 2 * ((-inner ℝ x y / ‖y‖ ^ 2) * inner ℝ x y) +
        (-inner ℝ x y / ‖y‖ ^ 2) ^ 2 * ‖y‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ x y) ^ 2 / ‖y‖ ^ 2 := by
      field_simp [hN.ne']
      ring
    rw [he] at hh
    have hd : (inner ℝ x y) ^ 2 / ‖y‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (div_nonneg (sq_nonneg _) hN.le)
    have hzero := congrArg (fun r : ℝ => r * ‖y‖ ^ 2) hd
    rw [div_mul_cancel₀ _ hN.ne', zero_mul] at hzero
    exact sq_eq_zero_iff.mp hzero

/-- The constructed time prefix is an actual orthogonal Hilbert projection. -/
theorem timePrefix_orthogonal {m : ℕ} (T : ℝ) (v w : Space m) :
    inner ℝ (timePrefix T v) (w - timePrefix T w) = 0 :=
  idempotent_contraction_orthogonal (timePrefixL m T)
    (timePrefix_idempotent T) (timePrefix_norm_le T) v w

/-- Self-adjointness, stated as the defining real inner-product identity. -/
theorem timePrefix_selfAdjoint {m : ℕ} (T : ℝ) (v w : Space m) :
    inner ℝ (timePrefix T v) w = inner ℝ v (timePrefix T w) := by
  have h1 := timePrefix_orthogonal T v w
  have h2 := timePrefix_orthogonal T w v
  rw [inner_sub_right] at h1 h2
  rw [← real_inner_comm (timePrefix T w) v, ← real_inner_comm (timePrefix T w) (timePrefix T v)] at h2
  linarith

/-- Exact prefix and complement Pythagoras identity. -/
theorem timePrefix_norm_sq_split {m : ℕ} (T : ℝ) (v : Space m) :
    ‖v‖ ^ 2 = ‖timePrefix T v‖ ^ 2 + ‖v - timePrefix T v‖ ^ 2 := by
  have he : v = timePrefix T v + (v - timePrefix T v) := by simp
  conv_lhs => rw [he]
  rw [norm_add_sq_real, timePrefix_orthogonal]
  ring

/-- The actual Brownian leaf cone, with nonnegative initial and noise coordinates. -/
@[expose] def LeafNonnegative (f : LeafSpace) : Prop :=
  0 ≤ f.fst ∧ ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ f.snd x

theorem leafPrefix_nonnegative (T : ℝ) (f : LeafSpace) (hf : LeafNonnegative f) :
    LeafNonnegative (leafPrefix T f) := by
  refine ⟨hf.1, ?_⟩
  filter_upwards [hf.2, noisePrefix_coe T f.snd] with x hx hp
  change 0 ≤ noisePrefix T f.snd x
  rw [hp]
  by_cases hT : x ≤ T
  · simpa only [Set.indicator, Set.mem_Iic, ite_eq_left hT] using hx
  · simp only [Set.indicator, Set.mem_Iic, ite_eq_right hT, le_refl]

/-- The completed tensor-domain cutoff, applied component by component. -/
@[expose] def rootTimePrefix {m : ℕ} (T : ℝ) (w : RootTensorSpace m) : RootTensorSpace m :=
  ⟨fun ts => fiberPrefix T (Tree.graft ts) (w ts),
    (lp.memℓp w).mono' (fun ts => fiberPrefix_norm_le T (Tree.graft ts) (w ts))⟩

@[simp] theorem rootTimePrefix_apply {m : ℕ} (T : ℝ) (w : RootTensorSpace m) (ts : Fin m → Tree m) :
    rootTimePrefix T w ts = fiberPrefix T (Tree.graft ts) (w ts) := rfl

/-- Full linear graft-prefix intertwining in the complete distributed tensor-domain. -/
theorem timePrefix_graft {m : ℕ} (T : ℝ) (w : RootTensorSpace m) :
    timePrefix T (graft w) = graft (rootTimePrefix T w) := by
  ext t
  cases t <;> simp

/-- Cutoffs tensorize on actual pure powers. -/
theorem rootTimePrefix_tensorPower {m : ℕ} (T : ℝ) (v : Space m) :
    rootTimePrefix T (tensorPower v) = tensorPower (timePrefix T v) := by
  ext ts
  simp only [rootTimePrefix_apply, tensorPower_apply, fiberPrefix_graft]
  exact HilbertDatum.finiteTensorMap_pure m (fun i => fiber (ts i))
    (fun i => fiberPrefix T (ts i)) (fun i => v (ts i))

end SphericalAging.CausalTree
