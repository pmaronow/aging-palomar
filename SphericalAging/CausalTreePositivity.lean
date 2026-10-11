module

public import SphericalAging.CausalTreeRealization
public import SphericalAging.LpProductTensor
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Constructions.Pi

public section

/-! Literal leaf labels and positivity for the causal tree Hilbert realization. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory Filter
namespace SphericalAging.CausalTreePositivity
open CausalTree CausalTreeRealization CKSpecification GreenCovariance
local instance (α : Type) : DecidableEq α := Classical.decEq α

@[expose] abbrev LeafLabel := Unit ⊕ ℝ

@[expose] def initialLabelEmbedding : MeasurableEmbedding (Sum.inl : Unit → LeafLabel) where
  injective := Sum.inl_injective
  measurable := measurable_inl
  measurableSet_image' := fun _ hs => hs.inl_image

@[expose] def noiseLabelEmbedding : MeasurableEmbedding (Sum.inr : ℝ → LeafLabel) where
  injective := Sum.inr_injective
  measurable := measurable_inr
  measurableSet_image' := fun _ hs => hs.inr_image

/-- A unit initial atom plus Lebesgue measure on the positive noise times. -/
@[expose] def leafMeasure : Measure LeafLabel :=
  (Measure.dirac ()).map Sum.inl + (volume.restrict (Ioi (0 : ℝ))).map Sum.inr

instance : SFinite leafMeasure := by unfold leafMeasure; infer_instance

instance : SigmaFinite leafMeasure := by
  letI : SigmaFinite ((Measure.dirac ()).map (Sum.inl : Unit → LeafLabel)) :=
    initialLabelEmbedding.sigmaFinite_map
  letI : SigmaFinite ((volume.restrict (Ioi (0 : ℝ))).map (Sum.inr : ℝ → LeafLabel)) :=
    noiseLabelEmbedding.sigmaFinite_map
  unfold leafMeasure
  infer_instance

/-- Actual function of the initial/noise label represented by a Brownian leaf vector. -/
@[expose] def leafLabelFunction (v : LeafSpace) : LeafLabel → ℝ :=
  Sum.elim (fun _ => v.fst) v.snd

theorem leafLabelFunction_memLp (v : LeafSpace) : MemLp (leafLabelFunction v) 2 leafMeasure := by
  have hi : MemLp (leafLabelFunction v) 2 ((Measure.dirac ()).map Sum.inl) :=
    initialLabelEmbedding.memLp_map_measure_iff.mpr (memLp_const v.fst)
  have hn : MemLp (leafLabelFunction v) 2 ((volume.restrict (Ioi (0 : ℝ))).map Sum.inr) :=
    noiseLabelEmbedding.memLp_map_measure_iff.mpr (Lp.memLp v.snd)
  unfold leafMeasure
  rw [memLp_two_iff_integrable_sq (hi.aestronglyMeasurable.add_measure hn.aestronglyMeasurable),
    integrable_add_measure]
  exact ⟨hi.integrable_sq, hn.integrable_sq⟩

/-- The Brownian leaf as an actual `L²` function of its label. -/
@[expose] def leafLabelVector (v : LeafSpace) : Lp ℝ 2 leafMeasure :=
  (leafLabelFunction_memLp v).toLp (leafLabelFunction v)

theorem leafLabelVector_coe (v : LeafSpace) :
    (leafLabelVector v : LeafLabel → ℝ) =ᵐ[leafMeasure] leafLabelFunction v :=
  (leafLabelFunction_memLp v).coeFn_toLp

theorem leafLabelFunction_add (v w : LeafSpace) :
    leafLabelFunction (v + w) =ᵐ[leafMeasure] fun x => leafLabelFunction v x + leafLabelFunction w x := by
  change ∀ᵐ x ∂leafMeasure, _
  rw [leafMeasure, ae_add_measure_iff]
  constructor
  · rw [initialLabelEmbedding.ae_map_iff]
    exact Filter.Eventually.of_forall (fun _ => by simp [leafLabelFunction])
  · rw [noiseLabelEmbedding.ae_map_iff]
    filter_upwards [Lp.coeFn_add v.snd w.snd] with x hx
    simpa [leafLabelFunction] using hx

theorem leafLabelFunction_smul (a : ℝ) (v : LeafSpace) :
    leafLabelFunction (a • v) =ᵐ[leafMeasure] fun x => a • leafLabelFunction v x := by
  change ∀ᵐ x ∂leafMeasure, _
  rw [leafMeasure, ae_add_measure_iff]
  constructor
  · rw [initialLabelEmbedding.ae_map_iff]
    exact Filter.Eventually.of_forall (fun _ => by simp [leafLabelFunction])
  · rw [noiseLabelEmbedding.ae_map_iff]
    filter_upwards [Lp.coeFn_smul a v.snd] with x hx
    simpa [leafLabelFunction] using hx

theorem leafLabelVector_add (v w : LeafSpace) : leafLabelVector (v + w) = leafLabelVector v + leafLabelVector w := by
  apply Lp.ext
  filter_upwards [leafLabelVector_coe (v + w), leafLabelVector_coe v, leafLabelVector_coe w,
    leafLabelFunction_add v w, Lp.coeFn_add (leafLabelVector v) (leafLabelVector w)] with x hvw hv hw hf hs
  rw [hvw, hf, hs]
  change leafLabelFunction v x + leafLabelFunction w x = leafLabelVector v x + leafLabelVector w x
  rw [hv, hw]

theorem leafLabelVector_smul (a : ℝ) (v : LeafSpace) : leafLabelVector (a • v) = a • leafLabelVector v := by
  apply Lp.ext
  filter_upwards [leafLabelVector_coe (a • v), leafLabelVector_coe v,
    leafLabelFunction_smul a v, Lp.coeFn_smul a (leafLabelVector v)] with x hav hv hf hs
  rw [hav, hf, hs]
  change a • leafLabelFunction v x = a • leafLabelVector v x
  rw [hv]

theorem leafLabelVector_inner (v w : LeafSpace) :
    inner ℝ (leafLabelVector v) (leafLabelVector w) = inner ℝ v w := by
  rw [L2.inner_def]
  have he : (∫ x, inner ℝ (leafLabelVector v x) (leafLabelVector w x) ∂leafMeasure) =
      ∫ x, leafLabelFunction v x * leafLabelFunction w x ∂leafMeasure := by
    apply integral_congr_ae
    filter_upwards [leafLabelVector_coe v, leafLabelVector_coe w] with x hv hw
    rw [hv, hw]
    simp [RCLike.inner_apply, mul_comm]
  rw [he]
  have hi : Integrable (fun x => leafLabelFunction v x * leafLabelFunction w x)
      ((Measure.dirac ()).map Sum.inl) :=
    initialLabelEmbedding.integrable_map_iff.mpr (by simpa [leafLabelFunction] using
      (integrable_const (v.fst * w.fst) : Integrable (fun _ : Unit => v.fst * w.fst) (Measure.dirac ())))
  have hn : Integrable (fun x => leafLabelFunction v x * leafLabelFunction w x)
      ((volume.restrict (Ioi (0 : ℝ))).map Sum.inr) := by
    apply noiseLabelEmbedding.integrable_map_iff.mpr
    change Integrable (fun x : ℝ => v.snd x * w.snd x) (volume.restrict (Ioi (0 : ℝ)))
    simpa [RCLike.inner_apply, mul_comm] using L2.integrable_inner (𝕜 := ℝ) v.snd w.snd
  rw [leafMeasure, integral_add_measure hi hn,
    initialLabelEmbedding.integral_map, noiseLabelEmbedding.integral_map, WithLp.prod_inner_apply,
    L2.inner_def]
  simp [leafLabelFunction, RCLike.inner_apply, mul_comm]

/-- Literal initial/noise label embedding, preserving the Hilbert inner product exactly. -/
@[expose] def leafLabelIsometry : LeafSpace →ₗᵢ[ℝ] Lp ℝ 2 leafMeasure where
  toFun := leafLabelVector
  map_add' := leafLabelVector_add
  map_smul' := leafLabelVector_smul
  norm_map' := by
    intro v
    change ‖leafLabelVector v‖ = ‖v‖
    have hi := leafLabelVector_inner v v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (leafLabelVector v), norm_nonneg v]

/-- The source positivity definition for a one-leaf vector is literal label positivity. -/
theorem leafLabel_nonnegative_iff (v : LeafSpace) :
    (∀ᵐ x ∂leafMeasure, 0 ≤ leafLabelIsometry v x) ↔ LeafNonnegative v := by
  have he := leafLabelVector_coe v
  change (∀ᵐ x ∂leafMeasure, 0 ≤ leafLabelVector v x) ↔ _
  rw [Filter.eventually_congr (he.mono (fun _ h => by rw [h])), leafMeasure, ae_add_measure_iff,
    initialLabelEmbedding.ae_map_iff, noiseLabelEmbedding.ae_map_iff]
  simp [leafLabelFunction, LeafNonnegative]


/-- An actual measured space of ordered leaf labels. -/
structure LabelDatum where
  Label : Type
  measurable : MeasurableSpace Label
  measure : @Measure Label measurable
  sfinite : @SigmaFinite Label measurable measure

attribute [instance] LabelDatum.measurable LabelDatum.sfinite

@[expose, reducible] def LabelDatum.hilbert (D : LabelDatum) : HilbertDatum :=
  ⟨Lp ℝ 2 D.measure, inferInstance, inferInstance, inferInstance⟩

@[expose, reducible] def leafLabels : LabelDatum := ⟨LeafLabel, inferInstance, leafMeasure, inferInstance⟩
@[expose, reducible] def unitLabels : LabelDatum := ⟨Unit, inferInstance, Measure.dirac (), inferInstance⟩
@[expose, reducible] def productLabels (D E : LabelDatum) : LabelDatum :=
  ⟨D.Label × E.Label, inferInstance, D.measure.prod E.measure, inferInstance⟩

/-- A zero-fold tensor has one empty tuple, carrying unit mass. -/
@[expose] def unitLabelVector (a : ℝ) : Lp ℝ 2 (Measure.dirac ()) :=
  (memLp_const a).toLp (fun _ : Unit => a)

theorem unitLabelVector_coe (a : ℝ) :
    (unitLabelVector a : Unit → ℝ) =ᵐ[Measure.dirac ()] fun _ => a :=
  (memLp_const a).coeFn_toLp

@[expose] def unitLabelIsometry : ℝ →ₗᵢ[ℝ] Lp ℝ 2 (Measure.dirac ()) where
  toFun := unitLabelVector
  map_add' := by
    intro a b
    apply Lp.ext
    filter_upwards [unitLabelVector_coe (a + b), unitLabelVector_coe a, unitLabelVector_coe b,
      Lp.coeFn_add (unitLabelVector a) (unitLabelVector b)] with x hab ha hb hs
    change unitLabelVector (a + b) x = (unitLabelVector a + unitLabelVector b) x
    change (unitLabelVector a + unitLabelVector b) x = unitLabelVector a x + unitLabelVector b x at hs
    rw [hab, hs, ha, hb]
  map_smul' := by
    intro a b
    apply Lp.ext
    filter_upwards [unitLabelVector_coe (a • b), unitLabelVector_coe b,
      Lp.coeFn_smul a (unitLabelVector b)] with x hab hb hs
    change unitLabelVector (a • b) x = (a • unitLabelVector b) x
    change (a • unitLabelVector b) x = a • unitLabelVector b x at hs
    rw [hab, hs, hb]
  norm_map' := by
    intro a
    change ‖unitLabelVector a‖ = ‖a‖
    have hi : inner ℝ (unitLabelVector a) (unitLabelVector a) = a ^ 2 := by
      rw [L2.inner_def]
      have he : (∫ x, inner ℝ (unitLabelVector a x) (unitLabelVector a x) ∂Measure.dirac ()) =
          ∫ _ : Unit, a ^ 2 ∂Measure.dirac () := by
        apply integral_congr_ae
        filter_upwards [unitLabelVector_coe a] with x hx
        simp [hx, RCLike.inner_apply, pow_two]
      rw [he]
      simp
    rw [real_inner_self_eq_norm_sq] at hi
    rw [Real.norm_eq_abs]
    nlinarith [norm_nonneg (unitLabelVector a), abs_nonneg a, sq_abs a]

/-- Completed tensor embedding into the actual ordered product-label space. -/
@[expose] def tensorLabelIsometry (A B : HilbertDatum) (D E : LabelDatum)
    (f : A.Carrier →ₗᵢ[ℝ] Lp ℝ 2 D.measure) (g : B.Carrier →ₗᵢ[ℝ] Lp ℝ 2 E.measure) :
    (HilbertDatum.tensor A B).Carrier →ₗᵢ[ℝ] Lp ℝ 2 (D.measure.prod E.measure) :=
  LpProductTensor.completedIsometry.comp (TensorProduct.mapIsometry f g).completion

@[simp] theorem tensorLabelIsometry_pure (A B : HilbertDatum) (D E : LabelDatum)
    (f : A.Carrier →ₗᵢ[ℝ] Lp ℝ 2 D.measure) (g : B.Carrier →ₗᵢ[ℝ] Lp ℝ 2 E.measure)
    (x : A.Carrier) (y : B.Carrier) :
    tensorLabelIsometry A B D E f g (HilbertDatum.pure A B x y) = LpProductTensor.product (f x) (g y) := by
  change LpProductTensor.completedIsometry ((TensorProduct.mapIsometry f g).completion
    ((x ⊗ₜ[ℝ] y : A.Carrier ⊗[ℝ] B.Carrier) : UniformSpace.Completion _)) = _
  rw [LinearIsometry.completion_apply_coe]
  exact LpProductTensor.completedIsometry_tmul (f x) (g y)

@[expose, reducible] def finiteLabels : (n : ℕ) → (Fin n → LabelDatum) → LabelDatum
  | 0, _ => unitLabels
  | n + 1, D => productLabels (D 0) (finiteLabels n (fun i => D i.succ))

/-- Every actual finite completed tensor fiber is realized as functions of ordered labels. -/
@[expose] def finiteLabelIsometry : (n : ℕ) → (A : Fin n → HilbertDatum) → (D : Fin n → LabelDatum) →
    (∀ i, (A i).Carrier →ₗᵢ[ℝ] Lp ℝ 2 (D i).measure) →
      (HilbertDatum.finiteTensor n A).Carrier →ₗᵢ[ℝ] Lp ℝ 2 (finiteLabels n D).measure
  | 0, _, _, _ => unitLabelIsometry
  | n + 1, A, D, f => tensorLabelIsometry (A 0) (HilbertDatum.finiteTensor n (fun i => A i.succ))
      (D 0) (finiteLabels n (fun i => D i.succ)) (f 0)
      (finiteLabelIsometry n (fun i => A i.succ) (fun i => D i.succ) (fun i => f i.succ))

@[expose, reducible] def fiberLabels {m : ℕ} : CausalTree.Tree m → LabelDatum :=
  CausalTree.Tree.rec leafLabels (fun _ children => finiteLabels m children)

@[expose] def fiberLabelIsometry {m : ℕ} (τ : CausalTree.Tree m) :
    (fiber τ).Carrier →ₗᵢ[ℝ] Lp ℝ 2 (fiberLabels τ).measure := by
  induction τ with
  | leaf => exact leafLabelIsometry
  | graft ts children =>
      exact finiteLabelIsometry m (fun i => fiber (ts i)) (fun i => fiberLabels (ts i)) children

@[simp] theorem fiberLabelIsometry_leaf (m : ℕ) :
    fiberLabelIsometry (CausalTree.Tree.leaf : CausalTree.Tree m) = leafLabelIsometry := rfl

@[simp] theorem fiberLabelIsometry_graft {m : ℕ} (ts : Fin m → CausalTree.Tree m) :
    fiberLabelIsometry (CausalTree.Tree.graft ts) =
      finiteLabelIsometry m (fun i => fiber (ts i)) (fun i => fiberLabels (ts i))
        (fun i => fiberLabelIsometry (ts i)) := rfl

/-- Literal almost everywhere positivity in every ordered leaf-label fiber. -/
@[expose] def Nonnegative {m : ℕ} (v : CausalTree.Space m) : Prop :=
  ∀ τ, LpProductTensor.Nonnegative (fiberLabelIsometry τ (v τ))

theorem finiteLabelIsometry_pure_nonnegative (n : ℕ) (A : Fin n → HilbertDatum)
    (D : Fin n → LabelDatum) (f : ∀ i, (A i).Carrier →ₗᵢ[ℝ] Lp ℝ 2 (D i).measure)
    (x : ∀ i, (A i).Carrier) (hx : ∀ i, LpProductTensor.Nonnegative (f i (x i))) :
    LpProductTensor.Nonnegative (finiteLabelIsometry n A D f (HilbertDatum.finitePure n A x)) := by
  induction n with
  | zero =>
    change LpProductTensor.Nonnegative (unitLabelVector 1)
    filter_upwards [unitLabelVector_coe 1] with u hu
    simp [hu]
  | succ n ih =>
    change LpProductTensor.Nonnegative
      (tensorLabelIsometry (A 0) (HilbertDatum.finiteTensor n (fun i => A i.succ))
        (D 0) (finiteLabels n (fun i => D i.succ)) (f 0)
        (finiteLabelIsometry n (fun i => A i.succ) (fun i => D i.succ) (fun i => f i.succ))
        (HilbertDatum.pure _ _ (x 0) (HilbertDatum.finitePure n (fun i => A i.succ) (fun i => x i.succ))))
    rw [tensorLabelIsometry_pure]
    exact LpProductTensor.product_nonnegative _ _ (hx 0)
      (ih (fun i => A i.succ) (fun i => D i.succ) (fun i => f i.succ) (fun i => x i.succ) (fun i => hx i.succ))

/-- Actual grafting of a positive pure tensor remains positive in every leaf-label fiber. -/
theorem graftPower_nonnegative {m : ℕ} {v : CausalTree.Space m} (hv : Nonnegative v) :
    Nonnegative (graftPower v) := by
  intro τ
  cases τ with
  | leaf =>
    change LpProductTensor.Nonnegative (leafLabelIsometry (graftPower v CausalTree.Tree.leaf))
    rw [graftPower, graft_leaf, map_zero]
    exact LpProductTensor.nonnegative_zero _
  | graft ts =>
    rw [fiberLabelIsometry_graft]
    change LpProductTensor.Nonnegative
      (finiteLabelIsometry m (fun i => fiber (ts i)) (fun i => fiberLabels (ts i))
        (fun i => fiberLabelIsometry (ts i)) (HilbertDatum.finitePure m (fun i => fiber (ts i)) (fun i => v (ts i))))
    exact finiteLabelIsometry_pure_nonnegative m _ _ _ _ (fun i => hv (ts i))


/-- The actual function cone is closed in the tree Hilbert norm. -/
theorem nonnegative_isClosed (m : ℕ) : IsClosed {v : CausalTree.Space m | Nonnegative v} := by
  have he : {v : CausalTree.Space m | Nonnegative v} =
      ⋂ τ : CausalTree.Tree m, {v : CausalTree.Space m | LpProductTensor.Nonnegative (fiberLabelIsometry τ (v τ))} := by
    ext v
    simp [Nonnegative]
  rw [he]
  apply isClosed_iInter
  intro τ
  exact (LpProductTensor.nonnegative_isClosed (fiberLabels τ).measure).preimage
    ((fiberLabelIsometry τ).continuous.comp (lp.evalCLM ℝ _ 2 τ).continuous)

theorem nonnegative_zero (m : ℕ) : Nonnegative (0 : CausalTree.Space m) := by
  intro τ
  change LpProductTensor.Nonnegative (fiberLabelIsometry τ 0)
  rw [map_zero]
  exact LpProductTensor.nonnegative_zero _

theorem nonnegative_add {m : ℕ} {v w : CausalTree.Space m} (hv : Nonnegative v) (hw : Nonnegative w) :
    Nonnegative (v + w) := by
  intro τ
  change LpProductTensor.Nonnegative (fiberLabelIsometry τ (v τ + w τ))
  rw [map_add]
  exact LpProductTensor.nonnegative_add (hv τ) (hw τ)

theorem nonnegative_smul {m : ℕ} {a : ℝ} {v : CausalTree.Space m} (ha : 0 ≤ a) (hv : Nonnegative v) :
    Nonnegative (a • v) := by
  intro τ
  change LpProductTensor.Nonnegative (fiberLabelIsometry τ (a • v τ))
  rw [map_smul]
  exact LpProductTensor.nonnegative_smul ha (hv τ)

theorem nonnegative_convex (m : ℕ) : Convex ℝ {v : CausalTree.Space m | Nonnegative v} := by
  intro v hv w hw a b ha hb _
  exact nonnegative_add (nonnegative_smul ha hv) (nonnegative_smul hb hw)

/-- Positivity of actual label functions is preserved by the Bochner memory integral. -/
theorem nonnegative_integral {m : ℕ} {A : Type} [MeasurableSpace A]
    {σ : Measure A} [IsFiniteMeasure σ] {f : A → CausalTree.Space m}
    (hf : ∀ᵐ a ∂σ, Nonnegative (f a)) (hfi : Integrable f σ) : Nonnegative (∫ a, f a ∂σ) := by
  by_cases hσ : σ = 0
  · simp only [hσ, integral_zero_measure]
    exact nonnegative_zero m
  · letI : NeZero σ := ⟨hσ⟩
    have ha := (nonnegative_convex m).average_mem (nonnegative_isClosed m) hf hfi
    rw [← measure_smul_average σ f]
    exact nonnegative_smul ENNReal.toReal_nonneg ha

theorem nonnegative_intervalIntegral {m : ℕ} {t : ℝ} (ht : 0 ≤ t) {f : ℝ → CausalTree.Space m}
    (hf : ∀ u ∈ Icc 0 t, Nonnegative (f u)) (hfi : IntervalIntegrable f volume 0 t) :
    Nonnegative (∫ u in (0 : ℝ)..t, f u) := by
  rw [intervalIntegral.integral_of_le ht]
  apply nonnegative_integral _ hfi.1
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact hf u ⟨hu.1.le, hu.2⟩

/-- The response row is an actual nonnegative initial/noise label function. -/
theorem leafResponseFeature_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    LeafNonnegative (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) t) := by
  constructor
  · change 0 ≤ clampedResponse d (max 0 t) 0
    rw [max_eq_right ht, clampedResponse_eq (le_refl 0) ht]
    exact hb.2 t 0 (le_refl 0) ht
  · change ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ (Real.sqrt 2 • noiseFeature (clampedResponse d) (clampedResponse_continuous h) (max 0 t)) u
    rw [max_eq_right ht]
    filter_upwards [Lp.coeFn_smul (Real.sqrt 2) (noiseFeature (clampedResponse d) (clampedResponse_continuous h) t),
      noiseFeature_coe (clampedResponse d) (clampedResponse_continuous h) t] with u hs hu
    change (Real.sqrt 2 • noiseFeature (clampedResponse d) (clampedResponse_continuous h) t) u =
      Real.sqrt 2 * noiseFeature (clampedResponse d) (clampedResponse_continuous h) t u at hs
    rw [hs, hu]
    by_cases hmem : u ∈ Ioc 0 t
    · rw [WhiteCovarianceKernel.rowCut, indicator_of_mem hmem, clampedResponse_eq hmem.1.le hmem.2]
      exact mul_nonneg (Real.sqrt_nonneg _) (hb.2 t u hmem.1.le hmem.2)
    · rw [WhiteCovarianceKernel.rowCut, indicator_of_notMem hmem, mul_zero]

theorem ckBaseVector_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    Nonnegative (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t) := by
  intro τ
  by_cases he : τ = CausalTree.Tree.leaf
  · subst τ
    rw [fiberLabelIsometry_leaf]
    change LpProductTensor.Nonnegative (leafLabelIsometry
      (lp.single (E := fun τ : CausalTree.Tree (p - 1) => (fiber τ).Carrier) 2 CausalTree.Tree.leaf
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) t) CausalTree.Tree.leaf))
    rw [lp.single_apply_self]
    exact (leafLabel_nonnegative_iff _).mpr (leafResponseFeature_nonnegative h hb ht)
  · have hz : baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t τ = 0 :=
      lp.single_apply_ne _ _ _ he
    rw [hz, map_zero]
    exact LpProductTensor.nonnegative_zero _

/-- Every genuine tree Picard stage is a nonnegative function of its ordered leaf labels. -/
theorem ckTreeIterate_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Nonnegative (ckTreeIterate p β d (clampedResponse_continuous h) n t) := by
  induction n generalizing t with
  | zero => exact ckBaseVector_nonnegative h hb ht
  | succ n ih =>
    change Nonnegative (baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t +
      (β * Real.sqrt p) • ∫ u in (0 : ℝ)..max 0 t, clampedResponse d (max 0 t) u •
        graftPower (ckTreeIterate p β d (clampedResponse_continuous h) n u))
    rw [max_eq_right ht]
    apply nonnegative_add (ckBaseVector_nonnegative h hb ht)
    apply nonnegative_smul (mul_nonneg h.beta_pos.le (Real.sqrt_nonneg _))
    apply nonnegative_intervalIntegral ht _
      (treeIterate_integrable (p - 1) (β * Real.sqrt p) (clampedResponse d) (clampedResponse_continuous h) n t 0 t)
    intro u hu
    apply nonnegative_smul
    · rw [clampedResponse_eq hu.1 hu.2]
      exact hb.2 t u hu.1 hu.2
    · exact graftPower_nonnegative (ih hu.1)

/-- Strong convergence and the actual closed function cone prove positivity of the final path. -/
theorem ckTreeState_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    Nonnegative (ckTreeState h t) :=
  (nonnegative_isClosed (p - 1)).mem_of_tendsto (ckTreeIterate_tendsto h hb ht)
    (Filter.Eventually.of_forall (fun n => ckTreeIterate_nonnegative h hb n ht))

theorem heightProjection_nonnegative {m : ℕ} {v : CausalTree.Space m} (hv : Nonnegative v) (j : ℕ) :
    Nonnegative (heightProjection j v) := by
  intro τ
  rw [heightProjection_apply]
  split_ifs
  · exact hv τ
  · rw [map_zero]
    exact LpProductTensor.nonnegative_zero _

/-- Inner products of literal nonnegative tree label functions are nonnegative. -/
theorem inner_nonnegative {m : ℕ} {v w : CausalTree.Space m} (hv : Nonnegative v) (hw : Nonnegative w) :
    0 ≤ inner ℝ v w := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro τ
  rw [← (fiberLabelIsometry τ).inner_map_map, L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hv τ, hw τ] with x hx hy
  change 0 ≤ inner ℝ (fiberLabelIsometry τ (v τ) x) (fiberLabelIsometry τ (w τ) x)
  simpa only [RCLike.inner_apply, conj_trivial] using mul_nonneg hy hx

/-- The same-height CK Gram coefficients are nonnegative, exactly as in Proposition 7.1. -/
theorem ckTreeState_height_gram_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (j : ℕ) :
    0 ≤ inner ℝ (heightProjection j (ckTreeState h t)) (heightProjection j (ckTreeState h s)) :=
  inner_nonnegative (heightProjection_nonnegative (ckTreeState_nonnegative h hb ht) j)
    (heightProjection_nonnegative (ckTreeState_nonnegative h hb hs) j)


/-- Removing the empty tuple factors identifies nested ordered labels with an actual tuple. -/
@[expose] def finiteLabelTupleEquiv : (n : ℕ) → (D : Fin n → LabelDatum) →
    (finiteLabels n D).Label ≃ᵐ (∀ i, (D i).Label)
  | 0, D => (MeasurableEquiv.ofUniqueOfUnique (∀ i : Fin 0, (D i).Label) Unit).symm
  | n + 1, D =>
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (D 0).Label)
        (finiteLabelTupleEquiv n (fun i => D i.succ))).trans
        (MeasurableEquiv.piFinSuccAbove (fun i => (D i).Label) 0).symm

theorem finiteLabelTupleEquiv_measurePreserving (n : ℕ) (D : Fin n → LabelDatum) :
    MeasurePreserving (finiteLabelTupleEquiv n D) (finiteLabels n D).measure
      (Measure.pi (fun i => (D i).measure)) := by
  induction n with
  | zero => exact (measurePreserving_pi_empty (fun i : Fin 0 => (D i).measure)).symm
  | succ n ih =>
    exact (measurePreserving_piFinSuccAbove (fun i => (D i).measure) 0).symm.comp
      ((MeasurePreserving.id (D 0).measure).prod (ih (fun i => D i.succ)))

@[expose, reducible] def tupleLabels (n : ℕ) : LabelDatum :=
  ⟨Fin n → LeafLabel, inferInstance, Measure.pi (fun _ => leafMeasure), inferInstance⟩

/-- Ordered concatenation of leaf labels from two consecutive blocks. -/
@[expose] def appendLabelEquiv (n k : ℕ) :
    ((Fin n → LeafLabel) × (Fin k → LeafLabel)) ≃ᵐ (Fin (n + k) → LeafLabel) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => LeafLabel)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + k) => LeafLabel) finSumFinEquiv)

theorem appendLabelEquiv_measurePreserving (n k : ℕ) :
    MeasurePreserving (appendLabelEquiv n k) ((tupleLabels n).measure.prod (tupleLabels k).measure)
      (tupleLabels (n + k)).measure :=
  (measurePreserving_piCongrLeft (fun _ : Fin (n + k) => leafMeasure) finSumFinEquiv).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin k => leafMeasure))

@[expose] def castLabelEquiv {n k : ℕ} (h : n = k) : (Fin n → LeafLabel) ≃ᵐ (Fin k → LeafLabel) := by
  subst k
  exact MeasurableEquiv.refl _

theorem castLabelEquiv_measurePreserving {n k : ℕ} (h : n = k) :
    MeasurePreserving (castLabelEquiv h) (tupleLabels n).measure (tupleLabels k).measure := by
  subst k
  exact MeasurePreserving.id _

/-- The ordered product of blocks has precisely the consecutive leaf ordering of the manuscript. -/
@[expose] def blockLabelEquiv : (n : ℕ) → (k : Fin n → ℕ) →
    (finiteLabels n (fun i => tupleLabels (k i))).Label ≃ᵐ (Fin (∑ i, k i) → LeafLabel)
  | 0, k => by
      change Unit ≃ᵐ (Fin (∑ i : Fin 0, k i) → LeafLabel)
      exact (MeasurableEquiv.ofUniqueOfUnique (Fin 0 → LeafLabel) Unit).symm.trans
        (castLabelEquiv (by simp))
  | n + 1, k =>
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin (k 0) → LeafLabel))
        (blockLabelEquiv n (fun i => k i.succ))).trans
        ((appendLabelEquiv (k 0) (∑ i : Fin n, k i.succ)).trans
          (castLabelEquiv (Fin.sum_univ_succ k).symm))

theorem blockLabelEquiv_measurePreserving (n : ℕ) (k : Fin n → ℕ) :
    MeasurePreserving (blockLabelEquiv n k) (finiteLabels n (fun i => tupleLabels (k i))).measure
      (tupleLabels (∑ i, k i)).measure := by
  induction n with
  | zero =>
      exact (castLabelEquiv_measurePreserving (by simp : 0 = ∑ i : Fin 0, k i)).comp
        (measurePreserving_pi_empty (fun _ : Fin 0 => leafMeasure)).symm
  | succ n ih =>
      exact (castLabelEquiv_measurePreserving (Fin.sum_univ_succ k).symm).comp
        ((appendLabelEquiv_measurePreserving (k 0) (∑ i : Fin n, k i.succ)).comp
          ((MeasurePreserving.id (tupleLabels (k 0)).measure).prod (ih (fun i => k i.succ))))

/-- Relabeling each factor independently in an actual nested product. -/
@[expose] def finiteLabelsCongr : (n : ℕ) → (D E : Fin n → LabelDatum) →
    (∀ i, (D i).Label ≃ᵐ (E i).Label) → (finiteLabels n D).Label ≃ᵐ (finiteLabels n E).Label
  | 0, _, _, _ => MeasurableEquiv.refl _
  | n + 1, D, E, e => MeasurableEquiv.prodCongr (e 0)
      (finiteLabelsCongr n (fun i => D i.succ) (fun i => E i.succ) (fun i => e i.succ))

theorem finiteLabelsCongr_measurePreserving (n : ℕ) (D E : Fin n → LabelDatum)
    (e : ∀ i, (D i).Label ≃ᵐ (E i).Label)
    (he : ∀ i, MeasurePreserving (e i) (D i).measure (E i).measure) :
    MeasurePreserving (finiteLabelsCongr n D E e) (finiteLabels n D).measure (finiteLabels n E).measure := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih => exact (he 0).prod (ih _ _ _ (fun i => he i.succ))

/-- Exact finite ordered tuple of leaf labels, with no extra labels or symmetry factors. -/
@[expose] def fiberLabelEquiv {m : ℕ} (τ : CausalTree.Tree m) :
    (fiberLabels τ).Label ≃ᵐ (Fin τ.leafCount → LeafLabel) := by
  induction τ with
  | leaf => exact (MeasurableEquiv.piUnique (fun _ : Fin 1 => LeafLabel)).symm
  | graft ts children =>
      exact (finiteLabelsCongr m (fun i => fiberLabels (ts i))
        (fun i => tupleLabels (ts i).leafCount) children).trans
        (blockLabelEquiv m (fun i => (ts i).leafCount))

theorem fiberLabelEquiv_measurePreserving {m : ℕ} (τ : CausalTree.Tree m) :
    MeasurePreserving (fiberLabelEquiv τ) (fiberLabels τ).measure (tupleLabels τ.leafCount).measure := by
  induction τ with
  | leaf => exact (measurePreserving_piUnique (fun _ : Fin 1 => leafMeasure)).symm
  | graft ts children =>
      exact (blockLabelEquiv_measurePreserving m (fun i => (ts i).leafCount)).comp
        (finiteLabelsCongr_measurePreserving m (fun i => fiberLabels (ts i))
          (fun i => tupleLabels (ts i).leafCount) (fun i => fiberLabelEquiv (ts i)) children)

/-- Literal source fiber: an actual L² function on the finite tuple of its ordered leaf labels. -/
@[expose] def orderedLeafLabelIsometry {m : ℕ} (τ : CausalTree.Tree m) :
    (fiber τ).Carrier →ₗᵢ[ℝ] Lp ℝ 2 (tupleLabels τ.leafCount).measure :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fiberLabelEquiv τ).symm
    (fiberLabelEquiv_measurePreserving τ).symm).comp (fiberLabelIsometry τ)

/-- The realized component is nonnegative in exactly the manuscript's ordered leaf-label coordinates. -/
theorem orderedLeafLabel_nonnegative {m : ℕ} {v : CausalTree.Space m} (hv : Nonnegative v)
    (τ : CausalTree.Tree m) : LpProductTensor.Nonnegative (orderedLeafLabelIsometry τ (v τ)) := by
  have he := Lp.coeFn_compMeasurePreserving (fiberLabelIsometry τ (v τ))
    (fiberLabelEquiv_measurePreserving τ).symm
  have hp := (fiberLabelEquiv_measurePreserving τ).symm.quasiMeasurePreserving.ae (hv τ)
  filter_upwards [he, hp] with x hx hp
  change 0 ≤ orderedLeafLabelIsometry τ (v τ) x
  change orderedLeafLabelIsometry τ (v τ) x = fiberLabelIsometry τ (v τ) ((fiberLabelEquiv τ).symm x) at hx
  rw [hx]
  exact hp

/-- Every CK state component is a nonnegative actual function of its ordered leaf labels. -/
theorem ckTreeState_orderedLeaf_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t)
    (τ : CausalTree.Tree (p - 1)) :
    LpProductTensor.Nonnegative (orderedLeafLabelIsometry τ (ckTreeState h t τ)) :=
  orderedLeafLabel_nonnegative (ckTreeState_nonnegative h hb ht) τ


/-- Source Proposition 7.1, bundled for one actual path in the constructed tree space.
The CK equations and physical bounds are the chapter's standing hypotheses. -/
theorem exact_causal_realization {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) :
    ∃ v : ℝ → CausalTree.Space (p - 1),
      ContinuousOn v (Ici 0) ∧
      (∀ t, 0 ≤ t → v t = baseVector (p - 1) (clampedResponse d) (clampedResponse_continuous h) t +
        (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t, d.R t u •
          graftTensor (p - 1) (standardTensorPower (v u))) ∧
      (∀ t s, 0 ≤ t → 0 ≤ s → inner ℝ (v t) (v s) = d.C t s) ∧
      (∀ t, 0 ≤ t → ‖v t‖ = 1) ∧
      (∀ t, 0 ≤ t → timePrefix t (v t) = v t) ∧
      (∀ t, 0 ≤ t → ∀ τ, LpProductTensor.Nonnegative (orderedLeafLabelIsometry τ (v t τ))) ∧
      (∀ t s, 0 ≤ t → 0 ≤ s → ∀ j, 0 ≤ inner ℝ (heightProjection j (v t)) (heightProjection j (v s))) ∧
      (∀ t, 0 ≤ t → treeEnergy p (v t) = energy p β d t) ∧
      (∀ t, 0 ≤ t → d.multiplier t = 1 + (p : ℝ) * β * treeEnergy p (v t)) ∧
      (∀ t, 0 ≤ t → ∀ T, graftTensorAdjoint (p - 1) (timePrefix T (v t)) =
        (β * Real.sqrt p) • ∫ u in (0 : ℝ)..t, d.R t u • standardTensorPower (timePrefix T (v u))) := by
  refine ⟨ckTreeState h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (ckTreeState_clamped_continuous h hb).continuousOn.congr
    intro t ht
    change 0 ≤ t at ht
    dsimp only
    rw [max_eq_right ht]
  · exact fun _ ht => ckTreeState_volterra h hb ht
  · exact fun _ _ ht hs => ckTreeState_gram h hb ht hs
  · exact fun _ ht => ckTreeState_norm h hb ht
  · exact fun _ ht => ckTreeState_timePrefix h hb ht (le_refl _)
  · exact fun _ ht τ => ckTreeState_orderedLeaf_nonnegative h hb ht τ
  · exact fun _ _ ht hs j => ckTreeState_height_gram_nonnegative h hb ht hs j
  · exact fun _ ht => ckTreeState_energy h hb ht
  · exact fun _ ht => ckTreeState_multiplier h hb ht
  · exact fun _ ht T => ckTreeState_prefix_root_frame_original h hb ht T


theorem leafNoise_memLp (f : Lp ℝ 2 leafMeasure) :
    MemLp (fun u : ℝ => f (Sum.inr u)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  exact noiseLabelEmbedding.memLp_map_measure_iff.mp
    ((Lp.memLp f).mono_measure (show (volume.restrict (Ioi (0 : ℝ))).map Sum.inr ≤ leafMeasure from by
      unfold leafMeasure
      exact Measure.le_add_left le_rfl))

/-- The actual inverse of the initial-atom/noise label embedding. -/
@[expose] def leafLabelInverse (f : Lp ℝ 2 leafMeasure) : LeafSpace :=
  WithLp.toLp 2 (f (Sum.inl ()), (leafNoise_memLp f).toLp (fun u => f (Sum.inr u)))

theorem leafLabelInverse_noise_coe (f : Lp ℝ 2 leafMeasure) :
    ((leafLabelInverse f).snd : ℝ → ℝ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u => f (Sum.inr u) :=
  (leafNoise_memLp f).coeFn_toLp

theorem leafLabelFunction_inverse (f : Lp ℝ 2 leafMeasure) :
    leafLabelFunction (leafLabelInverse f) =ᵐ[leafMeasure] f := by
  change ∀ᵐ x ∂leafMeasure, leafLabelFunction (leafLabelInverse f) x = f x
  change ∀ᵐ x ∂((Measure.dirac ()).map (Sum.inl : Unit → LeafLabel) +
    (volume.restrict (Ioi (0 : ℝ))).map (Sum.inr : ℝ → LeafLabel)), leafLabelFunction (leafLabelInverse f) x = f x
  rw [ae_add_measure_iff, initialLabelEmbedding.ae_map_iff, noiseLabelEmbedding.ae_map_iff]
  constructor
  · apply Filter.Eventually.of_forall
    intro u
    cases u
    rfl
  · exact leafLabelInverse_noise_coe f

/-- The leaf space equals the actual initial-atom/noise L² space, including surjectivity. -/
theorem leafLabelIsometry_surjective : Function.Surjective leafLabelIsometry := by
  intro f
  refine ⟨leafLabelInverse f, ?_⟩
  apply Lp.ext
  exact (leafLabelVector_coe (leafLabelInverse f)).trans (leafLabelFunction_inverse f)

@[expose] def leafLabelEquiv : LeafSpace ≃ₗᵢ[ℝ] Lp ℝ 2 leafMeasure :=
  LinearIsometryEquiv.ofSurjective leafLabelIsometry leafLabelIsometry_surjective

end SphericalAging.CausalTreePositivity
