module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

public section

/-! Concrete ordered-tree Hilbert space from manuscript Section 7.
Every vertex has either zero or exactly `m` ordered children. Each tree carries
an actual completed tensor product of copies of `ℝ ⊕ L²((0,∞),du)`; their `ℓ²`
direct sum is the causal tree Hilbert space. No dynamical or geometric conclusion
is assumed in this construction.
-/

noncomputable section
open scoped TensorProduct InnerProductSpace ENNReal
open MeasureTheory UniformSpace
namespace SphericalAging.CausalTree
attribute [local instance] Classical.propDecidable

/-- Finite rooted ordered full `m`-ary trees. -/
inductive Tree (m : ℕ) : Type
  | leaf : Tree m
  | graft : (Fin m → Tree m) → Tree m

local instance (m : ℕ) : DecidableEq (Tree m) := Classical.decEq _

namespace Tree
variable {m : ℕ}

@[expose] def height : Tree m → ℕ :=
  Tree.rec 0 (fun _ heights => 1 + Finset.univ.sup heights)

@[simp] theorem height_leaf : height (leaf : Tree m) = 0 := rfl
@[simp] theorem height_graft (t : Fin m → Tree m) :
    height (graft t) = 1 + Finset.univ.sup (fun i => height (t i)) := rfl

/-- The leaves in planar order, encoded recursively without identifying distinct trees. -/
@[expose] def leafCount : Tree m → ℕ :=
  Tree.rec 1 (fun _ counts => ∑ i, counts i)

@[simp] theorem leafCount_leaf : leafCount (leaf : Tree m) = 1 := rfl
@[simp] theorem leafCount_graft (t : Fin m → Tree m) :
    leafCount (graft t) = ∑ i, leafCount (t i) := rfl

theorem child_height_lt (t : Fin m → Tree m) (i : Fin m) :
    height (t i) < height (graft t) := by
  have := Finset.le_sup (s := Finset.univ) (f := fun i => height (t i))
    (Finset.mem_univ i)
  simp only [height_graft]
  omega

theorem graft_height_le_iff (t : Fin m → Tree m) (h : ℕ) :
    height (graft t) ≤ h + 1 ↔ ∀ i, height (t i) ≤ h := by
  simp only [height_graft]
  rw [show 1 + Finset.univ.sup (fun i => height (t i)) ≤ h + 1 ↔
      Finset.univ.sup (fun i => height (t i)) ≤ h by omega]
  simp [Finset.sup_le_iff]

theorem height_eq_zero_iff (t : Tree m) : height t = 0 ↔ t = leaf := by
  cases t with
  | leaf => simp
  | graft t => simp [height_graft]

/-- Root decomposition: every non-leaf has a unique ordered tuple of children. -/
@[expose] def rootEquiv : Tree m ≃ Unit ⊕ (Fin m → Tree m) where
  toFun t := match t with | leaf => .inl () | graft ts => .inr ts
  invFun x := match x with | .inl _ => leaf | .inr ts => graft ts
  left_inv t := by cases t <;> rfl
  right_inv x := by cases x with | inl u => cases u; rfl | inr ts => rfl

@[simp] theorem rootEquiv_leaf : rootEquiv (leaf : Tree m) = Sum.inl () := rfl
@[simp] theorem rootEquiv_graft (t : Fin m → Tree m) :
    rootEquiv (graft t) = Sum.inr t := rfl

theorem graft_injective : Function.Injective (@graft m) := fun _ _ h => graft.inj h

end Tree

/-- A complete real Hilbert space, bundled to permit recursion on a tree. -/
structure HilbertDatum where
  Carrier : Type
  group : NormedAddCommGroup Carrier
  inner : @InnerProductSpace ℝ Carrier _ group.toSeminormedAddCommGroup
  complete : @CompleteSpace Carrier group.toUniformSpace
attribute [instance] HilbertDatum.group HilbertDatum.inner HilbertDatum.complete

namespace HilbertDatum

@[expose, reducible] def real : HilbertDatum := ⟨ℝ, inferInstance, inferInstance, inferInstance⟩

/-- The completed, rather than merely algebraic, Hilbert tensor product. -/
@[expose, reducible] def tensor (A B : HilbertDatum) : HilbertDatum :=
  ⟨Completion (A.Carrier ⊗[ℝ] B.Carrier), inferInstance, inferInstance, inferInstance⟩

@[expose] def pure (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) :
    (tensor A B).Carrier := ((x ⊗ₜ[ℝ] y : A.Carrier ⊗[ℝ] B.Carrier) : Completion _)

@[simp] theorem norm_pure (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) :
    ‖pure A B x y‖ = ‖x‖ * ‖y‖ := by
  exact (Completion.norm_coe _).trans (TensorProduct.norm_tmul (𝕜 := ℝ) x y)

@[simp] theorem inner_pure (A B : HilbertDatum)
    (x x' : A.Carrier) (y y' : B.Carrier) :
    Inner.inner ℝ (pure A B x y) (pure A B x' y') = Inner.inner ℝ x x' * Inner.inner ℝ y y' := by
  exact (Completion.inner_coe _ _).trans (TensorProduct.inner_tmul ℝ _ _ _ _)

/-- Ordered finite completed tensor product, with the empty product equal to `ℝ`. -/
@[expose, reducible] def finiteTensor : (n : ℕ) → (Fin n → HilbertDatum) → HilbertDatum
  | 0, _ => real
  | n + 1, A => tensor (A 0) (finiteTensor n (fun i => A i.succ))

@[expose] def finitePure : (n : ℕ) → (A : Fin n → HilbertDatum) →
    ((i : Fin n) → (A i).Carrier) → (finiteTensor n A).Carrier
  | 0, _, _ => (1 : ℝ)
  | n + 1, A, x => pure (A 0) (finiteTensor n (fun i => A i.succ))
      (x 0) (finitePure n (fun i => A i.succ) (fun i => x i.succ))

@[simp] theorem norm_finitePure (n : ℕ) (A : Fin n → HilbertDatum)
    (x : (i : Fin n) → (A i).Carrier) :
    ‖finitePure n A x‖ = ∏ i, ‖x i‖ := by
  induction n with
  | zero => change ‖(1 : ℝ)‖ = 1; norm_num
  | succ n ih =>
      rw [finitePure, norm_pure, ih, Fin.prod_univ_succ]

@[simp] theorem inner_finitePure (n : ℕ) (A : Fin n → HilbertDatum)
    (x y : (i : Fin n) → (A i).Carrier) :
    Inner.inner ℝ (finitePure n A x) (finitePure n A y) = ∏ i, Inner.inner ℝ (x i) (y i) := by
  induction n with
  | zero => change Inner.inner ℝ (1 : ℝ) 1 = 1; norm_num
  | succ n ih =>
      calc
        _ = Inner.inner ℝ (x 0) (y 0) *
            Inner.inner ℝ (finitePure n (fun i => A i.succ) (fun i => x i.succ))
              (finitePure n (fun i => A i.succ) (fun i => y i.succ)) :=
          inner_pure (A 0) (finiteTensor n (fun i => A i.succ)) _ _ _ _
        _ = Inner.inner ℝ (x 0) (y 0) * ∏ i : Fin n, Inner.inner ℝ (x i.succ) (y i.succ) := by
          rw [ih]
        _ = _ := (Fin.prod_univ_succ (fun i : Fin (n + 1) => Inner.inner ℝ (x i) (y i))).symm

end HilbertDatum

/-- Brownian leaf factor, exactly `L²((0,∞),du)`, represented by restriction of Lebesgue measure. -/
@[expose] abbrev NoiseSpace := Lp ℝ 2 (volume.restrict (Set.Ioi (0 : ℝ)))
/-- Distinguished initial direction plus Brownian leaf factor, with the Hilbert product norm. -/
@[expose] abbrev LeafSpace := WithLp 2 (ℝ × NoiseSpace)

@[expose, reducible] def leafDatum : HilbertDatum := ⟨LeafSpace, inferInstance, inferInstance, inferInstance⟩

@[expose] def initialLeaf : LeafSpace := WithLp.toLp 2 (1, 0)

@[simp] theorem norm_initialLeaf : ‖initialLeaf‖ = 1 := by
  have h : ‖initialLeaf‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [initialLeaf]
  nlinarith [norm_nonneg initialLeaf]

/-- The actual completed leaf tensor associated to a particular ordered tree. -/
@[expose, reducible] def fiber {m : ℕ} : Tree m → HilbertDatum :=
  Tree.rec leafDatum (fun _ children => HilbertDatum.finiteTensor m children)

@[simp] theorem fiber_leaf (m : ℕ) : fiber (Tree.leaf : Tree m) = leafDatum := rfl
@[simp] theorem fiber_graft {m : ℕ} (ts : Fin m → Tree m) :
    fiber (Tree.graft ts) = HilbertDatum.finiteTensor m (fun i => fiber (ts i)) := rfl

/-- The full causal-tree Hilbert direct sum. Completeness is supplied by `lp.completeSpace`. -/
@[expose] abbrev Space (m : ℕ) := lp (fun t : Tree m => (fiber t).Carrier) 2

/-- Root-tuple completed tensor summands: the canonical distributed tensor-domain. -/
@[expose] abbrev RootTensorSpace (m : ℕ) :=
  lp (fun ts : Fin m → Tree m => (fiber (Tree.graft ts)).Carrier) 2

/-- The distinguished initial vector lives in the one-leaf tree summand. -/
@[expose] def initialVector (m : ℕ) : Space m := lp.single 2 Tree.leaf initialLeaf

@[simp] theorem norm_initialVector (m : ℕ) : ‖initialVector m‖ = 1 := by
  change ‖lp.single (E := fun t : Tree m => (fiber t).Carrier) 2 Tree.leaf initialLeaf‖ = 1
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact norm_initialLeaf

/-- A coordinate mask is a bounded orthogonal projection on the actual Hilbert sum. -/
@[expose] def mask {m : ℕ} (s : Set (Tree m)) (v : Space m) : Space m :=
  ⟨fun t => if t ∈ s then v t else 0,
    (lp.memℓp v).mono' (fun t => by split_ifs <;> simp)⟩

@[simp] theorem mask_apply {m : ℕ} (s : Set (Tree m)) (v : Space m) (t : Tree m) :
    mask s v t = if t ∈ s then v t else 0 := rfl

@[simp] theorem mask_idempotent {m : ℕ} (s : Set (Tree m)) (v : Space m) :
    mask s (mask s v) = mask s v := by
  ext t
  simp only [mask_apply]
  split_ifs <;> rfl

theorem mask_norm_le {m : ℕ} (s : Set (Tree m)) (v : Space m) :
    ‖mask s v‖ ≤ ‖v‖ :=
  lp.norm_mono (by norm_num) (fun t => by simp only [mask_apply]; split_ifs <;> simp)

@[expose] def heightProjection {m : ℕ} (j : ℕ) : Space m → Space m := mask {t | t.height = j}
@[expose] def heightPrefix {m : ℕ} (j : ℕ) : Space m → Space m := mask {t | t.height ≤ j}

@[simp] theorem heightProjection_apply {m : ℕ} (j : ℕ) (v : Space m) (t : Tree m) :
    heightProjection j v t = if t.height = j then v t else 0 := by
  simp [heightProjection, mask]
@[simp] theorem heightPrefix_apply {m : ℕ} (j : ℕ) (v : Space m) (t : Tree m) :
    heightPrefix j v t = if t.height ≤ j then v t else 0 := by
  simp [heightPrefix, mask]

@[simp] theorem heightPrefix_comp {m : ℕ} (j k : ℕ) (v : Space m) :
    heightPrefix j (heightPrefix k v) = heightPrefix (min j k) v := by
  ext t
  simp only [heightPrefix_apply, le_min_iff]
  split_ifs <;> simp_all

@[simp] theorem heightProjection_idempotent {m : ℕ} (j : ℕ) (v : Space m) :
    heightProjection j (heightProjection j v) = heightProjection j v := mask_idempotent _ _

/-- Parseval's equality in the actual tree Hilbert direct sum. -/
theorem norm_sq_eq_tsum {m : ℕ} (v : Space m) :
    ‖v‖ ^ 2 = ∑' t, ‖v t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  simp only [real_inner_self_eq_norm_sq]

theorem summable_norm_sq {m : ℕ} (v : Space m) :
    Summable (fun t => ‖v t‖ ^ 2) := by
  simpa only [real_inner_self_eq_norm_sq] using lp.summable_inner (𝕜 := ℝ) v v

/-- Ordered root grafting, extended by zero in the one-leaf summand. -/
@[expose] def graft {m : ℕ} (w : RootTensorSpace m) : Space m := by
  let f : (t : Tree m) → (fiber t).Carrier :=
    fun t => match t with | .leaf => 0 | .graft ts => w ts
  refine ⟨f, memℓp_gen ?_⟩
  apply Tree.graft_injective.summable_iff (f := fun t => ‖f t‖ ^ (2 : ℝ≥0∞).toReal) ?_ |>.mp
  · simpa [f, Function.comp_def] using (lp.memℓp w).summable (by norm_num)
  · intro t ht
    cases t with
    | leaf => simp [f]
    | graft ts => exact False.elim (ht ⟨ts, rfl⟩)

@[simp] theorem graft_leaf {m : ℕ} (w : RootTensorSpace m) :
    graft w Tree.leaf = 0 := rfl
@[simp] theorem graft_graft {m : ℕ} (w : RootTensorSpace m) (ts : Fin m → Tree m) :
    graft w (Tree.graft ts) = w ts := rfl

theorem norm_graft {m : ℕ} (w : RootTensorSpace m) : ‖graft w‖ = ‖w‖ := by
  have h : ‖graft w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [norm_sq_eq_tsum, ← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
    simp only [real_inner_self_eq_norm_sq]
    exact (Tree.graft_injective.tsum_eq (f := fun t => ‖graft w t‖ ^ 2) (by
      intro t ht
      cases t with
      | leaf => simp at ht
      | graft ts => exact ⟨ts, rfl⟩)).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The root graft is a genuine linear isometry between complete Hilbert spaces. -/
@[expose] def graftIsometry (m : ℕ) : RootTensorSpace m →ₗᵢ[ℝ] Space m where
  toFun := graft
  map_add' w z := by
    ext t
    cases t <;> simp only [graft_leaf, graft_graft, lp.coeFn_add, Pi.add_apply, zero_add]
  map_smul' c w := by ext t; cases t <;> simp [graft]
  norm_map' := norm_graft

/-- Finite tuple splitting used to verify the complete root tensor-power norm. -/
@[expose] def tupleSuccEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun t := (t 0, fun i => t i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv t := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl

/-- The norm product is summable over every ordered tuple, with its exact total. -/
theorem hasSum_tuple_product {α : Type*} (n : ℕ) (f : α → ℝ)
    (hf : Summable f) (hn : ∀ a, 0 ≤ f a) :
    HasSum (fun t : Fin n → α => ∏ i, f (t i)) ((∑' a, f a) ^ n) := by
  induction n with
  | zero =>
      simpa using (hasSum_fintype (fun _ : Fin 0 → α => (1 : ℝ)))
  | succ n ih =>
      have hp := hf.mul_of_nonneg ih.summable hn (fun t : Fin n → α => Finset.prod_nonneg (fun i _ => hn (t i)))
      have hs := hf.hasSum.mul ih hp
      convert (tupleSuccEquiv α n).hasSum_iff.mpr hs using 1
      · ext t
        simp [tupleSuccEquiv, Fin.prod_univ_succ]
      · rw [pow_succ]; ring

/-- Pure `m`-th tensor power, constructed in the distributed completed tensor-domain. -/
@[expose] def tensorPower {m : ℕ} (v : Space m) : RootTensorSpace m := by
  let f : (ts : Fin m → Tree m) → (fiber (Tree.graft ts)).Carrier :=
    fun ts => HilbertDatum.finitePure m (fun i => fiber (ts i)) (fun i => v (ts i))
  refine ⟨f, memℓp_gen ?_⟩
  have hs := hasSum_tuple_product m (fun t => ‖v t‖ ^ 2) (summable_norm_sq v) (fun _ => sq_nonneg _)
  simpa only [f, HilbertDatum.norm_finitePure, ENNReal.toReal_ofNat,
    Real.rpow_two, ← Finset.prod_pow] using hs.summable

@[simp] theorem tensorPower_apply {m : ℕ} (v : Space m) (ts : Fin m → Tree m) :
    tensorPower v ts = HilbertDatum.finitePure m (fun i => fiber (ts i)) (fun i => v (ts i)) := rfl

@[expose] def graftPower {m : ℕ} (v : Space m) : Space m := graft (tensorPower v)

@[simp] theorem graftPower_leaf {m : ℕ} (v : Space m) : graftPower v Tree.leaf = 0 := rfl
@[simp] theorem graftPower_graft {m : ℕ} (v : Space m) (ts : Fin m → Tree m) :
    graftPower v (Tree.graft ts) =
      HilbertDatum.finitePure m (fun i => fiber (ts i)) (fun i => v (ts i)) := rfl

theorem norm_graftPower_sq {m : ℕ} (v : Space m) : ‖graftPower v‖ ^ 2 = (‖v‖ ^ 2) ^ m := by
  rw [graftPower, norm_graft, ← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  simp only [real_inner_self_eq_norm_sq, tensorPower_apply, HilbertDatum.norm_finitePure,
    ← Finset.prod_pow]
  exact (hasSum_tuple_product m (fun t => ‖v t‖ ^ 2)
    (summable_norm_sq v) (fun _ => sq_nonneg _)).tsum_eq.trans
      (congrArg (fun a => a ^ m) (norm_sq_eq_tsum v).symm)

theorem heightProjection_orthogonal {m : ℕ} (j k : ℕ) (hjk : j ≠ k)
    (v w : Space m) :
    inner ℝ (heightProjection j v) (heightProjection k w) = 0 := by
  rw [lp.inner_eq_tsum]
  rw [show (0 : ℝ) = ∑' t : Tree m, (0 : ℝ) by simp]
  apply tsum_congr
  intro t
  simp only [heightProjection_apply]
  split_ifs with hj hk hk <;> simp_all

theorem heightPrefix_orthogonal_succ {m : ℕ} (j : ℕ) (v w : Space m) :
    inner ℝ (heightPrefix j v) (heightProjection (j + 1) w) = 0 := by
  rw [lp.inner_eq_tsum]
  rw [show (0 : ℝ) = ∑' t : Tree m, (0 : ℝ) by simp]
  apply tsum_congr
  intro t
  simp only [heightPrefix_apply, heightProjection_apply]
  split_ifs with hj hk hk <;> simp_all

theorem heightPrefix_succ {m : ℕ} (j : ℕ) (v : Space m) :
    heightPrefix (j + 1) v = heightPrefix j v + heightProjection (j + 1) v := by
  ext t
  simp only [heightPrefix_apply, heightProjection_apply, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp_all <;> omega

theorem heightPrefix_norm_sq_succ {m : ℕ} (j : ℕ) (v : Space m) :
    ‖heightPrefix (j + 1) v‖ ^ 2 =
      ‖heightPrefix j v‖ ^ 2 + ‖heightProjection (j + 1) v‖ ^ 2 := by
  rw [heightPrefix_succ, norm_add_sq_real, heightPrefix_orthogonal_succ]
  ring

/-- Actual squared height mass, defined from orthogonal tree components. -/
@[expose] def heightMass {m : ℕ} (v : Space m) (j : ℕ) : ℝ := ‖heightProjection j v‖ ^ 2
/-- Cumulative mass over heights strictly below `n`, with empty cumulative mass zero. -/
@[expose] def massBelow {m : ℕ} (v : Space m) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, heightMass v j

@[simp] theorem massBelow_zero {m : ℕ} (v : Space m) : massBelow v 0 = 0 := by
  simp [massBelow]

theorem heightPrefix_norm_sq {m : ℕ} (v : Space m) (n : ℕ) :
    ‖heightPrefix n v‖ ^ 2 = massBelow v (n + 1) := by
  induction n with
  | zero =>
      have he : heightPrefix 0 v = heightProjection 0 v := by
        ext t
        simp [heightPrefix_apply, heightProjection_apply]
      simp [he, massBelow, heightMass]
  | succ n ih =>
      rw [heightPrefix_norm_sq_succ, ih]
      simp [massBelow, heightMass, Finset.sum_range_succ]

/-- The grafted power has no component at height zero (Lemma 9.1). -/
@[simp] theorem graftPower_height_zero {m : ℕ} (v : Space m) :
    heightProjection 0 (graftPower v) = 0 := by
  ext t
  cases t with
  | leaf => simp
  | graft ts => simp [Tree.height_graft]

@[simp] theorem graftPower_prefix_zero {m : ℕ} (v : Space m) :
    heightPrefix 0 (graftPower v) = 0 := by
  ext t
  cases t with
  | leaf => simp
  | graft ts => simp [Tree.height_graft]

/-- Height causality of the actual grafted tensor power (Lemma 9.1). -/
theorem graftPower_height_causal {m : ℕ} (v : Space m) (j : ℕ) :
    heightProjection j (graftPower v) =
      heightProjection j (graftPower (heightPrefix (j - 1) v)) := by
  ext t
  cases t with
  | leaf => simp
  | graft ts =>
      simp only [heightProjection_apply]
      split_ifs with hj
      · simp only [graftPower_graft]
        congr 1
        funext i
        rw [heightPrefix_apply, ite_eq_left]
        have hi := Tree.child_height_lt ts i
        omega
      · rfl

/-- Prefix causality: all root labels are retained iff all child trees are retained. -/
theorem graftPower_heightPrefix {m : ℕ} (v : Space m) (j : ℕ) :
    heightPrefix (j + 1) (graftPower v) = graftPower (heightPrefix j v) := by
  ext t
  cases t with
  | leaf => simp
  | graft ts =>
      simp only [heightPrefix_apply, graftPower_graft]
      split_ifs with hj
      · congr 1
        funext i
        simp only [ite_eq_left ((Tree.graft_height_le_iff ts j).mp hj i)]
      · obtain ⟨i, hi⟩ := not_forall.mp (mt (Tree.graft_height_le_iff ts j).mpr hj)
        symm
        apply norm_eq_zero.mp
        rw [HilbertDatum.norm_finitePure]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [heightPrefix_apply, hi]

/-- Full norm identity of Lemma 9.1, for the constructed Hilbert graft.
`massBelow v j` is manuscript `B_{j-1}`, and `massBelow v (j-1)` is `B_{j-2}`. -/
theorem graftPower_height_norm_sq {m : ℕ} (hm : 0 < m) (v : Space m) (j : ℕ) (hj : 1 ≤ j) :
    ‖heightProjection j (graftPower v)‖ ^ 2 =
      massBelow v j ^ m - massBelow v (j - 1) ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hp := heightPrefix_norm_sq_succ k (graftPower v)
  rw [graftPower_heightPrefix, norm_graftPower_sq, heightPrefix_norm_sq] at hp
  cases k with
  | zero =>
      rw [graftPower_prefix_zero] at hp
      simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hp
      simp only [Nat.succ_eq_add_one, Nat.zero_add, Nat.sub_self, massBelow_zero,
        zero_pow hm.ne', sub_zero]
      linarith
  | succ k =>
      rw [graftPower_heightPrefix, norm_graftPower_sq, heightPrefix_norm_sq] at hp
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      linarith

/-- The complete height-mass distribution, obtained by regrouping actual tree components. -/
theorem hasSum_heightMass {m : ℕ} (v : Space m) : HasSum (heightMass v) (‖v‖ ^ 2) := by
  have hs := (summable_norm_sq v).hasSum.tsum_fiberwise Tree.height
  rw [← norm_sq_eq_tsum] at hs
  convert hs using 1
  funext j
  rw [heightMass, norm_sq_eq_tsum]
  rw [tsum_subtype (Tree.height ⁻¹' {j}) (fun t : Tree m => ‖v t‖ ^ 2)]
  apply tsum_congr
  intro t
  simp only [heightProjection_apply, Set.indicator]
  split_ifs <;> simp_all

/-- The scalar functional is the sum of its actual orthogonal height contributions. -/
theorem inner_eq_tsum_height {m : ℕ} (v w : Space m) :
    inner ℝ v w = ∑' j, inner ℝ (heightProjection j v) (heightProjection j w) := by
  have hs := (lp.summable_inner (𝕜 := ℝ) v w).hasSum.tsum_fiberwise Tree.height
  rw [← lp.inner_eq_tsum] at hs
  symm
  convert hs.tsum_eq using 1
  congr 1
  funext j
  rw [lp.inner_eq_tsum]
  rw [tsum_subtype (Tree.height ⁻¹' {j}) (fun t : Tree m => inner ℝ (v t) (w t))]
  apply tsum_congr
  intro t
  simp only [heightProjection_apply, Set.indicator]
  split_ifs <;> simp_all

/-- Strong convergence of the finite-height projections to the identity. -/
theorem heightPrefix_tendsto {m : ℕ} (v : Space m) :
    Filter.Tendsto (fun n => heightPrefix n v) Filter.atTop (nhds v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Filter.Tendsto (fun n => ‖heightPrefix n v - v‖ ^ 2)
      Filter.atTop (nhds (0 : ℝ)) := by
    simp_rw [norm_sq_eq_tsum]
    convert tendsto_tsum_of_dominated_convergence (summable_norm_sq v)
      (g := fun _ : Tree m => (0 : ℝ)) ?_ ?_ using 1
    · simp
    · intro t
      apply Filter.Tendsto.congr' (Filter.eventually_ge_atTop t.height |>.mono ?_)
        tendsto_const_nhds
      intro n hn
      simp [lp.coeFn_sub, heightPrefix_apply, hn]
    · apply Filter.Eventually.of_forall
      intro n t
      simp only [lp.coeFn_sub, Pi.sub_apply, heightPrefix_apply]
      split_ifs <;> simp
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn

@[simp] theorem heightProjection_add {m : ℕ} (j : ℕ) (v w : Space m) :
    heightProjection j (v + w) = heightProjection j v + heightProjection j w := by
  ext t
  simp only [heightProjection_apply, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp

@[simp] theorem heightProjection_smul {m : ℕ} (j : ℕ) (a : ℝ) (v : Space m) :
    heightProjection j (a • v) = a • heightProjection j v := by
  ext t
  simp only [heightProjection_apply, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp

@[simp] theorem heightProjection_comp {m : ℕ} (j k : ℕ) (v : Space m) :
    heightProjection j (heightProjection k v) = if j = k then heightProjection k v else 0 := by
  ext t
  simp only [heightProjection_apply, lp.coeFn_zero]
  split_ifs <;> simp_all

@[simp] theorem heightPrefix_add {m : ℕ} (j : ℕ) (v w : Space m) :
    heightPrefix j (v + w) = heightPrefix j v + heightPrefix j w := by
  ext t
  simp only [heightPrefix_apply, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp

@[simp] theorem heightPrefix_smul {m : ℕ} (j : ℕ) (a : ℝ) (v : Space m) :
    heightPrefix j (a • v) = a • heightPrefix j v := by
  ext t
  simp only [heightPrefix_apply, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp

@[simp] theorem heightPrefix_projection {m : ℕ} (j k : ℕ) (v : Space m) :
    heightPrefix j (heightProjection k v) = if k ≤ j then heightProjection k v else 0 := by
  ext t
  simp only [heightPrefix_apply, heightProjection_apply, lp.coeFn_zero]
  split_ifs <;> simp_all <;> intro h <;> omega

@[simp] theorem heightProjection_initialVector (m j : ℕ) :
    heightProjection j (initialVector m) = if j = 0 then initialVector m else 0 := by
  by_cases hj : j = 0
  · subst j
    rw [ite_eq_left rfl]
    ext t
    cases t <;> simp [heightProjection_apply, initialVector, lp.single_apply]
  · rw [ite_eq_right hj]
    ext t
    cases t <;> simp [heightProjection_apply, initialVector, lp.single_apply, Ne.symm hj]

/-- Vanishing higher height mass means that the actual vector is its finite prefix. -/
theorem heightPrefix_eq_self {m : ℕ} (v : Space m) (k : ℕ)
    (h : ∀ j, k < j → heightMass v j = 0) : heightPrefix k v = v := by
  ext t
  rw [heightPrefix_apply]
  split_ifs with ht
  · rfl
  · have hz : heightProjection t.height v = 0 := by
      apply norm_eq_zero.mp
      have hh := h t.height (by omega)
      dsimp [heightMass] at hh
      nlinarith [norm_nonneg (heightProjection t.height v)]
    have hv := congrArg (fun w : Space m => w t) hz
    simpa using hv.symm


/-- Restriction to the ordered root tuple, the actual adjoint of root grafting. -/
@[expose] def ungraft {m : ℕ} (v : Space m) : RootTensorSpace m := by
  refine ⟨fun ts => v (Tree.graft ts), memℓp_gen ?_⟩
  simpa only [Function.comp_def] using
    ((lp.memℓp v).summable (by norm_num)).comp_injective Tree.graft_injective

@[simp] theorem ungraft_apply {m : ℕ} (v : Space m) (ts : Fin m → Tree m) :
    ungraft v ts = v (Tree.graft ts) := rfl

@[simp] theorem ungraft_graft {m : ℕ} (w : RootTensorSpace m) : ungraft (graft w) = w := by
  ext ts
  rfl

/-- Grafting after its adjoint removes exactly the complete one-leaf summand. -/
theorem graft_ungraft {m : ℕ} (v : Space m) : graft (ungraft v) = v - heightProjection 0 v := by
  ext t
  cases t with
  | leaf => simp [lp.coeFn_sub, heightProjection_apply]
  | graft ts => simp [lp.coeFn_sub, heightProjection_apply, Tree.height_graft]

theorem graft_ungraft_mask {m : ℕ} (v : Space m) :
    graft (ungraft v) = mask {t | t ≠ Tree.leaf} v := by
  ext t
  cases t <;> simp [mask_apply]

theorem ungraft_norm_le {m : ℕ} (v : Space m) : ‖ungraft v‖ ≤ ‖v‖ := by
  rw [← norm_graft, graft_ungraft_mask]
  exact mask_norm_le _ _

/-- Exact adjoint inner-product identity for the complete distributed tensor-domain. -/
theorem graft_adjoint_identity {m : ℕ} (w : RootTensorSpace m) (v : Space m) :
    inner ℝ (graft w) v = inner ℝ w (ungraft v) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact (Tree.graft_injective.tsum_eq (f := fun t => inner ℝ (graft w t) (v t)) (by
    intro t ht
    cases t with
    | leaf => simp at ht
    | graft ts => exact ⟨ts, rfl⟩)).symm

/-- Root adjoint is a genuine bounded linear map. -/
@[expose] def ungraftL (m : ℕ) : Space m →L[ℝ] RootTensorSpace m :=
  ({ toFun := ungraft,
     map_add' := by intro v w; ext ts; rfl,
     map_smul' := by intro a v; ext ts; rfl } : Space m →ₗ[ℝ] RootTensorSpace m).mkContinuous
    1 (fun v => by simpa using ungraft_norm_le v)

end SphericalAging.CausalTree
