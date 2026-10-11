module

public import SphericalAging.CausalTreeRealization
public import SphericalAging.CKPhysicalConsequences

public section

/-! Explicit low-height components of the cubic ordered-tree realization
(Example 7.2). CausalTree.Tree coordinates are the actual completed tensor summands. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace NNReal ENNReal
namespace SphericalAging.ExampleFirstHeights
open CKSpecification CausalTree CausalTreeRealization GreenCovariance CKPhysicalConsequences
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
local instance (m : ℕ) : DecidableEq (CausalTree.Tree m) := Classical.decEq _

/-- The ordered binary fork does not identify left and right children. -/
@[expose, reducible] def binaryFork (l r : CausalTree.Tree 2) : CausalTree.Tree 2 := CausalTree.Tree.graft (fun i=>if i=0 then l else r)
@[expose] def firstFork : CausalTree.Tree 2 := binaryFork CausalTree.Tree.leaf CausalTree.Tree.leaf

theorem firstFork_height : firstFork.height=1 := by
  simp [firstFork,binaryFork,CausalTree.Tree.height_graft]

theorem height_le_one_cases (τ : CausalTree.Tree 2) (hτ : τ.height≤1) :
    τ=CausalTree.Tree.leaf ∨ τ=firstFork := by
  cases τ with
  | leaf => exact Or.inl rfl
  | graft ts =>
    right
    have hc (i : Fin 2) : ts i=CausalTree.Tree.leaf :=
      (CausalTree.Tree.height_eq_zero_iff _).mp (by have := CausalTree.Tree.child_height_lt ts i;omega)
    congr 1
    funext i
    fin_cases i <;> simp [hc]

/-- Precisely the three ordered binary trees of height two. -/
theorem height_two_cases (τ : CausalTree.Tree 2) (hτ : τ.height=2) :
    τ=binaryFork firstFork CausalTree.Tree.leaf ∨
    τ=binaryFork CausalTree.Tree.leaf firstFork ∨ τ=binaryFork firstFork firstFork := by
  cases τ with
  | leaf => simp at hτ
  | graft ts =>
    have hc (i : Fin 2) : (ts i).height≤1 := by
      have := CausalTree.Tree.child_height_lt ts i
      omega
    have he : ts=(fun i=>if i=0 then ts 0 else ts 1) := by ext i;fin_cases i <;> simp
    rcases height_le_one_cases (ts 0) (hc 0) with h0|h0 <;>
      rcases height_le_one_cases (ts 1) (hc 1) with h1|h1
    · rw [h0,h1] at he
      rw [he] at hτ
      change firstFork.height=2 at hτ
      rw [firstFork_height] at hτ
      norm_num at hτ
    · right;left
      rw [h0,h1] at he
      exact congrArg CausalTree.Tree.graft he
    · left
      rw [h0,h1] at he
      exact congrArg CausalTree.Tree.graft he
    · right;right
      rw [h0,h1] at he
      exact congrArg CausalTree.Tree.graft he

/-- An explicit ordered two-factor pure tensor in the recursive completion. -/
@[expose] def pairPure (l r : CausalTree.Tree 2) (x : (fiber l).Carrier) (y : (fiber r).Carrier) :
    (fiber (binaryFork l r)).Carrier :=
  HilbertDatum.pure (fiber l) (HilbertDatum.tensor (fiber r) HilbertDatum.real) x
    (HilbertDatum.pure (fiber r) HilbertDatum.real y 1)

/-- Evaluation of the genuine CK Volterra identity on an individual fork. -/
theorem graft_component {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0≤t)
    (ts : Fin (p-1)→CausalTree.Tree (p-1)) :
    ckTreeState h t (CausalTree.Tree.graft ts)=(β*Real.sqrt p) •
      ∫u in (0:ℝ)..t,d.R t u • HilbertDatum.finitePure (p-1)
        (fun i=>fiber (ts i)) (fun i=>ckTreeState h u (ts i)) := by
  let L := lp.evalCLM ℝ (fun τ : CausalTree.Tree (p-1)=>(fiber τ).Carrier) 2 (CausalTree.Tree.graft ts)
  have he := congrArg L (ckTreeState_volterra_clamped h hb ht)
  rw [map_add,map_smul,←L.intervalIntegral_comp_comm (ckTreeState_integrable h hb ht)] at he
  change ckTreeState h t (CausalTree.Tree.graft ts)=
    baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t (CausalTree.Tree.graft ts)+
      (β*Real.sqrt p) • ∫u in (0:ℝ)..t,
        L (clampedResponse d t u • graftPower (ckTreeState h u)) at he
  have hz : baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t (CausalTree.Tree.graft ts)=0 :=
    lp.single_apply_ne _ _ _ (by simp)
  rw [hz,zero_add] at he
  refine he.trans (congrArg (fun z=>(β*Real.sqrt p) • z) ?_)
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  change (clampedResponse d t u • graftPower (ckTreeState h u)) (CausalTree.Tree.graft ts)=_
  simp only [lp.coeFn_smul,Pi.smul_apply,graftPower_graft,clampedResponse_eq hu.1 hu.2]

/-- Literal left/right component form of the cubic fork recurrence. -/
theorem binaryFork_component {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0≤t) (l r : CausalTree.Tree 2) :
    ckTreeState h t (binaryFork l r)=(β*Real.sqrt 3) •
      ∫u in (0:ℝ)..t,d.R t u • pairPure l r (ckTreeState h u l) (ckTreeState h u r) := by
  have he := graft_component h (physical_bounds_of_equations h) ht (fun i : Fin 2=>if i=0 then l else r)
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at he
  exact he

/-- The leaf coordinate is exactly the manuscript's initial-plus-noise feature. -/
theorem leaf_component {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0≤t) :
    ckTreeState h t CausalTree.Tree.leaf=
      leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) t := by
  have he := congrArg (fun v : Space (p-1)=>v CausalTree.Tree.leaf) (ckTreeState_heightPrefix h hb ht 0)
  simpa only [heightPrefix_apply,CausalTree.Tree.height_leaf,le_refl,if_true,ckTreeIterate,
    treeIterate,baseVector,lp.single_apply_self] using he

/-- Cubic first-fork component in its actual completed two-leaf tensor space. -/
theorem firstFork_component {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0≤t) :
    ckTreeState h t firstFork=(β*Real.sqrt 3) •
      ∫u in (0:ℝ)..t,d.R t u • pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u)
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u) := by
  have he := binaryFork_component h ht CausalTree.Tree.leaf CausalTree.Tree.leaf
  refine he.trans (congrArg (fun z=>(β*Real.sqrt 3) • z) ?_)
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [leaf_component h (physical_bounds_of_equations h) hu.1]

/-- The same leaf vector with its bundled tree-coordinate type retained. -/
@[expose] def leafCoordinateFeature {β : ℝ} {d : CKData} (h : CKEquations 3 β d) (u : ℝ) :
    (fiber (CausalTree.Tree.leaf : CausalTree.Tree 2)).Carrier :=
  ckTreeState h u CausalTree.Tree.leaf

theorem leaf_component_feature {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {u : ℝ} : ckTreeState h u CausalTree.Tree.leaf=leafCoordinateFeature h u := rfl

section HeightTwo
set_option allowUnsafeReducibility true
attribute [local irreducible] fiber

/-- The three height-two components, with the source's three tensor integrands. -/
theorem height_two_components {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0≤t) :
    ckTreeState h t (binaryFork firstFork CausalTree.Tree.leaf)=(β*Real.sqrt 3) •
      (∫u in (0:ℝ)..t,d.R t u • pairPure firstFork CausalTree.Tree.leaf
        (ckTreeState h u firstFork)
        (leafCoordinateFeature h u)) ∧
    ckTreeState h t (binaryFork CausalTree.Tree.leaf firstFork)=(β*Real.sqrt 3) •
      (∫u in (0:ℝ)..t,d.R t u • pairPure CausalTree.Tree.leaf firstFork
        (leafCoordinateFeature h u)
        (ckTreeState h u firstFork)) ∧
    ckTreeState h t (binaryFork firstFork firstFork)=(β*Real.sqrt 3) •
      (∫u in (0:ℝ)..t,d.R t u • pairPure firstFork firstFork
        (ckTreeState h u firstFork) (ckTreeState h u firstFork)) := by
  with_unfolding_all
    exact ⟨binaryFork_component h ht firstFork CausalTree.Tree.leaf,
      binaryFork_component h ht CausalTree.Tree.leaf firstFork,
      binaryFork_component h ht firstFork firstFork⟩

end HeightTwo

/-- The prefix projection acts on the leaf labels of each summand. -/
theorem prefix_component (T : ℝ) (v : Space 2) (τ : CausalTree.Tree 2) :
    timePrefix T v τ=fiberPrefix T τ (v τ) := rfl

/-- The complete first-height truncation is the first genuine Green Picard stage. -/
theorem height_one_Picard {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0≤t) :
    heightPrefix 1 (ckTreeState h t)=
      baseVector 2 (clampedResponse d) (clampedResponse_continuous h) t+
        (β*Real.sqrt 3) • ∫u in (0:ℝ)..t,d.R t u •
          graftPower (baseVector 2 (clampedResponse d) (clampedResponse_continuous h) u) := by
  rw [ckTreeState_heightPrefix h (physical_bounds_of_equations h) ht]
  simp only [ckTreeIterate,treeIterate,max_eq_right ht]
  congr 2
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [clampedResponse_eq hu.1 hu.2]

/-- Exactly the displayed first Picard Gram kernel, in the cubic normalization. -/
theorem height_one_Gram {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t s : ℝ} (ht : 0≤t) (hs : 0≤s) :
    inner ℝ (heightPrefix 1 (ckTreeState h t)) (heightPrefix 1 (ckTreeState h s))=
      CovarianceIteration.baseCovariance d t s+3*β^2*
        ∫u in (0:ℝ)..t,∫v in (0:ℝ)..s,
          d.R t u*d.R s v*(CovarianceIteration.baseCovariance d u v)^2 := by
  rw [ckTreeState_heightPrefix h (physical_bounds_of_equations h) ht,
    ckTreeState_heightPrefix h (physical_bounds_of_equations h) hs,ckTreeIterate_gram 3 β d _ 1 ht hs]
  simp only [CovarianceIteration.covarianceIterate,CovarianceIteration.covarianceMap,
    CovarianceIteration.coloredCovariance]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub]
  rw [show β^2*(3:ℝ)=3*β^2 by ring]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hs] at hv
  dsimp only
  rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2]

end SphericalAging.ExampleFirstHeights
