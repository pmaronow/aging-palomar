module

public import SphericalAging.ExampleFirstForkLiteralKernel
public import SphericalAging.HilbertTensorContraction

public section

/-! The initial label is an actual bounded coordinate of the leaf
space. Its coefficient is R(u,0), and its contractions of the genuine
first-fork tensor follow the same Volterra integral. -/
noncomputable section
open Set MeasureTheory UniformSpace
open scoped InnerProductSpace TensorProduct
namespace SphericalAging.ExampleFirstForkInitialLabels
open CausalTree CKSpecification CausalTreeRealization GreenCovariance ExampleFirstHeights
open ExampleFirstForkNoiseProjection ExampleFirstForkIntegralProjection
open ExampleFirstForkLiteralKernel HilbertTensorContraction
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem initial_inner_leaf (x : LeafSpace) : ⟪initialLeaf,x⟫_ℝ = x.fst := by
  simp [initialLeaf, WithLp.prod_inner_apply, RCLike.inner_apply]

theorem leaf_initial_coefficient (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) {u : ℝ} (hu : 0 ≤ u) :
    (leafResponseFeature r hr u).fst = r u 0 := by
  change r (max 0 u) 0 = r u 0
  rw [max_eq_right hu]

/-- Contract the actual left initial label and retain the right leaf. -/
@[expose] def initialLeft : (fiber firstFork).Carrier →L[ℝ] LeafSpace :=
  (HilbertDatum.tensorRid leafDatum).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (contractLeft leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real) initialLeaf)

theorem initialLeft_pairPure (x y : LeafSpace) :
    initialLeft (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y) = x.fst • y := by
  change HilbertDatum.tensorRid leafDatum
    (contractLeft leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real) initialLeaf
      (HilbertDatum.pure leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real) x
        (HilbertDatum.pure leafDatum HilbertDatum.real y 1))) = _
  rw [contractLeft_pure, map_smul, HilbertDatum.tensorRid_pure, one_smul, initial_inner_leaf]

@[expose] def twoInitial : (fiber firstFork).Carrier →L[ℝ] ℝ :=
  (innerSL ℝ initialLeaf).comp initialLeft

theorem twoInitial_pairPure (x y : LeafSpace) :
    twoInitial (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y) = x.fst * y.fst := by
  change ⟪initialLeaf,initialLeft (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y)⟫_ℝ = _
  rw [initialLeft_pairPure, real_inner_smul_right, initial_inner_leaf]

/-- The two-star coefficient of the actual first-fork tensor. -/
theorem source7_2_two_initial {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    twoInitial (ckTreeState h t firstFork) =
      β * Real.sqrt 3 * ∫ u in (0:ℝ)..t, d.R t u * d.R u 0 * d.R u 0 := by
  rw [firstFork_component h ht, map_smul,
    ← twoInitial.intervalIntegral_comp_comm (firstFork_integrable h ht)]
  simp only [smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [map_smul,twoInitial_pairPure,leaf_initial_coefficient _ _ hu.1,
    clampedResponse_eq (le_refl 0) hu.1]
  simp only [smul_eq_mul]
  ring

/-- A star label replaces exactly one noise leaf coefficient by R(u,0). -/
theorem source7_2_initial_left {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    initialLeft (ckTreeState h t firstFork) = (β * Real.sqrt 3) •
      ∫ u in (0:ℝ)..t, (d.R t u * d.R u 0) •
        leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u := by
  rw [firstFork_component h ht, map_smul,
    ← initialLeft.intervalIntegral_comp_comm (firstFork_integrable h ht)]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [map_smul, initialLeft_pairPure, leaf_initial_coefficient _ _ hu.1,
    clampedResponse_eq (le_refl 0) hu.1, smul_smul]

end SphericalAging.ExampleFirstForkInitialLabels
