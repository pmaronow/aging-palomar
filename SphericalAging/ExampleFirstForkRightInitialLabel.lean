module

public import SphericalAging.ExampleFirstForkInitialLabels

public section

/-! The ordered right initial label of the actual first cubic fork. -/
noncomputable section
open Set MeasureTheory UniformSpace
open scoped InnerProductSpace TensorProduct
namespace SphericalAging.ExampleFirstForkRightInitialLabel
open CausalTree CKSpecification CausalTreeRealization GreenCovariance ExampleFirstHeights
open ExampleFirstForkNoiseProjection ExampleFirstForkIntegralProjection
open ExampleFirstForkInitialLabels HilbertTensorContraction
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

@[expose] def swapLeaves : Completion (LeafSpace ⊗[ℝ] LeafSpace) ≃ₗᵢ[ℝ]
    Completion (LeafSpace ⊗[ℝ] LeafSpace) :=
  HilbertDatum.completionCongr (TensorProduct.commIsometry ℝ LeafSpace LeafSpace)

@[expose] def initialRight : (fiber firstFork).Carrier →L[ℝ] LeafSpace :=
  (contractLeft leafDatum leafDatum initialLeaf).comp
    (swapLeaves.toContinuousLinearEquiv.toContinuousLinearMap.comp
      removeUnit.toContinuousLinearEquiv.toContinuousLinearMap)

theorem initialRight_pairPure (x y : LeafSpace) :
    initialRight (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y) = y.fst • x := by
  change contractLeft leafDatum leafDatum initialLeaf
    (swapLeaves (removeUnit (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y))) = _
  rw [removeUnit_pairPure, swapLeaves, HilbertDatum.completionCongr_coe,
    TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]
  change contractLeft leafDatum leafDatum initialLeaf (HilbertDatum.pure leafDatum leafDatum y x) = _
  rw [contractLeft_pure, initial_inner_leaf]

/-- A right star label replaces the right noise coefficient by R(u,0). -/
theorem source7_2_initial_right {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    initialRight (ckTreeState h t firstFork) = (β * Real.sqrt 3) •
      ∫ u in (0:ℝ)..t, (d.R t u * d.R u 0) •
        leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u := by
  rw [firstFork_component h ht, map_smul,
    ← initialRight.intervalIntegral_comp_comm (firstFork_integrable h ht)]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [map_smul, initialRight_pairPure, leaf_initial_coefficient _ _ hu.1,
    clampedResponse_eq (le_refl 0) hu.1, smul_smul]

end SphericalAging.ExampleFirstForkRightInitialLabel
