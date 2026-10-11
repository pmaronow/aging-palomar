module

public import SphericalAging.BranchMeasurePreserving
public import SphericalAging.PredictableTensorCanonicalRegeneration

public section

/-! One actual rank branch of tensor disclosure: a fresh query reads its
canonical tensor block and leaves the next Gaussian; a dependent query
retains the entire old Gaussian and reads no block. The full split law
is derived from the actual Householder transformation. -/
noncomputable section
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PredictableTensorRankBranch
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open PredictableTensorDisclosureStep PredictableTensorCanonicalRegeneration BranchMeasurePreserving

theorem actual_rank_branch_law {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (W : Submodule ℝ (Vector N))
    (e : Vector N) (he : e∈Wᗮ) {x : S→Vector N} (hx : Measurable x) :
    MeasurePreserving
      (branchMap {z : S×residualTensorSpace (p:=p) W | x z.1∉W}
        (fun z => (history (p:=p) W e he x z,canonicalRemaining (p:=p) W e he x z)) id)
      (μ.prod (stdGaussian (residualTensorSpace (p:=p) W)))
      ((((μ.restrict {s | x s∉W}).prod (stdGaussian (freshBlock (p:=p) W e))).prod
        (stdGaussian (residualTensorSpace (p:=p) (W⊔ℝ ∙ e)))).map Sum.inl+
        (((μ.restrict {s | x s∈W}).prod (stdGaussian (residualTensorSpace (p:=p) W))).map Sum.inr)) := by
  let B : Set S := {s | x s∉W}
  let A : Set (S×residualTensorSpace (p:=p) W) := {z | x z.1∉W}
  have hB : MeasurableSet B := (W.closed_of_finiteDimensional.measurableSet.preimage hx).compl
  have hA : MeasurableSet A := hB.preimage measurable_fst
  have hAB : A=B×ˢuniv := by ext z;simp [A,B]
  have hAc : Aᶜ=Bᶜ×ˢuniv := by ext z;simp [A,B]
  have hF := canonical_step_preserves_product (p:=p) (μ.restrict B) W e he hx
  have hFresh : MeasurePreserving
      (fun z => (history (p:=p) W e he x z,canonicalRemaining (p:=p) W e he x z))
      ((μ.prod (stdGaussian (residualTensorSpace (p:=p) W))).restrict A)
      (((μ.restrict B).prod (stdGaussian (freshBlock (p:=p) W e))).prod
        (stdGaussian (residualTensorSpace (p:=p) (W⊔ℝ ∙ e)))) := by
    rw [hAB,←Measure.restrict_prod_eq_prod_univ B]
    exact hF
  have hDep : MeasurePreserving id
      ((μ.prod (stdGaussian (residualTensorSpace (p:=p) W))).restrict Aᶜ)
      ((μ.restrict Bᶜ).prod (stdGaussian (residualTensorSpace (p:=p) W))) := by
    rw [hAc,←Measure.restrict_prod_eq_prod_univ Bᶜ]
    exact MeasurePreserving.id _
  have hh := preserves_branch_law (μ.prod (stdGaussian (residualTensorSpace (p:=p) W)))
    A hA _ id _ _ hFresh hDep
  simpa only [A,B,compl_setOf,not_not] using hh

end SphericalAging.PredictableTensorRankBranch
