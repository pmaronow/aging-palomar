module

public import SphericalAging.ExampleFirstForkNoiseProjection

public section

/-! The canonical two-noise projection commutes with the actual
first-fork Volterra integral, with integrability derived from the true leaf curve. -/
noncomputable section
open Set MeasureTheory UniformSpace
open scoped TensorProduct
namespace SphericalAging.ExampleFirstForkIntegralProjection
open CausalTree CKSpecification CausalTreeRealization ExampleFirstHeights GreenCovariance
open ExampleFirstForkNoiseProjection HilbertL2ExternalProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

theorem pairPure_curve_continuous {η : ℝ → LeafSpace} (hη : Continuous η) :
    Continuous (fun u => pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf (η u) (η u)) := by
  have he : (fun u => pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf (η u) (η u)) =
      fun u => removeUnit.symm ((η u ⊗ₜ[ℝ] η u : LeafSpace ⊗[ℝ] LeafSpace) : Completion _) := by
    funext u
    rw [← removeUnit_pairPure, LinearIsometryEquiv.symm_apply_apply]
  rw [he]
  have htm : Continuous (fun u => (η u ⊗ₜ[ℝ] η u : LeafSpace ⊗[ℝ] LeafSpace)) :=
    TensorProduct.continuous_tmul.comp (hη.prodMk hη)
  have hcoe : Continuous (fun u =>
      ((η u ⊗ₜ[ℝ] η u : LeafSpace ⊗[ℝ] LeafSpace) :
        Completion (LeafSpace ⊗[ℝ] LeafSpace))) :=
    (Completion.toComplL : (LeafSpace ⊗[ℝ] LeafSpace) →L[ℝ]
      Completion (LeafSpace ⊗[ℝ] LeafSpace)).continuous.comp htm
  exact removeUnit.symm.continuous.comp
    hcoe

theorem firstFork_integrable {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => d.R t u •
      pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u)
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u)) volume 0 t := by
  have hcoeff : Continuous (fun u => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hc := hcoeff.smul
      (pairPure_curve_continuous (leafResponseFeature_continuous
        (clampedResponse d) (clampedResponse_continuous h)))
  apply (hc.intervalIntegrable 0 t).congr
  intro u hu
  rw [uIoc_of_le ht] at hu
  change clampedResponse d t u •
      pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u)
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u) = _
  rw [clampedResponse_eq hu.1.le hu.2]

theorem projected_curve_integrable {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => d.R t u •
      product noiseMeasure noiseMeasure
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u).snd
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u).snd) volume 0 t := by
  have hj := firstFork_integrable h ht
  have hi : IntervalIntegrable (fun u => noiseProjection (d.R t u •
      pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u)
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u))) volume 0 t :=
    ⟨noiseProjection.integrable_comp hj.1, noiseProjection.integrable_comp hj.2⟩
  simpa only [map_smul, noiseProjection_pairPure] using hi

/-- The actual first-fork completed tensor has the actual projected leaf-product integral. -/
theorem noiseProjection_firstFork {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    noiseProjection (ckTreeState h t firstFork) = (β * Real.sqrt 3) •
      ∫ u in (0:ℝ)..t, d.R t u •
        product noiseMeasure noiseMeasure
          (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u).snd
          (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u).snd := by
  rw [firstFork_component h ht, map_smul,
    ← noiseProjection.intervalIntegral_comp_comm (firstFork_integrable h ht)]
  simp only [map_smul, noiseProjection_pairPure]

end SphericalAging.ExampleFirstForkIntegralProjection
