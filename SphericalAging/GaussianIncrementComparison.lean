module

public import SphericalAging.GaussianCompactComparison

public section

/-! Actual compact Gaussian increment comparison, with independent coordinate
blocks constructed internally. No independence or comparison conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianIncrementComparison
open Set MeasureTheory ProbabilityTheory GaussianComparison
open scoped BigOperators
variable {I κ η : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype κ] [Fintype η] [Nonempty η]

 theorem coordinate_left_measurePreserving :
    MeasurePreserving (fun z : (κ⊕η)→ℝ => fun k => z (Sum.inl k))
      (gaussianCoordinates (κ⊕η)) (gaussianCoordinates κ) := by
  have h := measurePreserving_sumPiEquivProdPi (fun _ : κ⊕η => gaussianReal 0 1)
  have hp : MeasurePreserving (Prod.fst : (κ→ℝ)×(η→ℝ)→(κ→ℝ))
      ((gaussianCoordinates κ).prod (gaussianCoordinates η)) (gaussianCoordinates κ) :=
    ⟨measurable_fst,by simp⟩
  exact hp.comp h

 theorem coordinate_right_measurePreserving :
    MeasurePreserving (fun z : (κ⊕η)→ℝ => fun k => z (Sum.inr k))
      (gaussianCoordinates (κ⊕η)) (gaussianCoordinates η) := by
  have h := measurePreserving_sumPiEquivProdPi (fun _ : κ⊕η => gaussianReal 0 1)
  have hp : MeasurePreserving (Prod.snd : (κ→ℝ)×(η→ℝ)→(η→ℝ))
      ((gaussianCoordinates κ).prod (gaussianCoordinates η)) (gaussianCoordinates η) :=
    ⟨measurable_snd,by simp⟩
  exact hp.comp h

 theorem compact_supremum_le {m : I→ℝ} {a : I→κ→ℝ} {b : I→η→ℝ}
    (hm : Continuous m) (ha : Continuous a) (hb : Continuous b)
    (hinc : ∀ i j, (∑k,(a i k-a j k)^2)≤∑k,(b i k-b j k)^2) :
    (∫z,gaussianSup m a z ∂gaussianCoordinates κ)≤
      ∫z,gaussianSup m b z ∂gaussianCoordinates η := by
  let A : I→(κ⊕η)→ℝ := fun i k => Sum.elim (a i) (fun _ => 0) k
  let B : I→(κ⊕η)→ℝ := fun i k => Sum.elim (fun _ => 0) (b i) k
  have hA : Continuous A := by
    apply continuous_pi
    intro k
    cases k with
    | inl k => exact (continuous_apply k).comp ha
    | inr k => exact continuous_const
  have hB : Continuous B := by
    apply continuous_pi
    intro k
    cases k with
    | inl k => exact continuous_const
    | inr k => exact (continuous_apply k).comp hb
  have hc := gaussianSup_comparison hm hB hA
    (fun i j => by simp [A,B,Fintype.sum_sum_type])
    (fun i j => by simpa [A,B,Fintype.sum_sum_type] using hinc i j)
  have hleft (z : (κ⊕η)→ℝ) : gaussianSup m A z=gaussianSup m a (fun k => z (Sum.inl k)) := by
    unfold gaussianSup gaussianAffine
    congr 1
    funext i
    simp [A,Fintype.sum_sum_type]
  have hright (z : (κ⊕η)→ℝ) : gaussianSup m B z=gaussianSup m b (fun k => z (Sum.inr k)) := by
    unfold gaussianSup gaussianAffine
    congr 1
    funext i
    simp [B,Fintype.sum_sum_type]
  simp_rw [hleft,hright] at hc
  have hpl := coordinate_left_measurePreserving (κ:=κ) (η:=η)
  have hpr := coordinate_right_measurePreserving (κ:=κ) (η:=η)
  have hll : HasLaw (fun z : (κ⊕η)→ℝ => fun k => z (Sum.inl k))
      (gaussianCoordinates κ) (gaussianCoordinates (κ⊕η)) := ⟨hpl.measurable.aemeasurable,hpl.map_eq⟩
  have hrr : HasLaw (fun z : (κ⊕η)→ℝ => fun k => z (Sum.inr k))
      (gaussianCoordinates η) (gaussianCoordinates (κ⊕η)) := ⟨hpr.measurable.aemeasurable,hpr.map_eq⟩
  have hl := hll.integral_comp (continuous_gaussianSup hm ha).aestronglyMeasurable
  have hr := hrr.integral_comp (continuous_gaussianSup hm hb).aestronglyMeasurable
  change (∫z,gaussianSup m a (fun k => z (Sum.inl k)) ∂gaussianCoordinates (κ⊕η))=
    (∫z,gaussianSup m a z ∂gaussianCoordinates κ) at hl
  change (∫z,gaussianSup m b (fun k => z (Sum.inr k)) ∂gaussianCoordinates (κ⊕η))=
    (∫z,gaussianSup m b z ∂gaussianCoordinates η) at hr
  rw [hl,hr] at hc
  exact hc

end SphericalAging.GaussianIncrementComparison
