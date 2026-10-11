module

public import SphericalAging.MainCubicGeometryActualModel
public import SphericalAging.WeightedSlowRatioTheorem

public section

/-! Mathematical content of Remark 14.8. The predicted susceptibility
mass is evaluated algebraically, and the actual cubic model proves its
lower bound even at the transition. The matching upper bound and the
chronological fluctuation--dissipation relation remain open statements;
no convergence or actual FDR identity is asserted here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.RemarkSusceptibilityPrediction
open CKSpecification PlateauAlgebra WeightedSlowRatioTheorem AllTemperatureTheorem
open MainCubicGeometryTheorem MainCubicGeometryActualModel

/-- The total response mass in the stated slow-FDR prediction. -/
@[expose] def predictedMass (p : ℕ) (q : ℝ) : ℝ := (1-q)+slowRatio p q*q

theorem predictedMass_eq {p : ℕ} {q : ℝ} (hq : q≠0) :
    predictedMass p q=((p:ℝ)-1)*(1-q) := by
  unfold predictedMass slowRatio
  field_simp [hq]
  ring

theorem predictedMass_cubic {q : ℝ} (hq : q≠0) :
    predictedMass 3 q=2*(1-q) := by
  rw [predictedMass_eq hq]
  norm_num

/-- The actual-model lower bound matching the scalar prediction, including
beta=beta_d. This theorem supplies no matching upper bound. -/
theorem source14_8_actual_model {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (hsector : transitionBetaSquared 3≤β^2) :
    ∃q : ℝ,q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧
      predictedMass 3 q=2*(1-q) ∧
      ENNReal.ofReal (predictedMass 3 q)≤
        liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop ∧
      (β^2=(4/3:ℝ)→q=1/2) := by
  obtain ⟨q,hq,hhalf,hproducts,hbound,haging,hcross,hend⟩ := source1_3_actual_model h hsector
  have hq0 : q≠0 := ne_of_gt (by linarith : 0<q)
  refine ⟨q,hq,hhalf,predictedMass_cubic hq0,?_,hend⟩
  simpa only [predictedMass_cubic hq0] using hbound

end SphericalAging.RemarkSusceptibilityPrediction
