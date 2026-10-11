module

public import SphericalAging.ActualSphereCKFisherClosure
public import SphericalAging.MainCubicGeometryTheorem
public import SphericalAging.MainFisherCostTheorem

public section

/-! Complete printed cubic product theorem and strict Fisher cost for the
actual spherical model. Stationary compactness and the Fisher majorant
are constructed; no density, PDE or finite-model limit premise remains. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.MainCubicGeometryActualModel
open CKSpecification PlateauAlgebra AllTemperatureTheorem MainCubicGeometryTheorem MainFisherCostTheorem
open ActualSphereCKFisherClosure StrongBackwardDefect
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

/-- All printed cubic product, susceptibility, aging and crossing clauses,
including the transition endpoint, with genuine actual-model inputs. -/
theorem source1_3_actual_model {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (hsector : transitionBetaSquared 3≤β^2) :
    ∃q : ℝ,q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧ PrintedProducts d q ∧
      ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop ∧
      OrderedAging d q ∧ LastCrossings d q ∧ (β^2=(4/3:ℝ)→q=1/2) := by
  obtain ⟨hc,aF,ha,_,_⟩ := actual_stationary_compactness_and_Fisher h
  exact source1_3_with_ordered_aging_and_last_crossings h hc hsector ⟨aF,ha⟩

/-- The actual model supplies the Fisher clock used in the strict
supercritical cubic Fisher-cost theorem. -/
theorem source1_4_actual_model {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (hsector : transitionBetaSquared 3<β^2) :
    ∃ (aF : ℝ→ℝ) (q : ℝ),FisherMajorant 3 β d aF ∧
      (∀s,0≤aF s) ∧ (∫s in Ioi 0,aF s)≤β^2/2 ∧
      q=largerPlateau 3 β ∧ (1/2:ℝ)<q ∧ FisherPassageTheorem.Conclusions β q d aF := by
  obtain ⟨hc,aF,ha,han,hmass⟩ := actual_stationary_compactness_and_Fisher h
  obtain ⟨q,hq,hhalf,hcost⟩ := MainFisherCostTheorem.source1_4 h hc hsector ha
  exact ⟨aF,q,ha,han,hmass,hq,hhalf,hcost⟩

end SphericalAging.MainCubicGeometryActualModel
