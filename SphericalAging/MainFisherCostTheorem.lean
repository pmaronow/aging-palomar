module

public import SphericalAging.FisherPassageTheorem
public import SphericalAging.MainCubicGeometryTheorem
public import SphericalAging.StrictSlowRatio

public section

/-! Complete local main Theorem1.4. Its cubic threshold/forgetting inputs
and the strict positive Fisher cost are constructed from preceding selection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.MainFisherCostTheorem
open CKSpecification StationaryMultiplierSelection PlateauAlgebra
  MainCubicGeometryTheorem FisherPassageTheorem StrongBackwardDefect AllTemperatureTheorem

theorem source1_4 {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (hc : ClusterCompactness h) (hβ : transitionBetaSquared 3<β^2)
    {aF : ℝ → ℝ} (ha : FisherMajorant 3 β d aF) :
    ∃q : ℝ,q=largerPlateau 3 β ∧ (1/2:ℝ)<q ∧ Conclusions β q d aF := by
  obtain ⟨ell,q,c,r,T,_H,HI,hf,hroot,hhalf,_hend⟩ := canonical_inputs h hc hβ.le
  have hqd : transitionPlateau 3≤q := by simpa only [cubic_transition_plateau] using hhalf
  have hq : (1/2:ℝ)<q := by
    simpa only [cubic_transition_plateau] using StrictSlowRatio.plateau_strict h.spin_ge_three hqd HI.marginality hβ
  exact ⟨q,hroot,hq,source15_1 HI hq hf ha⟩

end SphericalAging.MainFisherCostTheorem
