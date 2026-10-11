module

public import SphericalAging.SphereOnlyActualMainClosure
public import SphericalAging.MainCubicGeometryActualModel
public import SphericalAging.SphereOnlyActualMainStationaryTailTheorem

public section

/-! Collected five-main-theorem conclusion of the manuscript for the
actual spherical diffusion. The main1.1/main1.2/11.4/source12 closure is
extended by complete cubic1.3/1.4 and all-p stationary-relaxation1.5,
including both transition endpoints. Published field threshold10.1 is
the only supplied upstream mathematical theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal Asymptotics
namespace SphericalAging.SphereOnlyActualFiveMainTheorems
open CKSpecification PlateauAlgebra AllTemperatureTheorem StationaryClusterInputs
open MainCubicGeometryTheorem MainCubicGeometryActualModel StrongBackwardDefect
open SphereOnlyActualMainClosure

@[expose] def CubicGeometryConclusion (β : ℝ) (d : CKData) : Prop :=
    ∃q : ℝ,q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧ PrintedProducts d q ∧
      ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop ∧
      OrderedAging d q ∧ LastCrossings d q ∧ (β^2=(4/3:ℝ)→q=1/2)

@[expose] def CubicFisherCostConclusion (β : ℝ) (d : CKData) : Prop :=
    ∃ (aF : ℝ→ℝ) (q : ℝ),FisherMajorant 3 β d aF ∧
      (∀s,0≤aF s) ∧ (∫s in Ioi 0,aF s)≤β^2/2 ∧
      q=largerPlateau 3 β ∧ (1/2:ℝ)<q ∧ FisherPassageTheorem.Conclusions β q d aF

@[expose] def StationaryTailConclusion {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) : Prop :=
    ∃ (ell q : ℝ) (c r : ℝ→ℝ) (T : ℕ→ℝ),Cluster h T c r ell q ∧
      q=largerPlateau p β ∧
    ∃! a : ℝ,a∈Ioo 0 (1/2) ∧
      CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q ∧
      ∃ Aβ : ℝ,0<Aβ ∧
        (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => Aβ*t^(-a)) ∧
        (∀ n : ℕ,1≤n → (fun t : ℝ => (-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
          (fun t : ℝ => (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
        (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a*Aβ)*t^(-(a+1)))

/-- Every main theorem, with the source's exact spin and temperature
sectors. All fields are proved from the model by the following factory. -/
structure FiveMainClosure {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) : Prop extends Closure β h dim where
  cubic_geometry : p=3→transitionBetaSquared 3≤β^2→CubicGeometryConclusion β d
  cubic_fisher_cost : p=3→transitionBetaSquared 3<β^2→CubicFisherCostConclusion β d
  stationary_tail : transitionBetaSquared p≤β^2→StationaryTailConclusion β h

/-- Complete actual-model main theorem factory. It has no finite-model,
Fisher-density, stationary-limit, forgetting, or relaxation input. -/
theorem actual_five_main_closure {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    FiveMainClosure β h dim := by
  refine {
    toClosure := actual_main_closure β h dim hDim hTop hPub
    cubic_geometry := ?_
    cubic_fisher_cost := ?_
    stationary_tail := ?_
  }
  · intro hp hsector
    have h3 : CKEquations 3 β d := by simpa only [hp] using h
    exact source1_3_actual_model h3 hsector
  · intro hp hsector
    have h3 : CKEquations 3 β d := by simpa only [hp] using h
    exact source1_4_actual_model h3 hsector
  · intro hsector
    exact SphereOnlyActualMainStationaryTailTheorem.actual_source1_5 β h hPub hsector

/-- The physical PSD CK solution, its genuine source3.3 approximation and
all five main theorems are constructed under published field threshold10.1. -/
theorem exists_actual_five_main_closure {p : ℕ} (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃d : CKData,∃h : CKEquations p β d,PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧ FiveMainClosure β h dim := by
  obtain ⟨d,h,hB,hPSD,hbridge⟩ := ActualHardSphereBridge.exists_actual_hard_sphere_bridge hp β hβ
  exact ⟨d,h,hB,hPSD,actual_five_main_closure β h dim hDim hTop hPub⟩

end SphericalAging.SphereOnlyActualFiveMainTheorems
