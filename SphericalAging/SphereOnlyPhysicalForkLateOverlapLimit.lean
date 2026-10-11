module

public import SphericalAging.SphereOnlyPhysicalForkOverlapLaw
public import SphericalAging.SphereOnlyPhysicalForkCenterConcentration
public import SphericalAging.SphereOnlyPhysicalForkNormalizationLimits
public import SphericalAging.SphereOnlyPhysicalForkNormTheorem
public import SphericalAging.SphereOnlyPhysicalForkOverlapAggregation
public import SphericalAging.ForkOverlapSupLimit
public import SphericalAging.PhysicalForkLateOverlapLimit
public import SphericalAging.ActualSphereOnlyForkUniformL2

public section

/-! Literal source10.4 Step4 window supremum, dimension limsup, then
stationary-time limit, for the actual finite-fork mean and branch. -/

noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyPhysicalForkLateOverlapLimit
open PhysicalForkOverlapLaw PhysicalForkCenterConcentration PhysicalForkNormalizationLimits PhysicalForkNormTheorem PhysicalForkOverlapAggregation PhysicalForkLateOverlapLimit
open PhysicalForkLateOverlapLimit
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open PhysicalForkConstruction SphereOnlyPhysicalForkOverlapAggregation WienerForkTransfer ForkParameterBounds
open AnnealedHamiltonianEnergyStein CKSpecification StationaryClusterInputs ActualForkMeanBridge
open SphereFisherHelly ActualSphereForkEndpoints
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators

/-- Exact printed source10.4 Step4: the complete closed-window
supremum, dimension limsup first, then stationary-cluster time. -/
theorem actual_late_overlap_concentration {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) (b : Fin K) :
    Tendsto (fun n => limsup (fun j => sSup
      ((lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b) ''Icc (0:ℝ) L)) atTop)
      atTop (𝓝 0) := by
  have hh : Tendsto (fun n => limsup (fun j => ForkOverlapSupLimit.windowSup
      (fun n j (z : ℝ×ℝ) => lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b z.1)
        L n j) atTop) atTop (𝓝 0) := by
    apply ForkOverlapSupLimit.ordered_uniform_limsup (M:=8) L.coe_nonneg
    · intro n j z hz
      exact (lateOverlapError_bounds (by have hx:=hDim j;omega) hK β (T n).toNNReal L H.profile b hz.1).1
    · intro n j z hz
      exact (lateOverlapError_bounds (by have hx:=hDim j;omega) hK β (T n).toNNReal L H.profile b hz.1).2
    · intro ε hε
      have hu := SphereOnlyPhysicalForkOverlapAggregation.actual_late_overlap_ordered_uniform H hT dim hDim hTop hbridge hi hn hL1 hK L hε
      filter_upwards [hu] with n hnu
      filter_upwards [hnu] with j hju
      intro z hz
      exact hju z.1 hz.1 b
  have he (n j : ℕ) : ForkOverlapSupLimit.windowSup
      (fun n j (z : ℝ×ℝ) => lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b z.1) L n j=
      sSup ((lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b) ''Icc (0:ℝ) L) := by
    unfold ForkOverlapSupLimit.windowSup ForkOverlapSupLimit.window
    apply congrArg sSup
    ext a
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.1,hz.1,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(v,0),⟨hv,⟨le_rfl,L.coe_nonneg⟩⟩,rfl⟩
  simpa only [he] using hh

end SphericalAging.SphereOnlyPhysicalForkLateOverlapLimit
