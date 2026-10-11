module

public import SphericalAging.SphereOnlyPhysicalForkOverlapLaw
public import SphericalAging.SphereOnlyPhysicalForkCenterConcentration
public import SphericalAging.ForkSphereNormalization
public import SphericalAging.PhysicalForkNormalizationLimits
public import SphericalAging.ActualSphereOnlyForkUniformL2

public section

/-! The two additional normalization clauses of source10.4 for the
actual fork: scaled mean-square distance from the ball projection to
the predicted normalization or to the sphere normalization, with
dimension limsup taken before stationary time. -/

noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyPhysicalForkNormalizationLimits
open PhysicalForkOverlapLaw PhysicalForkCenterConcentration PhysicalForkNormalizationLimits
open PhysicalForkNormalizationLimits
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open WienerForkTransfer FiniteForkMoments ForkNormalizedEnergy ForkSphereNormalization
open ForkEnergyComparison RandomGaussianPairing SphereOnlyPhysicalForkCenterConcentration
open PhysicalForkConstruction AnnealedHamiltonianEnergyStein
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints ForkParameterBounds
open scoped NNReal ENNReal Topology

/-- Source10.4's two printed replacement clauses for the genuine
whole-path fork, from actual independent-future concentration and the
preceding CK mean/Fisher inputs, without a normalization error premise. -/
theorem actual_normalization_errors {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) :
    Tendsto (fun n => limsup (fun j => normalizationError (forkNorm c K L)
      (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
      Tendsto (fun n => limsup (fun j => radialError (forkNorm c K L)
        (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
          atTop (𝓝 0) := by
  apply normalization_errors_ordered (dim:=dim) (p:=p) (K:=K) (β:=(β:ℝ))
    (Q:=forkNorm c K L) (t:=fun n => (T n).toNNReal+L) (T:=fun n => (T n).toNNReal)
    (Y:=fun n j => branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)
    (fun j => by have hd:=hDim j;omega) hK
    (PhysicalForkCenterConcentration.forkNorm_pos_of_profile H.profile hK L)
    (fun n j => fork_joint_law β ((T n).toNNReal+L) (T n).toNNReal)
  simp_rw [defect_transfer]
  simpa only [forkNorm] using
    SphereOnlyPhysicalForkCenterConcentration.actual_center_defect_tendsto H hT dim hDim hTop hbridge hi hn hL1 hK L

end SphericalAging.SphereOnlyPhysicalForkNormalizationLimits
