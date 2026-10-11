module

public import SphericalAging.SphereOnlyCanonicalForkBridges
public import SphericalAging.SphereOnlyPhysicalForkOverlapLaw
public import SphericalAging.SphereOnlyPhysicalForkCenterConcentration
public import SphericalAging.SphereOnlyPhysicalForkNormalizationLimits
public import SphericalAging.SphereOnlyPhysicalForkNormTheorem
public import SphericalAging.SphereOnlyPhysicalForkOverlapAggregation
public import SphericalAging.SphereOnlyPhysicalForkLateOverlapLimit
public import SphericalAging.SphereOnlyActualForkLateEnergyLimit
public import SphericalAging.SphereOnlyActualForkOrderedTraceReplacement
public import SphericalAging.SphereOnlyActualForkCenterEnergyLimit
public import SphericalAging.CanonicalForkPrecedingBridges
public import SphericalAging.ForkOrderedThreshold
public import SphericalAging.PhysicalForkEnergyTheorem
public import SphericalAging.ActualSphereOnlyForkUniformL2

public section

/-! The physical finite-fork threshold ceiling, with its actual energy
and normalization limits and its Lipschitz approximants all discharged.
Only the preceding source3.3, Fisher extraction, stationary cluster and
published source10.1 interfaces remain explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyPhysicalForkEnergyTheorem
open PhysicalForkOverlapLaw PhysicalForkCenterConcentration PhysicalForkNormalizationLimits PhysicalForkNormTheorem PhysicalForkOverlapAggregation PhysicalForkLateOverlapLimit ActualForkLateEnergyLimit ActualForkOrderedTraceReplacement ActualForkCenterEnergyLimit PhysicalForkEnergyTheorem
open PhysicalForkEnergyTheorem
open MeasureTheory ProbabilityTheory Set Filter FiniteModel HardSphereDynamics
open WienerForkTransfer ForkSeedCoordinates FiniteForkMoments ForkNormalizedEnergy
open PhysicalForkConstruction ActualForkTraceFormula ForkParameterBounds
open SphereOnlyPhysicalForkCenterConcentration SphereOnlyPhysicalForkNormalizationLimits SphereOnlyPhysicalForkNormTheorem
open SphereOnlyActualForkCenterEnergyLimit CanonicalForkPrecedingBridges ActualEnergyUniformBridge
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints AnnealedHamiltonianEnergyStein
open ExternalFieldProbabilityTransfer ExternalFieldUniformCost ExternalFieldElementaryPenalty
open SphereOnlyCanonicalForkBridges
open scoped NNReal ENNReal Topology

/-- The exact source10.4(b) ceiling for the actual finite physical mean.
It is derived from genuine source10.4 energy/norm/algorithm estimates;
no finite-fork energy limit or ceiling is an input. -/
theorem actual_fork_energy_ceiling {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    (hThreshold : ∀Lip,PublishedFieldThreshold p Lip) (hK : 0<K) (L : ℝ≥0) :
    forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L≤
      thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2) := by
  classical
  have hp : 2≤p := by have hh:=h.spin_ge_three;omega
  have hd2 (j : ℕ) : 2≤dim j := by have hd:=hDim j;omega
  have hd1 (j : ℕ) : 1≤dim j := by have hd:=hDim j;omega
  let Q := forkNorm c K L
  have hQ : 0<Q := PhysicalForkCenterConcentration.forkNorm_pos_of_profile H.profile hK L
  have hQ1 : Q≤1 := forkNorm_le_one H.profile hK L
  let Y := fun n j => branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal
  have hAexists (n : ℕ) : Nonempty (ForkOrderedThreshold.Algorithm p K Q (Y n)) := by
    obtain ⟨Lip,A,hA,hLip,hBall,hError⟩ :=
      ActualForkBallAlgorithm.exists_actual_fork_ball_algorithm hK hp dim hd2 hTop β L (T n).toNNReal Q hQ
    exact ⟨{lip:=Lip,output:=A,measurable:=hA,lipschitz:=hLip,ball:=hBall,error:=hError}⟩
  let A := fun n => Classical.choice (hAexists n)
  have he : Tendsto (fun z : ℕ×ℕ => expectedEnergy (μ:=measure (dim z.2) p K)
      Prod.snd (seededMean (Y z.1 z.2))) ((atTop : Filter ℕ).curry (atTop : Filter ℕ))
      (𝓝 (forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L)) := by
    simp_rw [energy_transfer]
    exact SphereOnlyActualForkCenterEnergyLimit.actual_center_energy_ordered_limit H hT dim hDim hTop hbridge hi hn hL1
      (canonical_primitiveBridge β h dim hDim hTop)
      (canonical_energyBridge β h dim hDim hTop) hK L
  exact ForkOrderedThreshold.energy_ceiling h.spin_ge_three hK dim
    (fun j => by have hd:=hDim j;omega) hTop hQ hQ1 Y
    (fun n j => fork_joint_law β ((T n).toNNReal+L) (T n).toNNReal) he
    (SphereOnlyPhysicalForkCenterConcentration.actual_projection_distance_tendsto H hT dim hd2 hTop hbridge hi hn hL1 hK L)
    A hThreshold

end SphericalAging.SphereOnlyPhysicalForkEnergyTheorem
