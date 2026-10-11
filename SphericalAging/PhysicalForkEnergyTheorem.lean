module

public import SphericalAging.CanonicalForkPrecedingBridges
public import SphericalAging.ForkOrderedThreshold
public import SphericalAging.PhysicalForkNormTheorem

public section

/-! The physical finite-fork threshold ceiling, with its actual energy
and normalization limits and its Lipschitz approximants all discharged.
Only the preceding source3.3, Fisher extraction, stationary cluster and
published source10.1 interfaces remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.PhysicalForkEnergyTheorem
open MeasureTheory ProbabilityTheory Set Filter FiniteModel HardSphereDynamics
open WienerForkTransfer ForkSeedCoordinates FiniteForkMoments ForkNormalizedEnergy
open PhysicalForkConstruction ActualForkTraceFormula ForkParameterBounds
open PhysicalForkCenterConcentration PhysicalForkNormalizationLimits PhysicalForkNormTheorem
open ActualForkCenterEnergyLimit CanonicalForkPrecedingBridges ActualEnergyUniformBridge
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints AnnealedHamiltonianEnergyStein
open ExternalFieldProbabilityTransfer ExternalFieldUniformCost ExternalFieldElementaryPenalty
open scoped NNReal ENNReal Topology

theorem forkNorm_le_one {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) {K : ℕ} (hK : 0<K) (L : ℝ≥0) :
    forkNorm c K L≤1 := by
  have hKr : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hK1 : (1:ℝ)≤K := by exact_mod_cast (show 1≤K by omega)
  have hi : 1/(K:ℝ)≤1 := (div_le_one hKr).mpr hK1
  have hc := (H.bounds (2*(L:ℝ)) (by positivity)).2
  unfold forkNorm
  nlinarith

/-- The exact source10.4(b) ceiling for the actual finite physical mean.
It is derived from genuine source10.4 energy/norm/algorithm estimates;
no finite-fork energy limit or ceiling is an input. -/
theorem actual_fork_energy_ceiling {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hOverlap : ActualOverlapL1Convergence p β d)
    (hTrace : ActualTracePrimitiveConvergence (by have hh:=h.spin_ge_three;omega : 2≤p) β d)
    (hThreshold : ∀Lip,PublishedFieldThreshold p Lip) (hK : 0<K) (L : ℝ≥0) :
    forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L≤
      thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2) := by
  classical
  have hp : 2≤p := by have hh:=h.spin_ge_three;omega
  have hd2 (j : ℕ) : 2≤dim j := by have hd:=hDim j;omega
  have hd1 (j : ℕ) : 1≤dim j := by have hd:=hDim j;omega
  let Q := forkNorm c K L
  have hQ : 0<Q := forkNorm_pos_of_profile H.profile hK L
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
    exact actual_center_energy_ordered_limit H hT dim hDim hTop E hLaw hbridge hi hn hL1
      (primitive_bridge_from_preceding β h hTrace dim hTop)
      (energy_bridge_from_preceding β h hOverlap hTrace dim hd1 hTop) hK L
  exact ForkOrderedThreshold.energy_ceiling h.spin_ge_three hK dim
    (fun j => by have hd:=hDim j;omega) hTop hQ hQ1 Y
    (fun n j => fork_joint_law β ((T n).toNNReal+L) (T n).toNNReal) he
    (actual_projection_distance_tendsto H hT dim hd2 hTop E hLaw hbridge hi hn hL1 hK L)
    A hThreshold

end SphericalAging.PhysicalForkEnergyTheorem
