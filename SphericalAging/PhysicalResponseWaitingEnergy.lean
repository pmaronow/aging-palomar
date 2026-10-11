module

public import SphericalAging.PhysicalResponseRestart
public import SphericalAging.RandomLinearL2PropagationDifference

public section

/-! Whole-vector energy of moving the response waiting time. The earlier
response restarts from its observed L² state; the later response starts
from the actual later tangent projection. The same-driver difference
estimate contains no dimension factor or assumed cocycle identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PhysicalResponseWaitingEnergy
open HardSphereDynamics LocalSDE PredictableLinearCoefficient RandomLinearVariationalSDE
  TwoTimePhysicalResponse TwoTimeResponseMatrix TwoTimeResponseMoments
  RandomLinearL2PropagationDifference PhysicalVariationalMoments
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ}

theorem waiting_direction_difference_secondMoment (hN : 0<N) (hp : 2≤p)
    (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0→Ω→State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
    {Kb Ks : ℝ≥0} (hb : ∀i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s δ u : ℝ≥0) (hSphere : ∀ᵐ ω ∂P,OnSphere (X s ω))
    (hLater : ∀ᵐ ω ∂P,OnSphere (X (s+δ) ω))
    (hSpherePath : ∀ᵐ ω ∂P,∀t,t≤s+(δ+u)→OnSphere (X t ω))
    (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (v : State N) :
    let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere
    let L := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs (s+δ) u hLater
    (∫ω,‖M (δ+u) v ω-L u v ω‖^2 ∂P)≤
      (∫ω,‖M δ v ω-projection (X (s+δ) ω) v‖^2 ∂P)*
        Real.exp (((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N:ℝ≥0):ℝ)*(u:ℝ)) := by
  dsimp only
  let a := driftRows X hXa hXc β J R hR hb s (δ+u)
  let sigma := noiseRows X hXa hXc R hR hs s (δ+u)
  let Z0 := fun ω => projection (X s ω) v
  let hZ0 := projectedInitial_stronglyMeasurable hXa s v
  let hmZ := projectedInitial_memLp (Nat.ne_of_gt hN) hXa s v hSphere
  let Y := process (ShiftedBrownian.driver D s) a sigma Z0 hZ0 hmZ (δ+u)
  have hY := process_strongSolution (ShiftedBrownian.driver D s) a sigma Z0 hZ0 hmZ (δ+u)
  let aL := driftRows X hXa hXc β J R hR hb (s+δ) u
  let sigmaL := noiseRows X hXa hXc R hR hs (s+δ) u
  let V := Y δ
  let W := fun ω => projection (X (s+δ) ω) v
  have hV : StronglyMeasurable[ShiftedBrownian.filtration F (s+δ) 0] V := by
    rw [ShiftedBrownian.filtration_zero]
    exact hY.1 δ
  have hmV : MemLp V 2 P := (Lp.memLp _).ae_eq
    (terminalResponse_ae (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere δ v)
  have hW := projectedInitial_stronglyMeasurable hXa (s+δ) v
  have hmW := projectedInitial_memLp (Nat.ne_of_gt hN) hXa (s+δ) v hLater
  have hn := ShiftedBrownian.null_known_zero (s+δ) hnull
  have hr := PhysicalResponseRestart.strongSolution_restart D X hXa hXc β J R hR hb hs s δ u hY
  have hcan := process_strongSolution (ShiftedBrownian.driver D (s+δ)) aL sigmaL V hV hmV u
  have he := pathwise_uniqueness hcan hr hn
  have heV : terminalClass (ShiftedBrownian.driver D (s+δ)) aL sigmaL V hV hmV u u=ᵐ[P]
      (fun ω => Y (δ+u) ω) :=
    (terminalClass_ae _ _ _ _ _ _ _ _).trans (he.mono (fun _ h => h u le_rfl))
  have heW : terminalClass (ShiftedBrownian.driver D (s+δ)) aL sigmaL W hW hmW u u=
      terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs (s+δ) u hLater u v :=
    (terminalResponse_eq_terminalClass _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm
  have hpathL : ∀ᵐ ω ∂P,∀t,t≤(s+δ)+u→OnSphere (X t ω) := by
    simpa only [add_assoc] using hSpherePath
  have hc := shiftedRows_physical_bounds hN hp β R hR hNR J X hXa hXc (s+δ) u hpathL hb hs
  have hh := terminalClass_difference_secondMoment (ShiftedBrownian.driver D (s+δ)) aL sigmaL
    V W hV hW hmV hmW (physicalDriftBound p β J) (physicalNoiseTraceBound N) hc.1 hc.2 hn u u le_rfl
  have heOut : (fun ω => terminalClass (ShiftedBrownian.driver D (s+δ)) aL sigmaL V hV hmV u u ω-
      terminalClass (ShiftedBrownian.driver D (s+δ)) aL sigmaL W hW hmW u u ω)=ᵐ[P]
      (fun ω => terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere (δ+u) v ω-
        terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs (s+δ) u hLater u v ω) := by
    rw [heW]
    filter_upwards [heV,terminalResponse_ae (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere (δ+u) v]
      with ω hV hM
    rw [hV,hM]
  have heInit : (fun ω => ‖V ω-W ω‖^2)=ᵐ[P]
      (fun ω => ‖terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere δ v ω-
        projection (X (s+δ) ω) v‖^2) := by
    filter_upwards [terminalResponse_ae (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere δ v]
      with ω hM
    dsimp only [V,W]
    rw [hM]
  rw [integral_congr_ae (heOut.mono (fun _ h => congrArg (fun v => ‖v‖^2) h)),integral_congr_ae heInit] at hh
  exact hh

end SphericalAging.PhysicalResponseWaitingEnergy
