module

public import SphericalAging.PhysicalForkPastConcentration
public import SphericalAging.ActualForkEnergySubtraction

public section

/-! The full-law response formulation and the literal physical
common-past fork formulation have exactly the same overlap fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualForkPastOverlapTransfer
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkConstruction PhysicalForkPastLaw
  PhysicalForkPastConcentration WienerForkTransfer ActualSplicedEnergyLaw
  AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
  ActualForkTraceFormula ActualForkEnergySubtraction PhysicalForkMeanEnergyDuhamel
  AnnealedHamiltonianEnergyStein TwoTimeResponseTimeParameter
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

theorem trajectory_eq_branch (hN : 0<N) (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K) :
    (fun z : ForkSpace N p K => trajectory
      (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1) (modelRadius_pos N)
        t (MeasurableEquiv.prodAssoc z))=ᵐ[forkLaw N p K] branch β t trunk b := by
  exact (measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
    (futureLaw N K) (VectorBrownian.law N)).quasiMeasurePreserving.ae
      (spliced_trajectory_pullback hN β t trunk b)

theorem branchOverlap_eq_waiting (hN : 0<N) (β : ℝ≥0) (t trunk : ℝ≥0)
    (b : Fin K) (s : WaitingTime t) (hs : (s:ℝ≥0)≤trunk) :
    (fun z : ForkSpace N p K => overlapField
      (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1) (modelRadius_pos N)
        t (s,MeasurableEquiv.prodAssoc z))=ᵐ[forkLaw N p K]
      branchWaitingOverlap β t trunk s b := by
  filter_upwards [trajectory_eq_branch (p:=p) hN β t trunk b,
    trajectory_eq_branch (p:=p) hN β s trunk b,
    branch_prefix_eq_waiting (N:=N) (p:=p) β s trunk hs b] with z ht hz hp
  simp only [overlapField,branchWaitingOverlap,ht,hz,hp]

theorem meanOverlap_eq_waiting (hN : 0<N) (β : ℝ≥0) (t trunk : ℝ≥0)
    (b : Fin K) (s : WaitingTime t) (hs : (s:ℝ≥0)≤trunk) :
    (fun z : ForkSpace N p K => ActualForkTraceFormula.meanOverlap β t trunk b
      (s,MeasurableEquiv.prodAssoc z))=ᵐ[forkLaw N p K] meanWaitingOverlap β t trunk s := by
  filter_upwards [trajectory_eq_branch (p:=p) hN β s trunk b,
    branch_prefix_eq_waiting (N:=N) (p:=p) β s trunk hs b] with z hz hp
  change FiniteCorrelationIto.overlap
    (actualMean β t trunk z.1.1.1 z.1.1.2 (z.1.2,z.2))
    (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (modelRadius_pos N) s (MeasurableEquiv.prodAssoc z))=_
  rw [hz,hp]
  rfl

theorem subtraction_abs_integral_eq (hN : 0<N) (β : ℝ≥0) (t trunk : ℝ≥0)
    (b : Fin K) (s : WaitingTime t) (hs : (s:ℝ≥0)≤trunk)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N) :
    (∫q,|subtractionField β t trunk b U (s,q)|
      ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))=
    ∫z,|((branchWaitingOverlap β t trunk s b z)^(p-1)-(meanWaitingOverlap β t trunk s z)^(p-1))*
      EnergyCovarianceContraction.normalizedTrace (U (s,MeasurableEquiv.prodAssoc z))|
        ∂forkLaw N p K := by
  have he := (measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
    (futureLaw N K) (VectorBrownian.law N)).integral_comp
      MeasurableEquiv.prodAssoc.measurableEmbedding
        (fun q => |subtractionField β t trunk b U (s,q)|)
  apply he.symm.trans
  apply integral_congr_ae
  filter_upwards [branchOverlap_eq_waiting hN β t trunk b s hs,
    meanOverlap_eq_waiting hN β t trunk b s hs] with z hb hm
  change |subtractionField β t trunk b U (s,MeasurableEquiv.prodAssoc z)|=_
  simp only [subtractionField,hb,hm]

end SphericalAging.ActualForkPastOverlapTransfer
