module

public import SphericalAging.PhysicalForkLateOverlapLimit
public import SphericalAging.ActualForkPastOverlapTransfer

public section

/-! The last-window physical fork overlaps transfer exactly to the
full parameter × PathSeed fields used by the actual energy formula. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkLateOverlapTransfer
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open PhysicalForkDrivers PhysicalForkConstruction WienerForkTransfer ActualForkPastOverlapTransfer
open AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
open ActualForkTraceFormula ActualForkEnergySubtraction PhysicalForkMeanEnergyDuhamel
open AnnealedHamiltonianEnergyStein TwoTimeResponseTimeParameter
open PhysicalForkOverlapAggregation PhysicalForkLateOverlapLimit ForkParameterBounds
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def lateWaiting (T L v : ℝ≥0) (hv : v≤L) : WaitingTime (T+L) :=
  ⟨T+v,⟨zero_le,add_le_add le_rfl hv⟩⟩

theorem branchOverlap_eq_pairOverlap (hN : 0<N) (β : ℝ≥0) (T L v : ℝ≥0)
    (hv : v≤L) (b : Fin K) :
    (fun z : ForkSpace N p K => overlapField
      (NullAugmentation.driver (driver (N:=N) (K:=K) T b)) β (N+1) (modelRadius_pos N)
        (T+L) (lateWaiting T L v hv,MeasurableEquiv.prodAssoc z))=ᵐ[forkLaw N p K]
      pairOverlap β T L v b b := by
  filter_upwards [trajectory_eq_branch (p:=p) hN β (T+L) T b,
    trajectory_eq_branch (p:=p) hN β (T+v) T b] with z ht hs
  simp only [overlapField,lateWaiting,pairOverlap,FiniteCorrelationIto.overlap,ht,hs]

theorem meanOverlap_eq_literal (hN : 0<N) (β : ℝ≥0) (T L v : ℝ≥0)
    (hv : v≤L) (b : Fin K) :
    (fun z : ForkSpace N p K => ActualForkTraceFormula.meanOverlap β (T+L) T b
      (lateWaiting T L v hv,MeasurableEquiv.prodAssoc z))=ᵐ[forkLaw N p K]
        PhysicalForkOverlapAggregation.meanOverlap β T L v b := by
  filter_upwards [trajectory_eq_branch (p:=p) hN β (T+v) T b] with z hs
  change ⟪actualMean β (T+L) T z.1.1.1 z.1.1.2 (z.1.2,z.2),
    trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) T b)) β (N+1)
      (modelRadius_pos N) (T+v) (MeasurableEquiv.prodAssoc z)⟫_ℝ/(N:ℝ)=_
  rw [hs]
  rfl

/-- Exact full-law error identity for the actual single and mean overlap
fields, with no restriction to the common past. -/
theorem late_overlap_error_integral_eq (hN : 0<N) (β : ℝ≥0) (T L v : ℝ≥0)
    (hv : v≤L) (b : Fin K) (c : ℝ→ℝ) :
    (∫q,(overlapField (NullAugmentation.driver (driver (N:=N) (K:=K) T b)) β (N+1)
      (modelRadius_pos N) (T+L) (lateWaiting T L v hv,q)-c ((L:ℝ)-(v:ℝ)))^2
        ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))+
    (∫q,(ActualForkTraceFormula.meanOverlap β (T+L) T b (lateWaiting T L v hv,q)-
      mixedOverlap c K L ((L:ℝ)-(v:ℝ)))^2
        ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))=
      lateOverlapError (N:=N) (p:=p) β T L c b v := by
  have hmp := measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
    (futureLaw N K) (VectorBrownian.law N)
  have hd := hmp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun q => (overlapField (NullAugmentation.driver (driver (N:=N) (K:=K) T b)) β (N+1)
      (modelRadius_pos N) (T+L) (lateWaiting T L v hv,q)-c ((L:ℝ)-(v:ℝ)))^2)
  have hm := hmp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun q => (ActualForkTraceFormula.meanOverlap β (T+L) T b (lateWaiting T L v hv,q)-
      mixedOverlap c K L ((L:ℝ)-(v:ℝ)))^2)
  unfold pathSeedLaw
  rw [←hd,←hm]
  unfold lateOverlapError
  rw [Real.toNNReal_coe]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · exact integral_congr_ae ((branchOverlap_eq_pairOverlap hN β T L v hv b).mono
      (fun z hz => congrArg (fun a : ℝ => (a-c ((L:ℝ)-(v:ℝ)))^2) hz))
  · exact integral_congr_ae ((meanOverlap_eq_literal hN β T L v hv b).mono
      (fun z hz => congrArg (fun a : ℝ => (a-mixedOverlap c K L ((L:ℝ)-(v:ℝ)))^2) hz))

end SphericalAging.ActualForkLateOverlapTransfer
