module

public import SphericalAging.ActualForkLateEnergyReplacement

public section

/-! A finite genuine full-history energy trace estimate: the canonical
weighted response differs only by the actual common-past and late-window
random-power errors. Every term uses the same physical matrix field. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkWeightedEnergyReplacement
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open PhysicalForkDrivers ActualForkTraceFormula ActualForkEnergySubtraction
open ActualForkPastEnergyBound ActualForkLateEnergyReplacement PhysicalForkLateOverlapLimit
open AnnealedResponseMatrixContraction ActualCompactJointOverlapVariance
open TwoTimeResponseTimeParameter EnergyCovarianceContraction ActualResponseKernel
open ActualFiniteHorizonTraceReplacement ActualAnnealedEnergyReplacement
open AnnealedHamiltonianEnergyStein
open scoped NNReal ENNReal Topology
variable {N p K : ℕ}

theorem actual_full_trace_replacement_bound (hN : 3≤N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (T L : ℝ≥0) {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) (b : Fin K)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix (by omega : 0<N) β (T+L) T b U)
    {B : ℝ} (hB : ∀v : ℝ≥0,∀hv : v≤L,lateOverlapError (N:=N) (p:=p) β T L c b v≤B) :
    Integrable (subtractionField β (T+L) T b U) (integratedLaw N p K (T+L)) ∧
    |(∫a,subtractionField β (T+L) T b U a ∂integratedLaw N p K (T+L))-
      ∫s,lateDeterministicWeight p K c T L s*
        annealedResponse (p:=p) (by omega : N≠0) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
          (T+L) s ∂waitingMeasure (T+L)|≤
      ((T+L:ℝ≥0):ℝ)*((p-1:ℕ):ℝ)*Real.sqrt (4*jointVarianceCeiling p β (T+L+1)/(N:ℝ))*
        Real.sqrt (1+annealedFourthConstant p β (T+L))+
      (L:ℝ)*2*((p-1:ℕ):ℝ)*Real.sqrt B*Real.sqrt (1+annealedFourthConstant p β L) := by
  have hn : 0<N := by omega
  have hPast := actual_past_integrated_trace_bound hN hp hK β (T+L) T b U hU hUs
  have hLate := actual_late_integrated_replacement_bound hn hp hK β T L H b U hU hUs hB
  have hWeight := actual_late_weighted_response hn hp hK β T L H b U hU hUs
  have hsum := (hPast.1.add hLate.1).add hWeight.1
  have hi : Integrable (subtractionField β (T+L) T b U) (integratedLaw N p K (T+L)) :=
    hsum.congr (.of_forall (fun a => (subtractionField_split β T L b c U a).symm))
  refine ⟨hi,?_⟩
  have he : (∫a,subtractionField β (T+L) T b U a ∂integratedLaw N p K (T+L))-
      (∫s,lateDeterministicWeight p K c T L s*
        annealedResponse (p:=p) (Nat.ne_of_gt hn) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
          (T+L) s ∂waitingMeasure (T+L))=
      (∫a,pastSubtractionField β (T+L) T b U a ∂integratedLaw N p K (T+L))+
        ∫a,lateReplacementField β T L b c U a ∂integratedLaw N p K (T+L) := by
    have hsf : subtractionField β (T+L) T b U=
      pastSubtractionField β (T+L) T b U+lateReplacementField β T L b c U+
        (fun a => lateDeterministicWeight p K c T L a.1*normalizedTrace (U a)) :=
      funext (subtractionField_split β T L b c U)
    rw [←hWeight.2,hsf,
      integral_add' (hPast.1.add hLate.1) hWeight.1,integral_add' hPast.1 hLate.1]
    ring
  rw [he]
  have hpabs : |∫a,pastSubtractionField β (T+L) T b U a ∂integratedLaw N p K (T+L)|≤
      ∫a,|pastSubtractionField β (T+L) T b U a| ∂integratedLaw N p K (T+L) := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f:=pastSubtractionField β (T+L) T b U) (μ:=integratedLaw N p K (T+L))
  have hlabs : |∫a,lateReplacementField β T L b c U a ∂integratedLaw N p K (T+L)|≤
      ∫a,|lateReplacementField β T L b c U a| ∂integratedLaw N p K (T+L) := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f:=lateReplacementField β T L b c U) (μ:=integratedLaw N p K (T+L))
  exact (abs_add_le _ _).trans (add_le_add (hpabs.trans hPast.2) (hlabs.trans hLate.2))

end SphericalAging.ActualForkWeightedEnergyReplacement
