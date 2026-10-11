module

public import SphericalAging.BallMatrixFieldContraction
public import SphericalAging.AnnealedResponseTimeMatrix

public section

/-! Ball-center response corrections under the complete Gaussian,
uniform-sphere and Brownian background. Actual response column moments
are derived, including for a driver with a common fork past. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualBallResponseFieldMoments
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics TwoTimeResponseParameter TwoTimeResponseTimeParameter
  AnnealedTwoTimeResponseMoments AnnealedResponseTimeMoments AnnealedResponseMatrixContraction
  ResponseMatrixEnergyContraction EnergyCovarianceContraction BallMatrixFieldContraction
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem actual_matrix_columns_fourthMoments (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H×((Disorder N p×State N)×Ω)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (s : WaitingTime H) (i : Fin N) :
    MemLp (fun q => U (s,q) (basisVector i)) 4 ((parameterLaw N p).prod P) ∧
      (∫q,‖U (s,q) (basisVector i)‖^4 ∂(parameterLaw N p).prod P)≤annealedFourthConstant p β H := by
  obtain ⟨G,hG,hGV,hGM⟩ := exists_fixedTerminalColumn_joint_L4 hN hp D₀ β R hR hNR H (basisVector i)
  have hcol : StronglyMeasurable (fun q => U (s,q) (basisVector i)) :=
    ((ContinuousLinearMap.apply ℝ (State N) (basisVector i)).continuous.comp_stronglyMeasurable hU).comp_measurable
      (measurable_const.prodMk measurable_id)
  have hgs : StronglyMeasurable (fun q => G (s,q)) := hG.comp_measurable
    (measurable_const.prodMk measurable_id)
  have he : (fun q => U (s,q) (basisVector i))=ᵐ[(parameterLaw N p).prod P] (fun q => G (s,q)) := by
    apply (Measure.ae_prod_iff_ae_ae (hcol.measurableSet_eq_fun hgs)).mpr
    filter_upwards [parameterLaw_onSphere (p:=p) hN] with q hq
    filter_upwards [hUs s q hq,hGV s q] with ω hu hg
    rw [hu,sampleMatrix_basis]
    have heq : fixedTerminalColumn (Nat.ne_of_gt hN) D₀ β R hR hNR H (basisVector i) s q=
        physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hq (basisVector i) := by
      simp only [fixedTerminalColumn,dif_pos hq]
    rw [heq] at hg
    exact hg.symm
  refine ⟨(memLp_congr_ae he).mpr (hGM s).1,?_⟩
  rw [integral_congr_ae (he.mono fun q hq => congrArg (fun z : State N => ‖z‖^4) hq)]
  simpa [basisVector] using (hGM s).2

theorem actual_ball_field_energyCorrection_moments (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H×((Disorder N p×State N)×Ω)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (s : WaitingTime H) {M : (Disorder N p×State N)×Ω→State N}
    (hMm : AEStronglyMeasurable M ((parameterLaw N p).prod P))
    (hM : ∀ᵐq ∂(parameterLaw N p).prod P,‖M q‖≤Real.sqrt (N:ℝ)) :
    MemLp (fun q => energyCorrection (p:=p) (M q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q) (U (s,q))) 2 ((parameterLaw N p).prod P) ∧
    (∫q,(energyCorrection (p:=p) (M q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q) (U (s,q)))^2 ∂(parameterLaw N p).prod P)≤
      ((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β H) ∧
    (∫q,|energyCorrection (p:=p) (M q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q) (U (s,q))| ∂(parameterLaw N p).prod P)≤
      Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β H)) := by
  exact ball_field_energyCorrection_moments hN hp (fun q => U (s,q))
    (annealedFourthConstant p β H)
    (fun i => (actual_matrix_columns_fourthMoments hN hp D₀ β R hR hNR H U hU hUs s i).1)
    (fun i => (actual_matrix_columns_fourthMoments hN hp D₀ β R hR hNR H U hU hUs s i).2)
    hMm (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR s).aestronglyMeasurable hM
    ((trajectory_onSphere hN D₀ β R hR hNR s).mono fun q hq => le_of_eq (FiniteCorrelationIto.sphere_norm hq))

end SphericalAging.ActualBallResponseFieldMoments
