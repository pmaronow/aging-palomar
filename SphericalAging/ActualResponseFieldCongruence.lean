module

public import SphericalAging.ActualAnnealedEnergyReplacement

public section

/-! Actual physical response representatives agree under the entire
time/disorder/sphere/path law. The genuine single-branch energy formula
therefore holds for every strongly measurable actual representative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualResponseFieldCongruence
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics TwoTimeResponseParameter TwoTimeResponseTimeParameter
  AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualAnnealedEnergyContraction
  ActualFiniteHorizonEnergyContraction EnergyCovarianceContraction
  ResponseMatrixEnergyContraction
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem actual_matrix_representatives_ae (hN : 0<N)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (H : ℝ≥0)
    (U V : WaitingTime H×((Disorder N p×State N)×Ω)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U) (hV : StronglyMeasurable V)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (hVs : ∀s q (hx : OnSphere q.2),(fun ω => V (s,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) :
    U=ᵐ[(waitingMeasure H).prod ((parameterLaw N p).prod P)] V := by
  apply (Measure.ae_prod_iff_ae_ae (hU.measurableSet_eq_fun hV)).mpr
  exact .of_forall fun s => by
    have hUm : StronglyMeasurable (fun q => U (s,q)) :=
      hU.comp_measurable (measurable_const.prodMk measurable_id)
    have hVm : StronglyMeasurable (fun q => V (s,q)) :=
      hV.comp_measurable (measurable_const.prodMk measurable_id)
    apply (Measure.ae_prod_iff_ae_ae (hUm.measurableSet_eq_fun hVm)).mpr
    filter_upwards [parameterLaw_onSphere (p:=p) hN] with q hx
    exact (hUs s q hx).trans (hVs s q hx).symm

theorem actual_energy_trace_formula_for (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H×((Disorder N p×State N)×Ω)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) :
    let ν := (waitingMeasure H).prod ((parameterLaw N p).prod P)
    let a := overlapField (NullAugmentation.driver D₀) β R hR H
    let e := errorField (NullAugmentation.driver D₀) β R hR H U
    let E := (∫q,Hamiltonian N p q.1.1
      (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N:ℝ)
    Integrable (fun q => (a q)^(p-1)*normalizedTrace (U q)) ν ∧ Integrable e ν ∧
    E=(β:ℝ)*(p:ℝ)*(∫q,(a q)^(p-1)*normalizedTrace (U q) ∂ν)+
      (β:ℝ)*(∫q,e q ∂ν) ∧
    |E-(β:ℝ)*(p:ℝ)*(∫q,(a q)^(p-1)*normalizedTrace (U q) ∂ν)|≤
      (β:ℝ)*(H:ℝ)*Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β H)) := by
  obtain ⟨V,hV,hVs,hvtrace,hverror,hvid,hvbound⟩ :=
    exists_actual_energy_trace_formula hN hp D₀ β R hR hNR H
  have he := actual_matrix_representatives_ae hN D₀ β R hR hNR H U V hU hV hUs hVs
  have ht : (fun q => (overlapField (NullAugmentation.driver D₀) β R hR H q)^(p-1)*normalizedTrace (U q))=ᵐ[
      (waitingMeasure H).prod ((parameterLaw N p).prod P)]
      (fun q => (overlapField (NullAugmentation.driver D₀) β R hR H q)^(p-1)*normalizedTrace (V q)) := he.mono fun q hq => congrArg
    (fun W => (overlapField (NullAugmentation.driver D₀) β R hR H q)^(p-1)*normalizedTrace W) hq
  have hc : errorField (NullAugmentation.driver D₀) β R hR H U=ᵐ[
      (waitingMeasure H).prod ((parameterLaw N p).prod P)]
      errorField (NullAugmentation.driver D₀) β R hR H V := by
    filter_upwards [he] with q hq
    simp only [errorField,hq]
  dsimp only
  refine ⟨hvtrace.congr ht.symm,hverror.congr hc.symm,?_,?_⟩
  · rw [integral_congr_ae ht,integral_congr_ae hc]
    exact hvid
  · rw [integral_congr_ae ht]
    exact hvbound

end SphericalAging.ActualResponseFieldCongruence
