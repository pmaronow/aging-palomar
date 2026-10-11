module

public import SphericalAging.ActualResponseCoefficientIntegral
public import SphericalAging.ActualFiniteHorizonEnergyContraction

public section

/-! Genuine finite-N energy/response covariance identity under the
actual independent Gaussian disorder, sphere initial state and Brownian
law. All time/parameter exchanges follow from actual response-column
moments, after the actual Gaussian Stein and Duhamel identities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedEnergyContraction
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
open TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
open ActualFiniteHorizonTraceReplacement ActualFiniteHorizonEnergyContraction
open ActualResponseCoefficientIntegral AnnealedEnergyDuhamel QuenchedCoefficientDuhamel
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem actual_energy_eq_integrated_contraction (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) :
    (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
      ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)=
      (β : ℝ)*(∫ q,orderedContraction (NullAugmentation.driver D₀) β R hR H U q
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  let ν := (waitingMeasure H).prod ((parameterLaw N p).prod P)
  let f := coefficientField (NullAugmentation.driver D₀) β R hR H U
  have hfi (I : TensorIndex N p) : Integrable (f I) ν :=
    coefficientField_integrable hN hp D₀ β R hR hNR H U hU hUs I
  have hbi (I : TensorIndex N p) := (hfi I).const_mul (β : ℝ)
  have hn (I : TensorIndex N p) := integral_time_disorder_initial_brownian (hbi I)
  have he : (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
      ∂(AnnealedModelLaw.parameterLaw N p).prod P)=
      ∫ x : State N,∑ I : TensorIndex N p,∫ J : Disorder N p,∫ s : WaitingTime H,∫ ω,
        (β : ℝ)*f I (s,((J,x),ω)) ∂P ∂waitingMeasure H ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
    rw [actual_energy_duhamel hN (by omega) D₀ β R hR hNR H]
    apply integral_congr_ae
    filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
    have hx' := (onSphere_iff_norm_sq x).mpr hx
    apply Finset.sum_congr rfl
    intro I _
    apply integral_congr_ae
    exact .of_forall (fun J => by
      change (∫ s,sphereCoefficientKernel (Nat.ne_of_gt hN) D₀ β R hR hNR J x H I s ∂finiteTimeMeasure H)=_
      have hs : sphereCoefficientKernel (Nat.ne_of_gt hN) D₀ β R hR hNR J x H I=
          coefficientKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx' H I := by
        funext s
        simp only [sphereCoefficientKernel,dif_pos hx']
      rw [hs,← waiting_integral]
      apply integral_congr_ae
      exact .of_forall (fun s => by
        exact (coefficientField_pairing hN D₀ β R hR hNR H U hUs I s (J,x) hx').symm.trans
          (integral_const_mul (β : ℝ) (fun ω => f I (s,((J,x),ω)))).symm))
  have hs := integrable_finsetSum Finset.univ (fun I _ => hfi I)
  have hen : (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
      ∂(AnnealedModelLaw.parameterLaw N p).prod P)=
      (β : ℝ)*(∫ q,∑ I : TensorIndex N p,f I q ∂ν) := by
    rw [he,integral_finsetSum Finset.univ (fun I _ => (hn I).1)]
    simp_rw [← (hn _).2,integral_const_mul]
    rw [← Finset.mul_sum]
    change (β : ℝ)*(∑ I : TensorIndex N p,∫ q,f I q ∂ν)=_
    rw [← integral_finsetSum Finset.univ (fun I _ => hfi I)]
  rw [hen]
  unfold orderedContraction
  rw [integral_div]
  change (β : ℝ)*(∫ q,∑ I : TensorIndex N p,f I q ∂ν)/(N : ℝ)=
    (β : ℝ)*((∫ q,∑ I : TensorIndex N p,f I q ∂ν)/(N : ℝ))
  ring

/-- Exact finite-N source energy/response trace formula. The common
matrix represents the genuine physical two-time response in every sphere
parameter section. Its actual rank-one correction has vanishing mean;
no derivative, Duhamel, trace identity or moment is a premise. -/
theorem exists_actual_energy_trace_formula (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      let ν := (waitingMeasure H).prod ((parameterLaw N p).prod P)
      let a := overlapField (NullAugmentation.driver D₀) β R hR H
      let e := errorField (NullAugmentation.driver D₀) β R hR H U
      let E := (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)
      Integrable (fun q => (a q)^(p-1)*EnergyCovarianceContraction.normalizedTrace (U q)) ν ∧ Integrable e ν ∧
      E=(β : ℝ)*(p : ℝ)*(∫ q,(a q)^(p-1)*EnergyCovarianceContraction.normalizedTrace (U q) ∂ν)+(β : ℝ)*(∫ q,e q ∂ν) ∧
      |E-(β : ℝ)*(p : ℝ)*(∫ q,(a q)^(p-1)*EnergyCovarianceContraction.normalizedTrace (U q) ∂ν)|≤
        (β : ℝ)*(H : ℝ)*Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H)) := by
  obtain ⟨U,hU,hUs,hc,hw,he,hid,herr⟩ := exists_actual_integrated_contraction hN hp D₀ β R hR hNR H
  have henergy := actual_energy_eq_integrated_contraction hN hp D₀ β R hR hNR H U hU hUs
  refine ⟨U,hU,hUs,hw,he,?_,?_⟩
  · rw [henergy,hid]
    ring
  · have heq : (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)-
        (β : ℝ)*(p : ℝ)*(∫ q,(overlapField (NullAugmentation.driver D₀) β R hR H q)^(p-1)*
          EnergyCovarianceContraction.normalizedTrace (U q) ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))=
        (β : ℝ)*((∫ q,orderedContraction (NullAugmentation.driver D₀) β R hR H U q
          ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))-
          (p : ℝ)*(∫ q,(overlapField (NullAugmentation.driver D₀) β R hR H q)^(p-1)*
            EnergyCovarianceContraction.normalizedTrace (U q) ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))) := by
      rw [henergy]
      ring
    change |_ - _|≤_
    rw [heq,abs_mul,abs_of_nonneg β.coe_nonneg]
    exact (mul_le_mul_of_nonneg_left herr β.coe_nonneg).trans_eq (by ring)

/-- Concrete actual model form, using the literal independent vector
Wiener law and the cutoff already proved to agree on the physical sphere. -/
theorem exists_actual_model_energy_trace_formula (hN : 0<N) (hp : 2≤p)
    (β : ℝ≥0) (H : ℝ≥0) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × VectorBrownian.Space N) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[VectorBrownian.law N]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
          s (H+1) (H-s) q hx)) ∧
      let ν := (waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))
      let a := overlapField (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) H
      let e := errorField (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) H U
      let E := (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.modelProcess N p β H q)
        ∂AnnealedModelLaw.law N p)/(N : ℝ)
      Integrable (fun q => (a q)^(p-1)*EnergyCovarianceContraction.normalizedTrace (U q)) ν ∧ Integrable e ν ∧
      E=(β : ℝ)*(p : ℝ)*(∫ q,(a q)^(p-1)*EnergyCovarianceContraction.normalizedTrace (U q) ∂ν)+(β : ℝ)*(∫ q,e q ∂ν) ∧
      |E-(β : ℝ)*(p : ℝ)*(∫ q,(a q)^(p-1)*EnergyCovarianceContraction.normalizedTrace (U q) ∂ν)|≤
        (β : ℝ)*(H : ℝ)*Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H)) :=
  exists_actual_energy_trace_formula hN hp (VectorBrownian.driver N) β (N+1)
    (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N) H

end SphericalAging.ActualAnnealedEnergyContraction
