module

public import SphericalAging.ActualMixedResponseCoefficientIntegral
public import SphericalAging.MixedHamiltonianCoefficientDuhamel

public section

/-! The measurable joint actual mixed response coefficient fields
represent the genuine conditional matrix Duhamel kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualMixedResponseCoefficientPairing
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
  ActualMixedResponseCoefficientIntegral MixedHamiltonianCoefficientDuhamel
  ActualTerminalHorizonConsistency TwoTimeResponseParameter TwoTimeResponseTimeParameter
  TwoTimeResponseHorizon ResponseMatrixEnergyContraction AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualSphereTransition
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma hessianField_pairing (hN : 0 < N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (T H S : ℝ≥0) (hHT : H ≤ T) (hST : S ≤ T)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx))
    (I : TensorIndex N p) (r : WaitingTime H) (q : Disorder N p × State N) (hx : OnSphere q.2) :
    β*(∫ ω,hessianField (NullAugmentation.driver D₀) β R hR H S U I (r,(q,ω)) ∂P)=
      firstKernelPairing (Nat.ne_of_gt hN) D₀ β q.1 R hR hNR q.2 hx T S H I r := by
  unfold firstKernelPairing
  congr 1
  have hm := physicalMatrix_horizon_independent (Nat.ne_of_gt hN) D₀ β R hR hNR
    r (H-r) (H+1) (by exact (tsub_le_self).trans (le_add_right le_rfl)) (H-r) le_rfl q hx
  have hmr : physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H-r) (H-r) q hx=
      CanonicalDisorderDuhamelMatrix.responseMatrix (Nat.ne_of_gt hN) D₀ β q.1 R hR hNR q.2 hx H r := rfl
  apply integral_congr_ae
  filter_upwards [hUs r q hx,jointProcess_ae (NullAugmentation.driver D₀) β R hR q,
    stateClass_ae_global_at D₀ β R hR q.1 q.2 T H hHT,
    stateClass_ae_global_at D₀ β R hR q.1 q.2 T S hST] with ω hu hX hH hS
  change inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) _ (U (r,(q,ω)) _)) _=_
  rw [hu,hm,hmr,hH,hS]
  have hXH := hX H
  have hXr := hX r
  have hXS := hX S
  simp only [trajectory] at *
  rw [hXH,hXr,hXS]

lemma crossField_pairing (hN : 0 < N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (T H A : ℝ≥0) (hHT : H ≤ T) (hAT : A ≤ T)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx))
    (I : TensorIndex N p) (r : WaitingTime H) (q : Disorder N p × State N) (hx : OnSphere q.2) :
    β*(∫ ω,crossField (NullAugmentation.driver D₀) β R hR H A U I (r,(q,ω)) ∂P)=
      secondKernelPairing (Nat.ne_of_gt hN) D₀ β q.1 R hR hNR q.2 hx T A H I r := by
  unfold secondKernelPairing
  congr 1
  have hm := physicalMatrix_horizon_independent (Nat.ne_of_gt hN) D₀ β R hR hNR
    r (H-r) (H+1) (by exact (tsub_le_self).trans (le_add_right le_rfl)) (H-r) le_rfl q hx
  have hmr : physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H-r) (H-r) q hx=
      CanonicalDisorderDuhamelMatrix.responseMatrix (Nat.ne_of_gt hN) D₀ β q.1 R hR hNR q.2 hx H r := rfl
  apply integral_congr_ae
  filter_upwards [hUs r q hx,jointProcess_ae (NullAugmentation.driver D₀) β R hR q,
    stateClass_ae_global_at D₀ β R hR q.1 q.2 T A hAT] with ω hu hX hA
  change inner ℝ _ (U (r,(q,ω)) _)=_
  rw [hu,hm,hmr,hA]
  have hXA := hX A
  have hXr := hX r
  simp only [trajectory] at *
  rw [hXA,hXr]

end SphericalAging.ActualMixedResponseCoefficientPairing
