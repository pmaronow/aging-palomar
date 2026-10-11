module

public import SphericalAging.AnnealedMixedHamiltonianStein
public import SphericalAging.MixedHamiltonianSteinDuhamel
public import SphericalAging.ActualMixedResponseCoefficientPairing

public section

/-! Genuine full annealed two-time Hamiltonian-gradient contraction
formula. Both causal time integrals and all exchanges of finite tensor,
time, Gaussian, surface and Wiener integrals are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedMixedResponseContraction
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
  AnnealedMixedHamiltonianStein MixedHamiltonianSteinDuhamel MixedHamiltonianCoefficientDuhamel
  ActualMixedResponseCoefficientIntegral ActualMixedResponseCoefficientPairing
  HamiltonianDisorderTerminalDerivative ActualResponseCoefficientIntegral
  TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
  ActualFiniteHorizonTraceReplacement AnnealedResponseTimeMatrix AnnealedResponseMatrixContraction
  AnnealedTwoTimeResponseMoments
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma integrable_time_disorder_sections
    {S J X W : Type*} [MeasurableSpace S] [MeasurableSpace J] [MeasurableSpace X] [MeasurableSpace W]
    {ν : Measure S} {μJ : Measure J} {μX : Measure X} {μW : Measure W}
    [SFinite ν] [SFinite μJ] [SFinite μX] [SFinite μW]
    {f : S × ((J × X) × W) → ℝ} (hf : Integrable f (ν.prod ((μJ.prod μX).prod μW))) :
    ∀ᵐ x ∂μX,Integrable (fun j => ∫ s,∫ w,f (s,((j,x),w)) ∂μW ∂ν) μJ := by
  have ha := (measurePreserving_prodAssoc ν (μJ.prod μX) μW).integrable_comp_of_integrable hf
  have hj := ha.integral_prod_left.integral_prod_right
  have h := hj.prod_left_ae
  change ∀ᵐ x ∂μX,Integrable (fun j => ∫ s,∫ w,f (s,((j,x),w)) ∂μW ∂ν) μJ at h
  exact h

/-- Actual joint representatives give the exact annealed mixed
Hamiltonian-gradient causal contraction formula, with every exchange
condition derived from the physical SDE moments. -/
theorem actual_gradient_eq_integrated_contractions (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T)
    (Ut : WaitingTime t × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (Ust : StronglyMeasurable Ut)
    (Uts : ∀ r q (hx : OnSphere q.2),(fun ω => Ut (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (t+1) (t-r) q hx))
    (Us : WaitingTime s × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (Uss : StronglyMeasurable Us)
    (Ussr : ∀ r q (hx : OnSphere q.2),(fun ω => Us (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (s+1) (s-r) q hx)) :
    (∫ q : (Disorder N p × State N) × Ω,
      inner ℝ (hamiltonianGradient q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR t q))
        (AnnealedHamiltonianEnergyStein.process D₀ β R hR s q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)=
      (β : ℝ)*(∫ q,∑ I : TensorIndex N p,hessianField (NullAugmentation.driver D₀) β R hR t s Ut I q
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod P))+
      (β : ℝ)*(∫ q,∑ I : TensorIndex N p,crossField (NullAugmentation.driver D₀) β R hR s t Us I q
        ∂(waitingMeasure s).prod ((parameterLaw N p).prod P)) := by
  let f := hessianField (NullAugmentation.driver D₀) β R hR t s Ut
  let g := crossField (NullAugmentation.driver D₀) β R hR s t Us
  have hfi (I : TensorIndex N p) := hessianField_integrable hN hp D₀ β R hR hNR t s Ut Ust Uts I
  have hgi (I : TensorIndex N p) := crossField_integrable hN hp D₀ β R hR hNR s t Us Uss Ussr I
  have hfβ (I : TensorIndex N p) := (hfi I).const_mul (β : ℝ)
  have hgβ (I : TensorIndex N p) := (hgi I).const_mul (β : ℝ)
  have hn₁ (I : TensorIndex N p) := integral_time_disorder_initial_brownian (hfβ I)
  have hn₂ (I : TensorIndex N p) := integral_time_disorder_initial_brownian (hgβ I)
  have hj₁ : ∀ᵐ x ∂SphereInitialLaw.sphereLaw N,∀ I : TensorIndex N p,
      Integrable (fun J : Disorder N p => ∫ r : WaitingTime t,∫ ω,(β : ℝ)*f I (r,((J,x),ω)) ∂P
        ∂waitingMeasure t) (disorderLaw N p) := by
    rw [ae_all_iff]
    exact fun I => integrable_time_disorder_sections (hfβ I)
  have hj₂ : ∀ᵐ x ∂SphereInitialLaw.sphereLaw N,∀ I : TensorIndex N p,
      Integrable (fun J : Disorder N p => ∫ r : WaitingTime s,∫ ω,(β : ℝ)*g I (r,((J,x),ω)) ∂P
        ∂waitingMeasure s) (disorderLaw N p) := by
    rw [ae_all_iff]
    exact fun I => integrable_time_disorder_sections (hgβ I)
  have he : (∫ q : (Disorder N p × State N) × Ω,
      inner ℝ (hamiltonianGradient q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR t q))
        (AnnealedHamiltonianEnergyStein.process D₀ β R hR s q) ∂(AnnealedModelLaw.parameterLaw N p).prod P)=
      ∫ x : State N,∑ I : TensorIndex N p,
        ((∫ J : Disorder N p,∫ r : WaitingTime t,∫ ω,(β : ℝ)*f I (r,((J,x),ω)) ∂P
            ∂waitingMeasure t ∂disorderLaw N p)+
          (∫ J : Disorder N p,∫ r : WaitingTime s,∫ ω,(β : ℝ)*g I (r,((J,x),ω)) ∂P
            ∂waitingMeasure s ∂disorderLaw N p)) ∂SphereInitialLaw.sphereLaw N := by
    rw [actual_gradient_pairing_stein hN (by omega) D₀ β R hR hNR T s t hs ht]
    apply integral_congr_ae
    filter_upwards [SphereInitialLaw.sphereLaw_support hN,hj₁,hj₂] with x hx hj₁ hj₂
    have hx' := (onSphere_iff_norm_sq x).mpr hx
    apply Finset.sum_congr rfl
    intro I _
    have hi : (∫ J : Disorder N p,∫ ω,
      inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
        (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
        (stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1) ω))
        (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω)+
      inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
        (stateResponse (NullAugmentation.driver D₀) β R hR J x T s (Pi.single I 1) ω) ∂P ∂disorderLaw N p)=
        ∫ J : Disorder N p,(∫ r : WaitingTime t,∫ ω,(β : ℝ)*f I (r,((J,x),ω)) ∂P ∂waitingMeasure t)+
          (∫ r : WaitingTime s,∫ ω,(β : ℝ)*g I (r,((J,x),ω)) ∂P ∂waitingMeasure s) ∂disorderLaw N p := by
      apply integral_congr_ae
      exact .of_forall (fun J => by
        have hX := stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx' T t ht
        have hY := stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx' T s hs
        have h := mixed_derivative_matrix_duhamel (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx' T s t hs ht I
        dsimp only
        rw [integral_add (first_pairing_integrable I _ _ _ hX hY)
          (second_pairing_integrable I _ _ _ hX hY),h.2.2.1,h.2.2.2]
        rw [← waiting_integral t,← waiting_integral s]
        congr 1
        · apply integral_congr_ae
          exact .of_forall (fun r => (hessianField_pairing hN D₀ β R hR hNR T t s ht hs Ut Uts I r (J,x) hx').symm.trans
            (integral_const_mul (β : ℝ) (fun ω => f I (r,((J,x),ω)))).symm)
        · apply integral_congr_ae
          exact .of_forall (fun r => (crossField_pairing hN D₀ β R hR hNR T s t hs ht Us Ussr I r (J,x) hx').symm.trans
            (integral_const_mul (β : ℝ) (fun ω => g I (r,((J,x),ω)))).symm))
    exact hi.trans (integral_add (hj₁ I) (hj₂ I))
  rw [he]
  simp_rw [Finset.sum_add_distrib]
  rw [integral_add (integrable_finsetSum Finset.univ (fun I _ => (hn₁ I).1))
    (integrable_finsetSum Finset.univ (fun I _ => (hn₂ I).1))]
  rw [integral_finsetSum Finset.univ (fun I _ => (hn₁ I).1),
    integral_finsetSum Finset.univ (fun I _ => (hn₂ I).1)]
  simp_rw [← (hn₁ _).2,← (hn₂ _).2,integral_const_mul]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  simp only [parameterLaw] at hfi hgi ⊢
  rw [← integral_finsetSum Finset.univ (fun I _ => hfi I),
    ← integral_finsetSum Finset.univ (fun I _ => hgi I)]

/-- Every joint physical response field and every integrability condition
in the exact actual two-time gradient formula are constructed. -/
theorem exists_actual_gradient_contraction_formula (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (s t : ℝ≥0) :
    ∃ Ut : WaitingTime t × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),
    ∃ Us : WaitingTime s × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),
      StronglyMeasurable Ut ∧ StronglyMeasurable Us ∧
      (∀ r q (hx : OnSphere q.2),(fun ω => Ut (r,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (t+1) (t-r) q hx)) ∧
      (∀ r q (hx : OnSphere q.2),(fun ω => Us (r,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (s+1) (s-r) q hx)) ∧
      (∀ I : TensorIndex N p,Integrable (hessianField (NullAugmentation.driver D₀) β R hR t s Ut I)
        ((waitingMeasure t).prod ((parameterLaw N p).prod P))) ∧
      (∀ I : TensorIndex N p,Integrable (crossField (NullAugmentation.driver D₀) β R hR s t Us I)
        ((waitingMeasure s).prod ((parameterLaw N p).prod P))) ∧
      (∫ q : (Disorder N p × State N) × Ω,
        inner ℝ (hamiltonianGradient q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR t q))
          (AnnealedHamiltonianEnergyStein.process D₀ β R hR s q)
          ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)=
        (β : ℝ)*((∫ q,∑ I : TensorIndex N p,hessianField (NullAugmentation.driver D₀) β R hR t s Ut I q
          ∂(waitingMeasure t).prod ((parameterLaw N p).prod P))/(N : ℝ))+
        (β : ℝ)*((∫ q,∑ I : TensorIndex N p,crossField (NullAugmentation.driver D₀) β R hR s t Us I q
          ∂(waitingMeasure s).prod ((parameterLaw N p).prod P))/(N : ℝ)) := by
  obtain ⟨Ut,hUt,hUts,_⟩ := exists_actual_fixedTerminal_matrix hN hp D₀ β R hR hNR t
  obtain ⟨Us,hUs,hUss,_⟩ := exists_actual_fixedTerminal_matrix hN hp D₀ β R hR hNR s
  refine ⟨Ut,Us,hUt,hUs,hUts,hUss,
    (fun I => hessianField_integrable hN hp D₀ β R hR hNR t s Ut hUt hUts I),
    (fun I => crossField_integrable hN hp D₀ β R hR hNR s t Us hUs hUss I),?_⟩
  rw [actual_gradient_eq_integrated_contractions hN hp D₀ β R hR hNR (max s t) s t
    (le_max_left _ _) (le_max_right _ _) Ut hUt hUts Us hUs hUss]
  ring

end SphericalAging.ActualAnnealedMixedResponseContraction
