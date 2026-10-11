module

public import SphericalAging.ActualMixedResponseTraceContraction
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! The exact actual two-time Hamiltonian force is the two CK trace
memories plus explicit dimension-vanishing physical rank corrections. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedCorrelationMemory
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
  ActualMixedResponseCoefficientIntegral ActualMixedResponseTraceContraction
  ActualAnnealedMixedResponseContraction AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement AnnealedTwoTimeResponseMoments
  TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction AnnealedResponseTimeMatrix
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def meanForce (D₀ : BrownianDriver N P F) (β : ℝ≥0) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (s t : ℝ≥0) : ℝ :=
  (∫ q : (Disorder N p × State N) × Ω,
    inner ℝ (hamiltonianGradient q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR t q))
      (AnnealedHamiltonianEnergyStein.process D₀ β R hR s q)
      ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)

@[expose] def hessianMemory (D₀ : BrownianDriver N P F) (β : ℝ≥0) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H S : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N)) : ℝ :=
  ∫ q,(mixedOverlap (NullAugmentation.driver D₀) β R hR H H q)^(p-2)*
    mixedOverlap (NullAugmentation.driver D₀) β R hR H S q*normalizedTrace (U q)
    ∂(waitingMeasure H).prod ((parameterLaw N p).prod P)

@[expose] def crossMemory (D₀ : BrownianDriver N P F) (β : ℝ≥0) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H A : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N)) : ℝ :=
  ∫ q,(mixedOverlap (NullAugmentation.driver D₀) β R hR H A q)^(p-1)*normalizedTrace (U q)
    ∂(waitingMeasure H).prod ((parameterLaw N p).prod P)

@[expose] def rankResidualCeiling (p : ℕ) (β s t : ℝ≥0) (N : ℕ) : ℝ :=
  (β : ℝ)*(((p : ℝ)*((p : ℝ)-1)^2/(N : ℝ))*
    ((t : ℝ)*Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β t)))+
    ((p : ℝ)*((p : ℝ)-1)/(N : ℝ))*
    ((s : ℝ)*Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β s))))

theorem actual_force_trace_memory (hN : 0<N) (hp : 3≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0)
    (Ut : WaitingTime t × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hUt : StronglyMeasurable Ut)
    (hUts : ∀ r q (hx : OnSphere q.2),(fun ω => Ut (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (t+1) (t-r) q hx))
    (Us : WaitingTime s × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hUs : StronglyMeasurable Us)
    (hUss : ∀ r q (hx : OnSphere q.2),(fun ω => Us (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (s+1) (s-r) q hx)) :
    meanForce (p := p) D₀ β R hR s t=
      (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*hessianMemory D₀ β R hR t s Ut+
      (β : ℝ)*(p : ℝ)*crossMemory D₀ β R hR s t Us+
      (β : ℝ)*(∫ q,hessianError (NullAugmentation.driver D₀) β R hR t s Ut q
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod P))+
      (β : ℝ)*(∫ q,crossError (NullAugmentation.driver D₀) β R hR s t Us q
        ∂(waitingMeasure s).prod ((parameterLaw N p).prod P)) := by
  unfold meanForce
  rw [actual_gradient_eq_integrated_contractions hN (by omega) D₀ β R hR hNR (max s t) s t
    (le_max_left _ _) (le_max_right _ _) Ut hUt hUts Us hUs hUss]
  have ht := actual_hessian_trace_split hN hp D₀ β R hR hNR t s Ut hUt hUts
  have hs := actual_cross_trace_split hN (by omega) D₀ β R hR hNR s t Us hUs hUss
  rw [integral_div] at ht hs
  change _=(p : ℝ)*((p-1 : ℕ) : ℝ)*hessianMemory D₀ β R hR t s Ut+_ at ht
  change _=(p : ℝ)*crossMemory D₀ β R hR s t Us+_ at hs
  calc
    _=(β : ℝ)*((∫ q,∑ I : TensorIndex N p,hessianField (NullAugmentation.driver D₀) β R hR t s Ut I q
      ∂(waitingMeasure t).prod ((parameterLaw N p).prod P))/(N : ℝ))+
      (β : ℝ)*((∫ q,∑ I : TensorIndex N p,crossField (NullAugmentation.driver D₀) β R hR s t Us I q
      ∂(waitingMeasure s).prod ((parameterLaw N p).prod P))/(N : ℝ)) := by ring
    _=_ := by rw [ht,hs];ring

theorem actual_force_trace_memory_residual_le (hN : 0<N) (hp : 3≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0)
    (Ut : WaitingTime t × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hUt : StronglyMeasurable Ut)
    (hUts : ∀ r q (hx : OnSphere q.2),(fun ω => Ut (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (t+1) (t-r) q hx))
    (Us : WaitingTime s × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hUs : StronglyMeasurable Us)
    (hUss : ∀ r q (hx : OnSphere q.2),(fun ω => Us (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (s+1) (s-r) q hx)) :
    |meanForce (p := p) D₀ β R hR s t-
      ((β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*hessianMemory D₀ β R hR t s Ut+
        (β : ℝ)*(p : ℝ)*crossMemory D₀ β R hR s t Us)|≤rankResidualCeiling p β s t N := by
  rw [actual_force_trace_memory hN hp D₀ β R hR hNR s t Ut hUt hUts Us hUs hUss]
  have ht := (actual_hessianError_integrable_le hN hp D₀ β R hR hNR t s Ut hUt hUts).2
  have hs := (actual_crossError_integrable_le hN (by omega) D₀ β R hR hNR s t Us hUs hUss).2
  have he (a b c d : ℝ) : a+b+c+d-(a+b)=c+d := by ring
  rw [he]
  calc
    _≤|(β : ℝ)*(∫ q,hessianError (NullAugmentation.driver D₀) β R hR t s Ut q
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod P))|+
      |(β : ℝ)*(∫ q,crossError (NullAugmentation.driver D₀) β R hR s t Us q
        ∂(waitingMeasure s).prod ((parameterLaw N p).prod P))| := abs_add_le _ _
    _≤(β : ℝ)*((∫ q,|hessianError (NullAugmentation.driver D₀) β R hR t s Ut q|
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod P))+
      (∫ q,|crossError (NullAugmentation.driver D₀) β R hR s t Us q|
        ∂(waitingMeasure s).prod ((parameterLaw N p).prod P))) := by
      simp only [abs_mul,abs_of_nonneg β.coe_nonneg]
      rw [mul_add]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs β.coe_nonneg
      · exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs β.coe_nonneg
    _≤rankResidualCeiling p β s t N := by
      unfold rankResidualCeiling
      exact mul_le_mul_of_nonneg_left (add_le_add ht hs) β.coe_nonneg

theorem exists_actual_force_trace_memory_residual (hN : 0<N) (hp : 3≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    ∃ Ut : WaitingTime t × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),
    ∃ Us : WaitingTime s × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),
      StronglyMeasurable Ut ∧ StronglyMeasurable Us ∧
      (∀ r q (hx : OnSphere q.2),(fun ω => Ut (r,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (t+1) (t-r) q hx)) ∧
      (∀ r q (hx : OnSphere q.2),(fun ω => Us (r,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (s+1) (s-r) q hx)) ∧
      |meanForce (p := p) D₀ β R hR s t-
        ((β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*hessianMemory D₀ β R hR t s Ut+
          (β : ℝ)*(p : ℝ)*crossMemory D₀ β R hR s t Us)|≤rankResidualCeiling p β s t N := by
  obtain ⟨Ut,hUt,hUts,_⟩ := exists_actual_fixedTerminal_matrix (p := p) hN (by omega) D₀ β R hR hNR t
  obtain ⟨Us,hUs,hUss,_⟩ := exists_actual_fixedTerminal_matrix (p := p) hN (by omega) D₀ β R hR hNR s
  exact ⟨Ut,Us,hUt,hUs,hUts,hUss,
    actual_force_trace_memory_residual_le hN hp D₀ β R hR hNR s t Ut hUt hUts Us hUs hUss⟩

lemma sqrt_mul_div_self (a b : ℝ) (ha : 0≤a) :
    Real.sqrt (a*b)/a=Real.sqrt (b/a) := by
  rw [Real.sqrt_mul ha,Real.sqrt_div' _ ha]
  rw [show Real.sqrt a*Real.sqrt b/a=(Real.sqrt a/a)*Real.sqrt b by ring,
    Real.sqrt_div_self]
  simp only [div_eq_mul_inv]
  ring

theorem rankResidualCeiling_tendsto_zero (p : ℕ) (β s t : ℝ≥0) :
    Tendsto (fun n : ℕ => rankResidualCeiling p β s t (n+3)) atTop (𝓝 0) := by
  have hlim (A : ℝ) : Tendsto (fun n : ℕ => Real.sqrt (A/((n+3 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ((tendsto_add_atTop_iff_nat 3).mpr
      (tendsto_const_div_atTop_nhds_zero_nat A)).sqrt
  have hh := ((hlim (1+annealedFourthConstant p β t)).const_mul
    ((p : ℝ)*((p : ℝ)-1)^2*(t : ℝ))).add
      ((hlim (1+annealedFourthConstant p β s)).const_mul ((p : ℝ)*((p : ℝ)-1)*(s : ℝ)))
  have hhβ := hh.const_mul (β : ℝ)
  convert hhβ using 1
  · funext n
    unfold rankResidualCeiling
    rw [show (p : ℝ)*((p : ℝ)-1)^2/((n+3 : ℕ) : ℝ)*
      ((t : ℝ)*Real.sqrt (((n+3 : ℕ) : ℝ)*(1+annealedFourthConstant p β t)))=
      (p : ℝ)*((p : ℝ)-1)^2*(t : ℝ)*
        (Real.sqrt (((n+3 : ℕ) : ℝ)*(1+annealedFourthConstant p β t))/((n+3 : ℕ) : ℝ)) by ring,
      show (p : ℝ)*((p : ℝ)-1)/((n+3 : ℕ) : ℝ)*
      ((s : ℝ)*Real.sqrt (((n+3 : ℕ) : ℝ)*(1+annealedFourthConstant p β s)))=
      (p : ℝ)*((p : ℝ)-1)*(s : ℝ)*
        (Real.sqrt (((n+3 : ℕ) : ℝ)*(1+annealedFourthConstant p β s))/((n+3 : ℕ) : ℝ)) by ring,
      sqrt_mul_div_self _ _ (Nat.cast_nonneg _),sqrt_mul_div_self _ _ (Nat.cast_nonneg _)]
  · simp

end SphericalAging.ActualAnnealedCorrelationMemory
