module

public import SphericalAging.ActualResponseJointEnvelope
public import SphericalAging.ActualCorrelationJointKernel

public section

/-! Genuine simultaneous measurability of the correlation/response CK
memories, obtained from a fixed time measure with a measurable causal cut. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKMemoryJointMeasurability
open HardSphereDynamics FiniteModel ActualSphereTransition ActualAnnealedCorrelationIntegral
  ActualResponseJointKernel ActualResponseJointEnvelope ActualCorrelationJointKernel
  ActualCKCorrelationForceResidual ActualCKMultiplierResidual ActualFiniteHorizonTraceReplacement
  TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction ActualResponseCoefficientIntegral
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] abbrev Times := ℝ≥0×ℝ≥0×ℝ≥0

@[expose] def memoryField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (n m : ℕ) (q : Times×ℝ≥0) : ℝ :=
  if 0<q.2 ∧ q.2≤q.1.1 then
    (correlationPair (N := N) (p := p) β R hR q.2 q.1.2.1)^n*
      (correlationPair (N := N) (p := p) β R hR q.2 q.1.2.2)^m*
        responseMeanPair (N := N) (p := p) β R hR q.1.1 q.2 else 0

lemma memoryField_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (n m : ℕ) :
    StronglyMeasurable (memoryField (N := N) (p := p) β R hR n m) := by
  have hA : StronglyMeasurable (fun q : Times×ℝ≥0 => correlationPair (N := N) (p := p) β R hR q.2 q.1.2.1) :=
    (correlationPair_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
      (g := fun q : Times×ℝ≥0 => (q.2,q.1.2.1)) (by fun_prop)
  have hS : StronglyMeasurable (fun q : Times×ℝ≥0 => correlationPair (N := N) (p := p) β R hR q.2 q.1.2.2) :=
    (correlationPair_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
      (g := fun q : Times×ℝ≥0 => (q.2,q.1.2.2)) (by fun_prop)
  have hRk : StronglyMeasurable (fun q : Times×ℝ≥0 => responseMeanPair (N := N) (p := p) β R hR q.1.1 q.2) :=
    (responseMeanPair_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
      (g := fun q : Times×ℝ≥0 => (q.1.1,q.2)) (by fun_prop)
  have hs : MeasurableSet {q : Times×ℝ≥0 | 0<q.2 ∧ q.2≤q.1.1} :=
    (measurableSet_lt (f := fun _q : Times×ℝ≥0 => (0 : ℝ≥0)) measurable_const
      (by fun_prop)).inter (measurableSet_le (f := fun q : Times×ℝ≥0 => q.2)
        (g := fun q => q.1.1) (by fun_prop) (by fun_prop))
  classical
  let b := fun q : Times×ℝ≥0 => (correlationPair (N := N) (p := p) β R hR q.2 q.1.2.1)^n*
    (correlationPair (N := N) (p := p) β R hR q.2 q.1.2.2)^m*
      responseMeanPair (N := N) (p := p) β R hR q.1.1 q.2
  have he : memoryField (N := N) (p := p) β R hR n m=
      {q : Times×ℝ≥0 | 0<q.2 ∧ q.2≤q.1.1}.indicator b := by
    funext q
    simp only [memoryField,Set.indicator,mem_setOf_eq,b]
  rw [he]
  exact ((hA.pow n).mul (hS.pow m) |>.mul hRk).indicator hs

@[expose] def jointMemory (β R : ℝ≥0) (hR : 0<(R : ℝ)) (n m : ℕ) (H A S : ℝ≥0) : ℝ :=
  ∫ r,memoryField (N := N) (p := p) β R hR n m ((H,A,S),r) ∂nonnegativeLebesgueMeasure

lemma jointMemory_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (n m : ℕ) :
    StronglyMeasurable (fun z : Times => jointMemory (N := N) (p := p) β R hR n m z.1 z.2.1 z.2.2) :=
  (memoryField_stronglyMeasurable β R hR n m).integral_prod_right'

 theorem deterministicMemory_eq_jointMemory (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H A S : ℝ≥0) (n m : ℕ) :
    deterministicMemory (p := p) (by omega : N≠0) β R hR hNR H A S n m=
      jointMemory (N := N) (p := p) β R hR n m H A S := by
  classical
  calc
    _=∫ r : WaitingTime H,(correlationPair (N := N) (p := p) β R hR r A)^n*
        (correlationPair (N := N) (p := p) β R hR r S)^m*
          responseMeanPair (N := N) (p := p) β R hR H r ∂waitingMeasure H := by
      unfold deterministicMemory
      apply integral_congr_ae
      exact .of_forall (fun r => by
        dsimp only
        rw [responseMeanPair_eq_annealedResponse hN hp β R hR hNR H r]
        rfl)
    _=∫ r in Ioc (0 : ℝ≥0) H,(correlationPair (N := N) (p := p) β R hR r A)^n*
        (correlationPair (N := N) (p := p) β R hR r S)^m*
          responseMeanPair (N := N) (p := p) β R hR H r ∂nonnegativeLebesgueMeasure :=
      by simpa only [FourPapersCommon.FilteredBrownian.finiteTimeMeasure] using
        waiting_integral H (fun r => (correlationPair (N := N) (p := p) β R hR r A)^n*
          (correlationPair (N := N) (p := p) β R hR r S)^m*responseMeanPair (N := N) (p := p) β R hR H r)
    _=_ := by
      symm
      unfold jointMemory memoryField
      simpa only [indicator,mem_Ioc] using integral_indicator (μ := nonnegativeLebesgueMeasure)
        (s := Ioc (0 : ℝ≥0) H)
        (f := fun r => (correlationPair (N := N) (p := p) β R hR r A)^n*
          (correlationPair (N := N) (p := p) β R hR r S)^m*responseMeanPair (N := N) (p := p) β R hR H r)
        measurableSet_Ioc

lemma deterministicMemory_stronglyMeasurable (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (n m : ℕ) :
    StronglyMeasurable (fun z : Times => deterministicMemory (p := p) (by omega : N≠0)
      β R hR hNR z.1 z.2.1 z.2.2 n m) := by
  convert jointMemory_stronglyMeasurable (N := N) (p := p) β R hR n m using 1
  funext z
  exact deterministicMemory_eq_jointMemory hN hp β R hR hNR z.1 z.2.1 z.2.2 n m

end SphericalAging.ActualCKMemoryJointMeasurability
