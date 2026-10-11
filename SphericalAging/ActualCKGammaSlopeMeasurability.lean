module

public import SphericalAging.ActualGammaJointKernel
public import SphericalAging.ActualCKGammaSlopeResidual
public import SphericalAging.ActualCKCorrelationSlopeMeasurability

public section

/-! Genuine joint-time CK Γ memory and slope measurability. Varying
waiting-time domains are represented by a measurable causal indicator
against one fixed nonnegative-time Lebesgue measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKGammaSlopeMeasurability
open HardSphereDynamics FiniteModel ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualGammaJointKernel ActualCorrelationJointKernel ActualResponseJointKernel ActualResponseJointEnvelope
  ActualBrownianMemoryMeanReplacement ActualCKGammaSlopeResidual ActualCKMultiplierResidual
  ActualCKCorrelationSlopeMeasurability AnnealedHamiltonianEnergyStein ActualResponseCoefficientIntegral
  TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction ActualResponseKernel ActualPhysicalBrownianPairing
  AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def gammaMemoryField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (n : ℕ)
    (q : (ℝ≥0×ℝ≥0)×ℝ≥0) : ℝ :=
  if 0<q.2 ∧ q.2≤q.1.1 then
    (correlationPair (N := N) (p := p) β R hR q.2 q.1.1)^n*
      annealedGammaPair (N := N) (p := p) β R hR q.2 q.1.2*
        responseMeanPair (N := N) (p := p) β R hR q.1.1 q.2 else 0

lemma gammaMemoryField_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (n : ℕ) :
    StronglyMeasurable (gammaMemoryField (N := N) (p := p) β R hR n) := by
  have hC : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 =>
      correlationPair (N := N) (p := p) β R hR q.2 q.1.1) :=
    (correlationPair_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
      (g := fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 => (q.2,q.1.1)) (by fun_prop)
  have hG : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 =>
      annealedGammaPair (N := N) (p := p) β R hR q.2 q.1.2) :=
    (annealedGammaPair_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
      (g := fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 => (q.2,q.1.2)) (by fun_prop)
  have hRk : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 =>
      responseMeanPair (N := N) (p := p) β R hR q.1.1 q.2) :=
    (responseMeanPair_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
      (g := fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 => (q.1.1,q.2)) (by fun_prop)
  have hs : MeasurableSet {q : (ℝ≥0×ℝ≥0)×ℝ≥0 | 0<q.2 ∧ q.2≤q.1.1} := by
    exact (measurableSet_lt (f := fun _q : (ℝ≥0×ℝ≥0)×ℝ≥0 => (0 : ℝ≥0)) measurable_const
      (by fun_prop)).inter (measurableSet_le (f := fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 => q.2)
        (g := fun q => q.1.1) (by fun_prop) (by fun_prop))
  classical
  let b := fun q : (ℝ≥0×ℝ≥0)×ℝ≥0 => (correlationPair (N := N) (p := p) β R hR q.2 q.1.1)^n*
    annealedGammaPair (N := N) (p := p) β R hR q.2 q.1.2*
      responseMeanPair (N := N) (p := p) β R hR q.1.1 q.2
  have he : gammaMemoryField (N := N) (p := p) β R hR n=
      {q : (ℝ≥0×ℝ≥0)×ℝ≥0 | 0<q.2 ∧ q.2≤q.1.1}.indicator b := by
    funext q
    simp only [gammaMemoryField,Set.indicator,mem_setOf_eq,b]
  rw [he]
  exact (((hC.pow n).mul hG).mul hRk).indicator hs

@[expose] def jointGammaMemory (β R : ℝ≥0) (hR : 0<(R : ℝ)) (n : ℕ) (H S : ℝ≥0) : ℝ :=
  ∫ r,gammaMemoryField (N := N) (p := p) β R hR n ((H,S),r) ∂nonnegativeLebesgueMeasure

 theorem deterministicGammaMemory_eq_joint (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0) (n : ℕ) :
    deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR H S n=
      jointGammaMemory (N := N) (p := p) β R hR n H S := by
  classical
  calc
    _=∫ r : WaitingTime H,(correlationPair (N := N) (p := p) β R hR r H)^n*
      annealedGammaPair (N := N) (p := p) β R hR r S*
        responseMeanPair (N := N) (p := p) β R hR H r ∂waitingMeasure H := by
      unfold deterministicGammaMemory
      apply integral_congr_ae
      exact .of_forall (fun r => by
        dsimp only
        rw [responseMeanPair_eq_annealedResponse hN hp β R hR hNR H r]
        rfl)
    _=∫ r in Ioc (0 : ℝ≥0) H,(correlationPair (N := N) (p := p) β R hR r H)^n*
      annealedGammaPair (N := N) (p := p) β R hR r S*
        responseMeanPair (N := N) (p := p) β R hR H r ∂nonnegativeLebesgueMeasure :=
      by simpa only [FourPapersCommon.FilteredBrownian.finiteTimeMeasure] using
        waiting_integral H (fun r => (correlationPair (N := N) (p := p) β R hR r H)^n*
          annealedGammaPair (N := N) (p := p) β R hR r S*
            responseMeanPair (N := N) (p := p) β R hR H r)
    _=_ := by
      symm
      unfold jointGammaMemory gammaMemoryField
      simpa only [indicator,mem_Ioc] using integral_indicator (μ := nonnegativeLebesgueMeasure)
        (s := Ioc (0 : ℝ≥0) H) (f := fun r => (correlationPair (N := N) (p := p) β R hR r H)^n*
          annealedGammaPair (N := N) (p := p) β R hR r S*
            responseMeanPair (N := N) (p := p) β R hR H r) measurableSet_Ioc

lemma deterministicGammaMemory_stronglyMeasurable (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (n : ℕ) :
    StronglyMeasurable (fun z : ℝ≥0×ℝ≥0 => deterministicGammaMemory (p := p) (by omega : N≠0)
      β R hR hNR z.1 z.2 n) := by
  have hm := (gammaMemoryField_stronglyMeasurable (N := N) (p := p) β R hR n).integral_prod_right'
    (ν := nonnegativeLebesgueMeasure)
  convert hm using 1
  funext z
  exact deterministicGammaMemory_eq_joint hN hp β R hR hNR z.1 z.2 n

 theorem ckGammaSlope_stronglyMeasurable (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0) :
    StronglyMeasurable (Function.uncurry (ckGammaSlope (by omega : N≠0) p β)) := by
  have hG := annealedGammaPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)
  have hm := meanMemory_stronglyMeasurable hN (by omega : 2≤p) β
  have hM : StronglyMeasurable (fun z : ℝ≥0×ℝ≥0 =>
      1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (by omega : N≠0) p β z.1) :=
    stronglyMeasurable_const.add ((hm.const_mul ((β : ℝ)^2*(p : ℝ)^2)).comp_fst)
  have hmem := deterministicGammaMemory_stronglyMeasurable hN (by omega : 2≤p) β (N+1)
    (modelRadius_pos N) (modelRadius_sq N) (p-2)
  convert (hM.neg.mul hG).add (hmem.const_mul ((β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ))) using 1
  funext z
  simp only [ckGammaSlope,Function.uncurry,Pi.add_apply,Pi.mul_apply,Pi.neg_apply]

end SphericalAging.ActualCKGammaSlopeMeasurability
