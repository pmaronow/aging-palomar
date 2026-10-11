module

public import SphericalAging.ActualCKMemoryJointMeasurability

public section

/-! Simultaneous measurability of the true finite-N deterministic CK
correlation slope assembled from the actual mean kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKCorrelationSlopeMeasurability
open HardSphereDynamics FiniteModel ActualSphereTransition ActualAnnealedCorrelationIntegral
  ActualCKMemoryJointMeasurability ActualCKCorrelationForceResidual ActualCKMultiplierResidual
  ActualCKCorrelationSlopeResidual AnnealedHamiltonianEnergyStein ActualMixedOverlapMean
  ActualPhysicalBrownianPairing ActualResponseKernel ActualCorrelationJointKernel
  ActualFiniteHorizonTraceReplacement ActualMixedResponseTraceContraction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma meanMemory_eq_deterministicMemory (hN : N≠0) (β : ℝ≥0) (H : ℝ≥0) :
    meanMemory hN p β H=deterministicMemory (p := p) hN β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) H H H (p-1) 0 := by
  unfold meanMemory deterministicMemory
  simp only [pow_zero,mul_one]
  rfl

lemma meanMemory_stronglyMeasurable (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0) :
    StronglyMeasurable (meanMemory (by omega : N≠0) p β) := by
  have hm := (deterministicMemory_stronglyMeasurable hN hp β (N+1)
    (modelRadius_pos N) (modelRadius_sq N) (p-1) 0).comp_measurable
      (measurable_id.prodMk (measurable_id.prodMk measurable_id))
  convert hm using 1
  funext H
  exact meanMemory_eq_deterministicMemory (by omega : N≠0) β H

 theorem ckCorrelationSlope_stronglyMeasurable (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0) :
    StronglyMeasurable (Function.uncurry (ckCorrelationSlope (by omega : N≠0) p β)) := by
  have hC := correlationPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)
  have hm := meanMemory_stronglyMeasurable hN (by omega : 2≤p) β
  have hMt : StronglyMeasurable (fun z : ℝ≥0×ℝ≥0 =>
      1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (by omega : N≠0) p β z.2) := by
    exact stronglyMeasurable_const.add ((hm.const_mul ((β : ℝ)^2*(p : ℝ)^2)).comp_snd)
  have htm := (deterministicMemory_stronglyMeasurable hN (by omega : 2≤p) β (N+1)
    (modelRadius_pos N) (modelRadius_sq N) (p-2) 1).comp_measurable
      (measurable_snd.prodMk (measurable_snd.prodMk measurable_fst))
  have hsm := (deterministicMemory_stronglyMeasurable hN (by omega : 2≤p) β (N+1)
    (modelRadius_pos N) (modelRadius_sq N) (p-1) 0).comp_measurable
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))
  convert (((hMt.neg.mul hC).add (htm.const_mul ((β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ)))).add
    (hsm.const_mul ((β : ℝ)^2*(p : ℝ)))) using 1
  funext z
  simp only [ckCorrelationSlope,Function.uncurry,Function.comp_apply,Pi.add_apply,Pi.mul_apply,Pi.neg_apply]

end SphericalAging.ActualCKCorrelationSlopeMeasurability
