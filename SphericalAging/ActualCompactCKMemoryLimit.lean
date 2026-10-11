module

public import SphericalAging.CompactKernelMemoryLimit
public import SphericalAging.ActualCKMemoryIntervalIntegrability

public section

/-! Nonlinear memory convergence for literal finite-dimensional CK kernels.
Only uniform preceding kernel limits enter; all finite-N mean bounds and
integrability are discharged from the actual stochastic model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCompactCKMemoryLimit
open CompactKernelMemoryLimit ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualResponsePrimitiveInterchange ActualResponseCompactEnvelope ActualCKMemoryRealIntegral
  ActualCKMemoryIntervalIntegrability ActualCKCorrelationSlopeResidual ActualGammaEnergyFactorization
  ActualCKCorrelationForceResidual ActualBrownianMemoryMeanReplacement ActualCKMultiplierResidual
  ActualCKCorrelationSlopeMeasurability AnnealedHamiltonianEnergyStein GaussianLandscapeMoments
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def modelCorrelation (N p : ℕ) (β : ℝ≥0) : Kernel :=
  correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N)

@[expose] def modelGamma (N p : ℕ) (β : ℝ≥0) : Kernel :=
  annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N)

variable {A : Type*} {L : Filter A} [NeBot L] {p : ℕ}

 theorem actual_correlation_memory_uniform_limit (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hp : 2≤p) (β T : ℝ≥0) {C R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R)) (n m : ℕ) :
    TendstoUniformlyOn (fun j => fun z : Times => deterministicMemory (p := p)
      (by have := hD j;omega) β (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j))
        z.1 z.2.1 z.2.2 n m) (correlationMemory C R n m) L (timeCube T) := by
  have hlim := correlationMemory_uniform_limit (Q := momentCeiling p ((β : ℝ)*(p : ℝ)^2*(T : ℝ)))
    (by unfold momentCeiling;positivity) hC hR
    (fun j z hz => correlationPair_abs_le_one (by have := hD j;omega)
      β (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) z.1 z.2)
    (fun j z hz => modelResponse_abs_le_compact (hD j) hp β T z.1 z.2 hz.2)
    hCc hRc n m (fun j z hz => actual_correlation_memory_intervalIntegrable (hD j) hp β z.1 z.2.1 z.2.2 n m)
  apply hlim.congr
  exact Eventually.of_forall (fun j z hz => (deterministicMemory_eq_interval (hD j) hp β
    (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) z.1 z.2.1 z.2.2 n m).symm)

 theorem actual_gamma_memory_uniform_limit (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hp : 2≤p) (β T : ℝ≥0) {C G R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hG : TendstoUniformlyOn (fun j => Function.uncurry (modelGamma (dim j) p β))
      (Function.uncurry G) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hGc : Continuous (Function.uncurry G))
    (hRc : Continuous (Function.uncurry R)) (n : ℕ) :
    TendstoUniformlyOn (fun j => fun z : Times => deterministicGammaMemory (p := p)
      (by have := hD j;omega) β (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) z.1 z.2.2 n)
      (gammaMemory C G R n) L (timeCube T) := by
  have hlim := gammaMemory_uniform_limit (B := Real.sqrt ((T : ℝ)/2))
    (Q := momentCeiling p ((β : ℝ)*(p : ℝ)^2*(T : ℝ))) (Real.sqrt_nonneg _)
    (by unfold momentCeiling;positivity) hC hG hR
    (fun j z hz => correlationPair_abs_le_one (by have := hD j;omega)
      β (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) z.1 z.2)
    (fun j z hz => (annealedGammaPair_abs_le (by have := hD j;omega) β (dim j+1)
      (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) z.1 z.2).trans
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (show (z.2 : ℝ)≤T from hz.2) (by norm_num))))
    (fun j z hz => modelResponse_abs_le_compact (hD j) hp β T z.1 z.2 hz.2)
    hCc hGc hRc n (fun j z hz => actual_gamma_memory_intervalIntegrable (hD j) hp β z.1 z.2.2 n)
  apply hlim.congr
  exact Eventually.of_forall (fun j z hz => (deterministicGammaMemory_eq_interval (hD j) hp β
    (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) z.1 z.2.2 n).symm)

 theorem actual_meanMemory_uniform_limit (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hp : 2≤p) (β T : ℝ≥0) {C R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R)) :
    TendstoUniformlyOn (fun j H => meanMemory (N := dim j) (by have := hD j;omega) p β H)
      (fun H => correlationMemory C R (p-1) 0 (H,H,H)) L (Iic T) := by
  have hlim := (actual_correlation_memory_uniform_limit dim hD hp β T hC hR hCc hRc (p-1) 0).comp
    (fun H : ℝ≥0 => (H,H,H))
  have he := hlim.mono (show Iic T⊆{H | (H,H,H)∈timeCube T} from fun H hH => ⟨hH,hH,hH⟩)
  apply he.congr
  exact Eventually.of_forall (fun j H hH => (meanMemory_eq_deterministicMemory
    (N := dim j) (by have := hD j;omega) β H).symm)

end SphericalAging.ActualCompactCKMemoryLimit
