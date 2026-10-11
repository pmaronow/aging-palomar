module

public import SphericalAging.ActualCompactCKMemoryLimit
public import SphericalAging.ActualCKMeanMemoryCompactBound
public import SphericalAging.UniformBoundedKernelOperations

public section

/-! Actual uniform kernel convergence forces both nonlinear CK slope
limits. No multiplier, memory, or slope convergence is retained as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCompactCKSlopeLimit
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualCKMeanMemoryCompactBound
  UniformBoundedKernelOperations UniformCausalMemoryIntegration
  ActualResponsePrimitiveInterchange ActualCKMultiplierResidual ActualCKCorrelationSlopeResidual
  ActualCKGammaSlopeResidual ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualGammaEnergyFactorization AnnealedHamiltonianEnergyStein GaussianLandscapeMoments
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose]  def effectiveMultiplier (p : ℕ) (β : ℝ≥0) (C R : Kernel) (t : ℝ≥0) : ℝ :=
  1+(β : ℝ)^2*(p : ℝ)^2*correlationMemory C R (p-1) 0 (t,t,t)

@[expose]  def correlationSlope (p : ℕ) (β : ℝ≥0) (C R : Kernel) (s t : ℝ≥0) : ℝ :=
  -effectiveMultiplier p β C R t*C s t+
    (β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ)*correlationMemory C R (p-2) 1 (t,t,s)+
    (β : ℝ)^2*(p : ℝ)*correlationMemory C R (p-1) 0 (s,t,t)

@[expose]  def gammaSlope (p : ℕ) (β : ℝ≥0) (C G R : Kernel) (t s : ℝ≥0) : ℝ :=
  -effectiveMultiplier p β C R t*G t s+
    (β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ)*gammaMemory C G R (p-2) (t,t,s)

@[expose]  def multiplierCeiling (p : ℕ) (β T : ℝ≥0) : ℝ :=
  1+(β : ℝ)^2*(p : ℝ)^2*(T : ℝ)*momentCeiling p ((β : ℝ)*(p : ℝ)^2*(T : ℝ))

variable {A : Type*} {L : Filter A} [NeBot L] {p : ℕ}

 theorem actual_effective_multiplier_abs_le (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hp : 2≤p) (β T : ℝ≥0) (j : A) (t : ℝ≥0) (ht : t≤T) :
    |1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (N := dim j) (by have := hD j;omega) p β t|≤
      multiplierCeiling p β T := by
  have hk : 0≤(β : ℝ)^2*(p : ℝ)^2 := by positivity
  calc
    _≤|1|+|(β : ℝ)^2*(p : ℝ)^2*meanMemory (N := dim j) (by have := hD j;omega) p β t| := abs_add_le _ _
    _=1+(β : ℝ)^2*(p : ℝ)^2*|meanMemory (N := dim j) (by have := hD j;omega) p β t| := by
      rw [abs_one,abs_mul,abs_of_nonneg hk]
    _≤1+(β : ℝ)^2*(p : ℝ)^2*((T : ℝ)*momentCeiling p ((β : ℝ)*(p : ℝ)^2*(T : ℝ))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (actual_meanMemory_abs_le (hD j) hp β T t ht) hk)
    _=_ := by unfold multiplierCeiling;ring

 theorem actual_effective_multiplier_uniform_limit (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hp : 2≤p) (β T : ℝ≥0) {C R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R)) :
    TendstoUniformlyOn (fun j t => 1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (N := dim j)
      (by have := hD j;omega) p β t) (effectiveMultiplier p β C R) L (Iic T) := by
  have hm := actual_meanMemory_uniform_limit dim hD hp β T hC hR hCc hRc
  have hmul := (Real.uniformContinuous_const_mul (x := (β : ℝ)^2*(p : ℝ)^2)).comp_tendstoUniformlyOn hm
  have hconst : TendstoUniformlyOn (fun _j : A => fun _t : ℝ≥0 => (1 : ℝ)) (fun _ => 1) L (Iic T) :=
    tendsto_const_nhds.tendstoUniformlyOn_const (Iic T)
  exact hconst.add hmul

 theorem actual_correlation_slope_uniform_limit (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β T : ℝ≥0) {C R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R)) :
    TendstoUniformlyOn (fun j => Function.uncurry (ckCorrelationSlope (N := dim j)
      (by have := hD j;omega) p β)) (Function.uncurry (correlationSlope p β C R)) L (square T) := by
  have hμ := (actual_effective_multiplier_uniform_limit dim hD (by omega : 2≤p) β T hC hR hCc hRc).comp
    (fun z : ℝ≥0×ℝ≥0 => z.2)
  have hμsq := hμ.mono (show square T⊆{z | z.2∈Iic T} from fun z hz => hz.2)
  have hcB := uniform_limit_abs_bound hC (fun j z hz =>
    correlationPair_abs_le_one (by have := hD j;omega) β (dim j+1)
      (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) z.1 z.2)
  have hprod := uniform_mul_of_bounds (show 0≤multiplierCeiling p β T by unfold multiplierCeiling momentCeiling;positivity)
    (by norm_num : (0 : ℝ)≤1) hμsq.neg hC
    (fun j z hz => by simpa only [Pi.neg_apply, Function.comp_apply, abs_neg] using actual_effective_multiplier_abs_le dim hD (by omega : 2≤p) β T j z.2 hz.2) hcB
  have hmem1 := (actual_correlation_memory_uniform_limit dim hD (by omega : 2≤p) β T hC hR hCc hRc (p-2) 1).comp
    (fun z : ℝ≥0×ℝ≥0 => (z.2,z.2,z.1))
  have hm1 := hmem1.mono (show square T⊆{z | (z.2,z.2,z.1)∈timeCube T} from fun z hz => ⟨hz.2,hz.2,hz.1⟩)
  have hmem2 := (actual_correlation_memory_uniform_limit dim hD (by omega : 2≤p) β T hC hR hCc hRc (p-1) 0).comp
    (fun z : ℝ≥0×ℝ≥0 => (z.1,z.2,z.2))
  have hm2 := hmem2.mono (show square T⊆{z | (z.1,z.2,z.2)∈timeCube T} from fun z hz => ⟨hz.1,hz.2,hz.2⟩)
  have hscaled1 := (Real.uniformContinuous_const_mul (x := (β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ))).comp_tendstoUniformlyOn hm1
  have hscaled2 := (Real.uniformContinuous_const_mul (x := (β : ℝ)^2*(p : ℝ))).comp_tendstoUniformlyOn hm2
  exact (hprod.add hscaled1).add hscaled2

 theorem actual_gamma_slope_uniform_limit (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β T : ℝ≥0) {C G R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hG : TendstoUniformlyOn (fun j => Function.uncurry (modelGamma (dim j) p β))
      (Function.uncurry G) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hGc : Continuous (Function.uncurry G))
    (hRc : Continuous (Function.uncurry R)) :
    TendstoUniformlyOn (fun j => Function.uncurry (ckGammaSlope (N := dim j)
      (by have := hD j;omega) p β)) (Function.uncurry (gammaSlope p β C G R)) L (square T) := by
  have hμ := (actual_effective_multiplier_uniform_limit dim hD (by omega : 2≤p) β T hC hR hCc hRc).comp
    (fun z : ℝ≥0×ℝ≥0 => z.1)
  have hμsq := hμ.mono (show square T⊆{z | z.1∈Iic T} from fun z hz => hz.1)
  have hgB := uniform_limit_abs_bound hG (fun j z hz =>
    (annealedGammaPair_abs_le (by have := hD j;omega) β (dim j+1) (modelRadius_pos (dim j))
      (modelRadius_sq (dim j)) z.1 z.2).trans
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (show (z.2 : ℝ)≤T from hz.2) (by norm_num))))
  have hprod := uniform_mul_of_bounds (show 0≤multiplierCeiling p β T by unfold multiplierCeiling momentCeiling;positivity)
    (Real.sqrt_nonneg ((T : ℝ)/2)) hμsq.neg hG
    (fun j z hz => by simpa only [Pi.neg_apply, Function.comp_apply, abs_neg] using actual_effective_multiplier_abs_le dim hD (by omega : 2≤p) β T j z.1 hz.1) hgB
  have hmem := (actual_gamma_memory_uniform_limit dim hD (by omega : 2≤p) β T hC hG hR hCc hGc hRc (p-2)).comp
    (fun z : ℝ≥0×ℝ≥0 => (z.1,z.1,z.2))
  have hm := hmem.mono (show square T⊆{z | (z.1,z.1,z.2)∈timeCube T} from fun z hz => ⟨hz.1,hz.1,hz.2⟩)
  have hscaled := (Real.uniformContinuous_const_mul (x := (β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ))).comp_tendstoUniformlyOn hm
  exact hprod.add hscaled

end SphericalAging.ActualCompactCKSlopeLimit
