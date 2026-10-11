module

public import SphericalAging.ActualCKEnergyResidual
public import SphericalAging.ActualCompactCKMemoryLimit

public section

/-! Actual energy convergence follows from the actual correlation and
response limits. The finite-model error and every memory integrability
input are derived, including at beta zero. -/
noncomputable section
open Set Filter Topology
open scoped NNReal
namespace SphericalAging.ActualCKEnergyLimit
open ActualCKEnergyResidual ActualCKMultiplierResidual ActualCompactCKMemoryLimit
  CompactKernelMemoryLimit ActualResponsePrimitiveInterchange
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} {L : Filter A} [NeBot L] {p : ℕ}

/-- Uniform convergence of the literal actual energy on any compact
horizon, for every diverging dimension family. -/
theorem actual_energy_uniform_limit (dim : A→ℕ) (hD : ∀j,3≤dim j)
    (hTop : Tendsto dim L atTop) (hp : 2≤p) (β T : ℝ≥0) {C R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N:=dim j) (p:=p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R)) :
    TendstoUniformlyOn (fun j H => meanEnergy (dim j) p β H)
      (fun H => (β:ℝ)*(p:ℝ)*correlationMemory C R (p-1) 0 (H,H,H)) L (Iic T) := by
  have hm := actual_meanMemory_uniform_limit dim hD hp β T hC hR hCc hRc
  have hs := (Real.uniformContinuous_const_mul (x:=(β:ℝ)*(p:ℝ))).comp_tendstoUniformlyOn hm
  have he := energyResidualCeiling_tendsto_zero dim hTop p β (T+1)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hsmall := (tendsto_order.mp he).2 (ε/2) hh
  filter_upwards [hsmall,(Metric.tendstoUniformlyOn_iff.mp hs) (ε/2) hh] with j hj hjm H hH
  have hres := actual_energy_memory_residual_le (hD j) hp β H (T+1)
    (hH.trans (by simp)) (by positivity)
  have hmem := hjm H hH
  rw [Real.dist_eq,abs_sub_comm] at hmem ⊢
  simp only [Function.comp_apply] at hmem
  calc
    _≤|meanEnergy (dim j) p β H-(β:ℝ)*(p:ℝ)*meanMemory (by have := hD j;omega) p β H|+
      |(β:ℝ)*(p:ℝ)*meanMemory (by have := hD j;omega) p β H-
        (β:ℝ)*(p:ℝ)*correlationMemory C R (p-1) 0 (H,H,H)| := abs_sub_le _ _ _
    _<ε/2+ε/2 := add_lt_add (hres.trans_lt hj) hmem
    _=ε := by ring

end SphericalAging.ActualCKEnergyLimit
