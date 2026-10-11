module

public import SphericalAging.ActualCompactCKMemoryLimit

public section

/-! Symmetry and diagonal normalization of compact limits of the literal
annealed hard-sphere correlation kernels. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualCompactCorrelationProperties
open ActualCompactCKMemoryLimit CompactKernelMemoryLimit ActualAnnealedCorrelationIntegral
  AnnealedHamiltonianEnergyStein FiniteCorrelationIto
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem modelCorrelation_symm (β : ℝ≥0) (s t : ℝ≥0) :
    modelCorrelation N p β s t=modelCorrelation N p β t s := by
  unfold modelCorrelation correlationPair
  congr 1
  funext q
  simp only [overlap,real_inner_comm]

 theorem modelCorrelation_diag (hN : 1≤N) (hp : 0<p) (β : ℝ≥0) (t : ℝ≥0) :
    modelCorrelation N p β t t=1 := by
  simpa only [modelCorrelation,intervalIntegral.integral_same,add_zero] using
    actual_annealed_correlation_integral (N := N) (p := p) (by omega : 0<N) hp β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) t t le_rfl

 theorem compact_correlation_limit_symm {A : Type*} {L : Filter A} [NeBot L]
    (dim : A→ℕ) (β T : ℝ≥0) {C : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T)) {s t : ℝ≥0} (hs : s≤T) (ht : t≤T) :
    C s t=C t s := by
  have hst := hC.tendsto_at (x := (s,t)) ⟨hs,ht⟩
  have hts := hC.tendsto_at (x := (t,s)) ⟨ht,hs⟩
  exact tendsto_nhds_unique hst (hts.congr (fun j => modelCorrelation_symm (N := dim j) (p := p) β t s))

 theorem compact_correlation_limit_diag {A : Type*} {L : Filter A} [NeBot L]
    (dim : A→ℕ) (hD : ∀j,1≤dim j) (hp : 0<p) (β T : ℝ≥0) {C : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T)) {t : ℝ≥0} (ht : t≤T) : C t t=1 := by
  have hh := hC.tendsto_at (x := (t,t)) ⟨ht,ht⟩
  exact tendsto_nhds_unique hh (tendsto_const_nhds.congr
    (fun j => (modelCorrelation_diag (hD j) hp β t).symm))

end SphericalAging.ActualCompactCorrelationProperties
