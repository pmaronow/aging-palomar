module

public import SphericalAging.ActualCanonicalMeanKernelExtraction
public import SphericalAging.ActualResponseCompactEnvelope
public import SphericalAging.ActualCompactCKMemoryLimit

public section

/-! Actual uniform response bounds combine with equicontinuity to give
joint compact extraction of the literal C/Γ/R kernels. Equicontinuity is
an explicit analytic hypothesis of this auxiliary module. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualResponseKernelCompactExtraction
open ActualMeanKernelExtraction ActualCanonicalMeanKernelExtraction ActualCompactCKMemoryLimit
  ActualResponsePrimitiveInterchange ActualResponseCompactEnvelope GaussianLandscapeMoments
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

 theorem actual_response_compact_subsequence (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hp : 2≤p) (β : ℝ≥0)
    (hEqui : Equicontinuous (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β))) :
    ∃r : C(ℝ≥0×ℝ≥0,ℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀K : Set (ℝ≥0×ℝ≥0),IsCompact K→TendstoUniformlyOn
        (fun n => Function.uncurry (modelResponse (N := dim (φ n)) (p := p) β)) r atTop K := by
  let F : ℕ→C(ℝ≥0×ℝ≥0,ℝ) := fun n =>
    ⟨Function.uncurry (modelResponse (N := dim n) (p := p) β),hEqui.continuous n⟩
  exact pointwise_bounded_equicontinuous_subsequence F
    (fun z => momentCeiling p ((β : ℝ)*(p : ℝ)^2*(z.1 : ℝ)))
    (fun n z => modelResponse_abs_le_compact (hD n) hp β z.1 z.1 z.2 le_rfl) hEqui

 theorem actual_correlation_gamma_response_common_subsequence (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hp : 2≤p) (β : ℝ≥0)
    (hEqui : Equicontinuous (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β))) :
    ∃c g r : C(ℝ≥0×ℝ≥0,ℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀K : Set (ℝ≥0×ℝ≥0),IsCompact K→
        TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim (φ n)) p β)) c atTop K ∧
        TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim (φ n)) p β)) g atTop K ∧
        TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := dim (φ n)) (p := p) β)) r atTop K := by
  obtain ⟨c,g,φ,hφ,hCg⟩ := actual_canonical_means_common_subsequence dim
    (fun n => by have := hD n;omega) p (by omega) β
  obtain ⟨r,ψ,hψ,hR⟩ := actual_response_compact_subsequence (dim ∘ φ)
    (fun n => hD (φ n)) hp β (hEqui.comp φ)
  refine ⟨c,g,r,φ ∘ ψ,hφ.comp hψ,?_⟩
  intro K hK
  exact ⟨(hCg K hK).1.seq_tendstoUniformlyOn ψ hψ.tendsto_atTop,
    (hCg K hK).2.seq_tendstoUniformlyOn ψ hψ.tendsto_atTop,hR K hK⟩

end SphericalAging.ActualResponseKernelCompactExtraction
