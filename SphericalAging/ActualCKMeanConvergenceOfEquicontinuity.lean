module

public import SphericalAging.ActualResponseKernelCompactExtraction
public import SphericalAging.ActualCKKernelLimitUniqueness
public import SphericalAging.UniformKernelSubsequenceCriterion

public section

/-! True finite-N CK closure and uniqueness turn actual response
 equicontinuity into whole-sequence compact convergence of all three
annealed kernels. Response equicontinuity is an explicit hypothesis of this auxiliary result. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualCKMeanConvergenceOfEquicontinuity
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualResponseKernelCompactExtraction
  ActualCKKernelLimitUniqueness ActualResponsePrimitiveInterchange UniformKernelSubsequenceCriterion
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

 theorem square_isCompact (T : ℝ≥0) : IsCompact (square T) := by
  have he : square T=Icc (0 : ℝ≥0) T ×ˢ Icc (0 : ℝ≥0) T := by
    ext z
    simp only [square,mem_setOf_eq,mem_prod,mem_Icc,zero_le,true_and]
  rw [he]
  exact isCompact_Icc.prod isCompact_Icc

 theorem triangle_subset_square (T : ℝ≥0) : triangle T⊆square T :=
  fun z hz => ⟨hz.2,hz.1.trans hz.2⟩

 theorem actual_ck_means_identified_subsubsequence (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hD : ∀n,3≤dim n) (hp : 3≤p)
    (β : ℝ≥0) (hβ : 0<β)
    (hEqui : Equicontinuous (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β)))
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d)
    (φ : ℕ→ℕ) (hφ : StrictMono φ) :
    ∃ψ : ℕ→ℕ,StrictMono ψ ∧ ∀T : ℝ≥0,
      TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim (φ (ψ n))) p β))
        (fun z : ℝ≥0×ℝ≥0 => d.C z.1 z.2) atTop (square T) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim (φ (ψ n))) p β))
        (fun z : ℝ≥0×ℝ≥0 => ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2) atTop (square T) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := dim (φ (ψ n))) (p := p) β))
        (fun z : ℝ≥0×ℝ≥0 => d.R z.1 z.2) atTop (triangle T) := by
  obtain ⟨c,g,r,ψ,hψ,hLim⟩ := actual_correlation_gamma_response_common_subsequence
    (dim ∘ φ) (fun n => hD (φ n)) (by omega : 2≤p) β (hEqui.comp φ)
  let D := fun n => dim (φ (ψ n))
  have hDC : ∀T,TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (D n) p β))
      c atTop (square T) := fun T => (hLim (square T) (square_isCompact T)).1
  have hDG : ∀T,TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (D n) p β))
      g atTop (square T) := fun T => (hLim (square T) (square_isCompact T)).2.1
  have hDR : ∀T,TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := D n) (p := p) β))
      r atTop (triangle T) := fun T => (hLim (square T) (square_isCompact T)).2.2.mono (triangle_subset_square T)
  have he := actual_ck_kernel_limit_identification (C := fun t s => c (t,s))
    (G := fun t s => g (t,s)) (R := fun t s => r (t,s)) D (hdim.comp (hφ.comp hψ).tendsto_atTop)
      (fun n => hD (φ (ψ n))) hp β hβ hDC hDG hDR c.continuous g.continuous r.continuous hd
  refine ⟨ψ,hψ,?_⟩
  intro T
  refine ⟨(hDC T).congr_right (fun z _ => he.1 z.1 z.2),
    (hDG T).congr_right (fun z _ => he.2.2 z.1 z.2),?_⟩
  exact (hDR T).congr_right (fun z hz => he.2.1 z.1 z.2 hz.1)

 theorem actual_ck_means_uniform_limit_of_response_equicontinuity (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hD : ∀n,3≤dim n) (hp : 3≤p)
    (β : ℝ≥0) (hβ : 0<β)
    (hEqui : Equicontinuous (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β)))
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim n) p β))
      (fun z : ℝ≥0×ℝ≥0 => d.C z.1 z.2) atTop (square T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim n) p β))
      (fun z : ℝ≥0×ℝ≥0 => ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2) atTop (square T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β))
      (fun z : ℝ≥0×ℝ≥0 => d.R z.1 z.2) atTop (triangle T) := by
  constructor
  · apply uniform_limit_of_subsubsequence
    intro φ hφ
    obtain ⟨ψ,hψ,hLim⟩ := actual_ck_means_identified_subsubsequence dim hdim hD hp β hβ hEqui d hd φ hφ
    exact ⟨ψ,hψ,(hLim T).1⟩
  constructor
  · apply uniform_limit_of_subsubsequence
    intro φ hφ
    obtain ⟨ψ,hψ,hLim⟩ := actual_ck_means_identified_subsubsequence dim hdim hD hp β hβ hEqui d hd φ hφ
    exact ⟨ψ,hψ,(hLim T).2.1⟩
  · apply uniform_limit_of_subsubsequence
    intro φ hφ
    obtain ⟨ψ,hψ,hLim⟩ := actual_ck_means_identified_subsubsequence dim hdim hD hp β hβ hEqui d hd φ hφ
    exact ⟨ψ,hψ,(hLim T).2.2⟩

end SphericalAging.ActualCKMeanConvergenceOfEquicontinuity
