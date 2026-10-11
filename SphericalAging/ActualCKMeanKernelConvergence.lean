module

public import SphericalAging.ActualResponseTimeEquicontinuity
public import SphericalAging.ActualCKMeanConvergenceOfEquicontinuity
public import SphericalAging.ActualMeanKernelDimensionTransfer
public import SphericalAging.CKGlobalExistence

public section

/-! Genuine whole-sequence compact convergence of the actual annealed
C/Γ/R kernels to the unique CK solution. All compactness and nonlinear
finite-dimensional closure inputs have been derived from the model. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualCKMeanKernelConvergence
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualResponseKernelCompactExtraction
  ActualCKMeanConvergenceOfEquicontinuity ActualMeanKernelDimensionTransfer
  ActualResponseTimeEquicontinuity ActualResponsePrimitiveInterchange
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

 theorem actual_kernels_common_subsequence (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hp : 2≤p) (β : ℝ≥0) :
    ∃c g r : C(ℝ≥0×ℝ≥0,ℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀K : Set (ℝ≥0×ℝ≥0),IsCompact K→
        TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim (φ n)) p β)) c atTop K ∧
        TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim (φ n)) p β)) g atTop K ∧
        TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := dim (φ n)) (p := p) β)) r atTop K :=
  actual_correlation_gamma_response_common_subsequence dim hD hp β
    (actual_modelResponse_equicontinuous dim hD hp β)

 theorem actual_ck_means_uniform_limit (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim n) p β))
      (fun z : ℝ≥0×ℝ≥0 => d.C z.1 z.2) atTop (square T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim n) p β))
      (fun z : ℝ≥0×ℝ≥0 => ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2) atTop (square T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β))
      (fun z : ℝ≥0×ℝ≥0 => d.R z.1 z.2) atTop (triangle T) := by
  have hD := floorDimension_ge_three dim
  have hlim := actual_ck_means_uniform_limit_of_response_equicontinuity
    (floorDimension dim) (floorDimension_tendsto hdim) hD hp β hβ
      (actual_modelResponse_equicontinuous (floorDimension dim) hD (by omega : 2≤p) β) d hd T
  exact ⟨actual_correlation_uniform_dimension_transfer hdim p β hlim.1,
    actual_gamma_uniform_dimension_transfer hdim p β hlim.2.1,
    actual_response_uniform_dimension_transfer hdim p β hlim.2.2⟩

 theorem exists_actual_ck_uniform_limit (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β) :
    ∃d : CKSpecification.CKData,CKSpecification.CKEquations p β d ∧
      CKSpecification.PhysicalBounds d ∧ CKSpecification.PositiveSemidefiniteCorrelation d ∧
      ∀dim : ℕ→ℕ,Tendsto dim atTop atTop→∀T : ℝ≥0,
        TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim n) p β))
          (fun z : ℝ≥0×ℝ≥0 => d.C z.1 z.2) atTop (square T) ∧
        TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim n) p β))
          (fun z : ℝ≥0×ℝ≥0 => ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2) atTop (square T) ∧
        TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β))
          (fun z : ℝ≥0×ℝ≥0 => d.R z.1 z.2) atTop (triangle T) := by
  obtain ⟨d,hd,hB,hPSD,_⟩ := CKGlobalExistence.ck_global_wellposedness hp (show (0 : ℝ)<β from hβ)
  exact ⟨d,hd,hB,hPSD,fun dim hdim T => actual_ck_means_uniform_limit dim hdim hp β hβ d hd T⟩

end SphericalAging.ActualCKMeanKernelConvergence
