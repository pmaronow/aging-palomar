module

public import SphericalAging.ActualGlobalCKKernelIdentification
public import SphericalAging.CKWellposedness

public section

/-! A global compact limit of the actual finite-dimensional kernels is
uniquely identified with any solution of the manuscript CK equations. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualCKKernelLimitUniqueness
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualGlobalCKKernelIdentification
  ActualCKUniformKernelRowIdentification CompactCKPrimitiveSlopeIdentification
  ActualResponsePrimitiveInterchange
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} {L : Filter A} [NeBot L] {p : ℕ}

 theorem actual_ck_kernel_limit_domainEquivalent
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β) {C G R : Kernel}
    (hC : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hG : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelGamma (dim j) p β))
      (Function.uncurry G) L (square T))
    (hR : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hGc : Continuous (Function.uncurry G))
    (hRc : Continuous (Function.uncurry R)) {d : CKSpecification.CKData}
    (hd : CKSpecification.CKEquations p β d) :
    CKSpecification.DomainEquivalent (realCKData p β C R) d :=
  CKWellposedness.ck_equations_unique
    (actual_global_ck_equations_of_uniform_kernels dim hdim hD hp β hβ hC hG hR hCc hGc hRc) hd

 theorem actual_ck_kernel_limit_identification
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β) {C G R : Kernel}
    (hC : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hG : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelGamma (dim j) p β))
      (Function.uncurry G) L (square T))
    (hR : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hGc : Continuous (Function.uncurry G))
    (hRc : Continuous (Function.uncurry R)) {d : CKSpecification.CKData}
    (hd : CKSpecification.CKEquations p β d) :
    (∀t s : ℝ≥0,C t s=d.C t s) ∧ (∀t s : ℝ≥0,s≤t→R t s=d.R t s) ∧
      (∀t s : ℝ≥0,G t s=∫v in (0 : ℝ)..(min (t : ℝ) (s : ℝ)),d.R t v) := by
  have he := actual_ck_kernel_limit_domainEquivalent dim hdim hD hp β hβ hC hG hR hCc hGc hRc hd
  have hCe : ∀t s : ℝ≥0,C t s=d.C t s := by
    intro t s
    simpa only [realCKData,realKernel,Real.toNNReal_coe] using he.1 t s t.coe_nonneg s.coe_nonneg
  have hRe : ∀t s : ℝ≥0,s≤t→R t s=d.R t s := by
    intro t s hst
    simpa only [realCKData,realKernel,Real.toNNReal_coe] using he.2.1 t s s.coe_nonneg
      (show (s : ℝ)≤t from hst)
  refine ⟨hCe,hRe,?_⟩
  intro t s
  let T := max t s
  rw [actual_gamma_primitive_of_uniform_kernels dim hdim (by omega : 2≤p) β T (hG T) (hR T) hRc
    t s (le_max_left _ _) (le_max_right _ _)]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  rw [uIcc_of_le (le_min t.coe_nonneg s.coe_nonneg)] at hv
  have hvt : v.toNNReal≤t := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hv.1]
    exact hv.2.trans (min_le_left _ _)
  have hh := hRe t v.toNNReal hvt
  simpa only [Real.coe_toNNReal _ hv.1] using hh

end SphericalAging.ActualCKKernelLimitUniqueness
