module

public import SphericalAging.ActualCKUniformKernelRowIdentification
public import SphericalAging.ActualCompactCorrelationProperties
public import SphericalAging.CompactCKPrimitiveSlopeIdentification
public import SphericalAging.ActualCKResponseRowLimit

public section

/-! Both printed CK integral rows follow from actual compact C/Γ/R kernel
limits. The true finite-N residuals, nonlinear memory convergence, Γ
primitive, correlation symmetry, and response normalization are discharged. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualPrintedCKRowIdentification
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualCompactCKSlopeLimit
  CompactCKKernelContinuity ActualCKUniformKernelRowIdentification
  ActualCompactCorrelationProperties CompactCKPrimitiveSlopeIdentification
  ActualResponsePrimitiveInterchange ActualAnnealedGammaIntegral AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} {L : Filter A} [NeBot L] {p : ℕ}

 theorem actual_printed_correlation_integral_row
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) {C R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R))
    (s t : ℝ≥0) (hst : s≤t) (htT : t≤T) :
    (realCKData p β C R).C t s=1+∫u in (s : ℝ)..(t : ℝ),
      CKSpecification.correlationSlope p β (realCKData p β C R) u s := by
  have hSymm : ∀t≤T,∀s≤T,C t s=C s t := fun t ht s hs =>
    compact_correlation_limit_symm dim β T hC ht hs
  calc
    _=C s t := by simp only [realCKData,realKernel,Real.toNNReal_coe];exact hSymm t htT s (hst.trans htT)
    _=1+∫u in (s : ℝ)..(t : ℝ),correlationSlope p β C R s u.toNNReal :=
      actual_correlation_integral_row_of_uniform_kernels dim hdim hD hp β T hT hC hR hCc hRc s t hst htT
    _=_ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      have huT := interval_toNNReal_le hst htT hu
      rw [uIcc_of_le (show (s : ℝ)≤t from hst)] at hu
      have hh := correlationSlope_eq_printed (R := R) (by omega : 1≤p) β T hSymm s u.toNNReal (hst.trans htT) huT
      simpa only [Real.coe_toNNReal _ (s.coe_nonneg.trans hu.1)] using hh

 theorem actual_printed_response_integral_row
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) {C G R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hG : TendstoUniformlyOn (fun j => Function.uncurry (modelGamma (dim j) p β))
      (Function.uncurry G) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hGc : Continuous (Function.uncurry G))
    (hRc : Continuous (Function.uncurry R)) (t : ℝ≥0) (htT : t≤T) :
    ∀s∈Icc 0 (t : ℝ),(realCKData p β C R).R t s=1+∫u in s..(t : ℝ),
      CKSpecification.responseSlope p β (realCKData p β C R) u s := by
  have hSymm : ∀t≤T,∀s≤T,C t s=C s t := fun t ht s hs =>
    compact_correlation_limit_symm dim β T hC ht hs
  have hPrefix : ∀t≤T,∀s≤T,G t s=ResponsePrimitiveInterchange.responsePrimitive (realKernel R) t s := by
    intro t ht s hs
    simpa only [ResponsePrimitiveInterchange.responsePrimitive,realKernel,Real.toNNReal_coe] using
      actual_gamma_primitive_of_uniform_kernels dim hdim (by omega : 2≤p) β T hG hR hRc t s ht hs
  have hSl := actual_gamma_slope_uniform_limit dim hD hp β T hC hG hR hCc hGc hRc
  apply ActualCKResponseRowLimit.actual_ck_response_integral_row dim hdim hD hp β T hT
    (realCKData p β C R) (realCKData_multiplier_continuous p β hCc hRc)
      (realKernel_continuous hCc) (realKernel_continuous hRc)
  · intro u hu s hs
    exact hG.tendsto_at (x := (u,s)) ⟨hu,hs⟩
  · intro u hu s hs
    have hh := actual_response_row_uniform_limit dim β T hR u s hu
    convert hh using 1
    funext v
    simp only [realCKData,realKernel,Real.toNNReal_coe]
  · intro v hv a ha s hs
    have hLim := (hSl.comp (fun u : ℝ => (u.toNNReal,s))).mono
      (show uIcc (a : ℝ) (v : ℝ)⊆{u | (u.toNNReal,s)∈square T} from
        fun u hu => ⟨interval_toNNReal_le ha hv hu,hs.trans (ha.trans hv)⟩)
    apply hLim.congr_right
    intro u hu
    dsimp only [Function.comp_apply,Function.uncurry]
    exact gammaSlope_eq_primitive (by omega : 1≤p) β T hSymm hPrefix u.toNNReal s
      (interval_toNNReal_le ha hv hu) (hs.trans (ha.trans hv))
  · exact htT

end SphericalAging.ActualPrintedCKRowIdentification
