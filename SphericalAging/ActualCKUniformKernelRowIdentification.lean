module

public import SphericalAging.CompactCKKernelContinuity
public import SphericalAging.ActualCKCorrelationRowLimit
public import SphericalAging.ActualResponsePrimitiveLimit

public section

/-! Exact correlation integral rows and exact saturated response primitives
from uniform compact limits of the actual stochastic kernels. Neither a
memory limit nor an equation for the limiting kernels is a hypothesis. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualCKUniformKernelRowIdentification
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualCompactCKSlopeLimit
  CompactCKKernelContinuity ActualResponsePrimitiveInterchange ActualAnnealedCorrelationIntegral
  ActualAnnealedGammaIntegral AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} {L : Filter A} [NeBot L] {p : ℕ}

 theorem interval_toNNReal_le {a t T : ℝ≥0} (hat : a≤t) (htT : t≤T)
    {u : ℝ} (hu : u∈uIcc (a : ℝ) (t : ℝ)) : u.toNNReal≤T := by
  rw [uIcc_of_le (show (a : ℝ)≤t from hat)] at hu
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (a.coe_nonneg.trans hu.1)]
  exact hu.2.trans (show (t : ℝ)≤T from htT)

 theorem actual_correlation_integral_row_of_uniform_kernels
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) {C R : Kernel}
    (hC : TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R))
    (s t : ℝ≥0) (hst : s≤t) (htT : t≤T) :
    C s t=1+∫u in (s : ℝ)..(t : ℝ),correlationSlope p β C R s u.toNNReal := by
  have hS : Continuous (fun u : ℝ => correlationSlope p β C R s u.toNNReal) :=
    (correlationSlope_continuous p β hCc hRc).comp (continuous_const.prodMk continuous_real_toNNReal)
  have hSl := (actual_correlation_slope_uniform_limit dim hD hp β T hC hR hCc hRc).comp
    (fun u : ℝ => (s,u.toNNReal))
  have hSlim := hSl.mono (show uIcc (s : ℝ) (t : ℝ)⊆{u | (s,u.toNNReal)∈square T} from
    fun u hu => ⟨hst.trans htT,interval_toNNReal_le hst htT hu⟩)
  exact ActualCKCorrelationRowLimit.actual_correlation_integral_row_limit dim hdim hD hp β T hT s t hst htT
    (hC.tendsto_at (x := (s,t)) ⟨hst.trans htT,htT⟩) (hS.intervalIntegrable s t) hSlim

 theorem actual_response_row_uniform_limit (dim : A→ℕ) (β T : ℝ≥0) {R : Kernel}
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T)) (t s : ℝ≥0) (htT : t≤T) :
    TendstoUniformlyOn (fun j => fun v : ℝ => modelResponse (N := dim j) (p := p) β t v.toNNReal)
      (fun v : ℝ => R t v.toNNReal) L (uIcc 0 (min (t : ℝ) (s : ℝ))) := by
  apply (hR.comp (fun v : ℝ => (t,v.toNNReal))).mono
  intro v hv
  rw [uIcc_of_le (le_min t.coe_nonneg s.coe_nonneg)] at hv
  refine ⟨?_,htT⟩
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ hv.1]
  exact hv.2.trans (min_le_left _ _)

 theorem actual_gamma_primitive_of_uniform_kernels
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hp : 2≤p) (β T : ℝ≥0) {G R : Kernel}
    (hG : TendstoUniformlyOn (fun j => Function.uncurry (modelGamma (dim j) p β))
      (Function.uncurry G) L (square T))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hRc : Continuous (Function.uncurry R)) (t s : ℝ≥0) (htT : t≤T) (hsT : s≤T) :
    G t s=∫v in (0 : ℝ)..(min (t : ℝ) (s : ℝ)),R t v.toNNReal := by
  have hRt : Continuous (fun v : ℝ => R t v.toNNReal) :=
    hRc.comp (continuous_const.prodMk continuous_real_toNNReal)
  exact ActualResponsePrimitiveLimit.actual_gamma_response_limit dim hdim hp β t s
    (hRt.intervalIntegrable 0 (min (t : ℝ) (s : ℝ)))
    (actual_response_row_uniform_limit dim β T hR t s htT)
    (hG.tendsto_at (x := (t,s)) ⟨htT,hsT⟩)

end SphericalAging.ActualCKUniformKernelRowIdentification
