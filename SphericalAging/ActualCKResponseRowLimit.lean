module

public import SphericalAging.ActualResponseCKPrimitiveLimit
public import SphericalAging.CKResponsePrimitiveKernel

public section

/-! The literal printed response CK row from actual model subsequence limits.
All finite-dimensional primitive, diagonal and Γ-defect inputs are proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualCKResponseRowLimit
open ActualResponsePrimitiveInterchange ActualAnnealedGammaIntegral
  ActualCKGammaSlopeResidual AnnealedHamiltonianEnergyStein CKResponsePrimitiveKernel
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

theorem actual_ck_response_integral_row {ι : Type*} {l : Filter ι} [NeBot l]
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hD : ∀ i,3≤dim i)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) (d : CKSpecification.CKData)
    {G : ℝ≥0→ℝ≥0→ℝ}
    (hμ : Continuous d.multiplier) (hC : Continuous (Function.uncurry d.C))
    (hR : Continuous (Function.uncurry d.R))
    (hGlim : ∀ u≤T,∀ s≤T,Tendsto (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) u s) l (𝓝 (G u s)))
    (hRlim : ∀ u≤T,∀ s≤T,TendstoUniformlyOn (fun i => fun v : ℝ =>
      modelResponse (N := dim i) (p := p) β u v.toNNReal) (d.R u) l
        (uIcc 0 (min (u : ℝ) (s : ℝ))))
    (hSlim : ∀ t≤T,∀ a≤t,∀ s≤a,TendstoUniformlyOn (fun i => fun u : ℝ =>
      ckGammaSlope (N := dim i) (by have := hD i;omega) p β u.toNNReal s)
        (fun u : ℝ => ResponsePrimitiveInterchange.gammaSlope d.multiplier
          (memoryKernel p β d.C d.R) d.R (u.toNNReal : ℝ) s) l
          (uIcc (a : ℝ) (t : ℝ)))
    (t : ℝ≥0) (htT : t≤T) :
    ∀ s ∈ Icc 0 (t : ℝ),d.R t s=1+∫ u in s..(t : ℝ),CKSpecification.responseSlope p β d u s := by
  have hh := ActualResponseCKPrimitiveLimit.actual_response_ck_integral_limit
    dim hDim hD hp β T hT hμ (memoryKernel_continuous p β hC hR) hR hGlim hRlim hSlim t htT
  simpa only [responseSlope_eq_ckResponseSlope] using hh

/-- Its derivative form on a compact causal row, including both endpoints. -/
theorem actual_ck_response_hasDerivWithinAt {ι : Type*} {l : Filter ι} [NeBot l]
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hD : ∀ i,3≤dim i)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) (d : CKSpecification.CKData)
    {G : ℝ≥0→ℝ≥0→ℝ}
    (hμ : Continuous d.multiplier) (hC : Continuous (Function.uncurry d.C))
    (hR : Continuous (Function.uncurry d.R))
    (hGlim : ∀ u≤T,∀ s≤T,Tendsto (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) u s) l (𝓝 (G u s)))
    (hRlim : ∀ u≤T,∀ s≤T,TendstoUniformlyOn (fun i => fun v : ℝ =>
      modelResponse (N := dim i) (p := p) β u v.toNNReal) (d.R u) l
        (uIcc 0 (min (u : ℝ) (s : ℝ))))
    (hSlim : ∀ t≤T,∀ a≤t,∀ s≤a,TendstoUniformlyOn (fun i => fun u : ℝ =>
      ckGammaSlope (N := dim i) (by have := hD i;omega) p β u.toNNReal s)
        (fun u : ℝ => ResponsePrimitiveInterchange.gammaSlope d.multiplier
          (memoryKernel p β d.C d.R) d.R (u.toNNReal : ℝ) s) l
          (uIcc (a : ℝ) (t : ℝ)))
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) (htT : t≤(T : ℝ)) :
    HasDerivWithinAt (fun u => d.R u s) (CKSpecification.responseSlope p β d t s) (Icc s T) t := by
  have hS : Continuous (fun u => CKSpecification.responseSlope p β d u s) :=
    (ckResponseSlope_continuous p β d hμ hC hR).comp (continuous_id.prodMk continuous_const)
  have hrow : ∀ u ∈ Icc s (T : ℝ),d.R u s=1+∫ r in s..u,CKSpecification.responseSlope p β d r s := by
    intro u hu
    let un := u.toNNReal
    have heu : (un : ℝ)=u := Real.coe_toNNReal _ (hs.trans hu.1)
    have huT : un≤T := by change (un : ℝ)≤T;rw [heu];exact hu.2
    have hh := actual_ck_response_integral_row dim hDim hD hp β T hT d hμ hC hR hGlim hRlim hSlim un huT s
      (by rw [heu];exact ⟨hs,hu.1⟩)
    simpa only [heu] using hh
  exact ResponseIntegralSlope.hasDerivWithinAt_of_integral_row hS hrow t ⟨hst,htT⟩

end SphericalAging.ActualCKResponseRowLimit
