module

public import SphericalAging.ActualGammaDifferenceLimit
public import SphericalAging.ActualResponseDiagonalLimit
public import SphericalAging.ResponsePrimitiveClosure
public import SphericalAging.ResponsePrimitiveSlopeContinuity

public section

/-! Actual subsequence response CK identification from the true Γ row and
source 3.4. Only preceding kernel and nonlinear slope convergence enter;
no Γ equation or response CK equation is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualResponseCKPrimitiveLimit
open ActualResponsePrimitiveInterchange ActualResponsePrimitiveLimit
  ActualResponseDiagonalLimit ActualGammaDifferenceLimit ActualAnnealedGammaIntegral
  ActualCKGammaSlopeResidual AnnealedHamiltonianEnergyStein
  ResponsePrimitiveInterchange ResponsePrimitiveClosure ResponsePrimitiveSlopeContinuity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

theorem actual_response_row_limit {ι : Type*} {l : Filter ι} [NeBot l]
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hD : ∀ i,3≤dim i)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T)
    {μ : ℝ→ℝ} {K R : ℝ→ℝ→ℝ} {G : ℝ≥0→ℝ≥0→ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R))
    (hGlim : ∀ u≤T,∀ s≤T,Tendsto (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) u s) l (𝓝 (G u s)))
    (hRlim : ∀ u≤T,∀ s≤T,TendstoUniformlyOn (fun i => fun v : ℝ =>
      modelResponse (N := dim i) (p := p) β u v.toNNReal) (R u) l
        (uIcc 0 (min (u : ℝ) (s : ℝ))))
    (hSlim : ∀ t≤T,∀ a≤t,∀ s≤a,TendstoUniformlyOn (fun i => fun u : ℝ =>
      ckGammaSlope (N := dim i) (by have := hD i;omega) p β u.toNNReal s)
        (fun u : ℝ => gammaSlope μ K R (u.toNNReal : ℝ) s) l
          (uIcc (a : ℝ) (t : ℝ)))
    (t : ℝ≥0) (htT : t≤T) :
    ∀ v ∈ Icc 0 (t : ℝ),R t v-R v v=∫ u in v..(t : ℝ),responseSlope μ K R u v := by
  have hPrefix : ∀ u≤T,∀ s≤T,G u s=responsePrimitive R u s := by
    intro u hu s hs
    have hRu : Continuous (R u) := hR.comp (continuous_const.prodMk continuous_id)
    exact actual_gamma_response_limit dim hDim (by omega : 2≤p) β u s
      (hRu.intervalIntegrable 0 (min (u : ℝ) (s : ℝ))) (hRlim u hu s hs) (hGlim u hu s hs)
  have hGS := gammaSlope_continuous hμ hK hR
  apply response_row_of_all_gamma_rows hμ hK hR t.coe_nonneg (fun _ _ => rfl)
  intro a ha s hs
  let an := a.toNNReal
  let sn := s.toNNReal
  have hea : (an : ℝ)=a := Real.coe_toNNReal _ ha.1
  have hes : (sn : ℝ)=s := Real.coe_toNNReal _ hs.1
  have hat : an≤t := by change (an : ℝ)≤t;rw [hea];exact ha.2
  have hsa : sn≤an := by change (sn : ℝ)≤an;rw [hes,hea];exact hs.2
  have haT := hat.trans htT
  have hsT := hsa.trans haT
  have hSlope : Continuous (fun u : ℝ => gammaSlope μ K R (u.toNNReal : ℝ) sn) :=
    hGS.comp ((continuous_subtype_val.comp continuous_real_toNNReal).prodMk continuous_const)
  have he := actual_gamma_difference_row_limit (S := fun u s => gammaSlope μ K R u s)
    dim hDim hD hp β T hT t an sn hsa hat htT
    (hGlim t htT sn hsT) (hGlim an haT sn hsT)
    (hSlope.intervalIntegrable (an : ℝ) (t : ℝ)) (hSlim t htT an hat sn hsa)
  rw [hPrefix t htT sn hsT,hPrefix an haT sn hsT] at he
  simp only [hea,hes] at he
  change responsePrimitive R t s-responsePrimitive R a s=
    ∫ u in a..(t : ℝ),gammaSlope μ K R u s
  rw [he]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.2] at hu
  dsimp only
  rw [Real.coe_toNNReal _ (ha.1.trans hu.1)]

/-- The actual response diagonal normalization is inherited by the row limit,
so the identified response row has its CK initial value one. -/
theorem actual_response_ck_integral_limit {ι : Type*} {l : Filter ι} [NeBot l]
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hD : ∀ i,3≤dim i)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T)
    {μ : ℝ→ℝ} {K R : ℝ→ℝ→ℝ} {G : ℝ≥0→ℝ≥0→ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R))
    (hGlim : ∀ u≤T,∀ s≤T,Tendsto (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) u s) l (𝓝 (G u s)))
    (hRlim : ∀ u≤T,∀ s≤T,TendstoUniformlyOn (fun i => fun v : ℝ =>
      modelResponse (N := dim i) (p := p) β u v.toNNReal) (R u) l
        (uIcc 0 (min (u : ℝ) (s : ℝ))))
    (hSlim : ∀ t≤T,∀ a≤t,∀ s≤a,TendstoUniformlyOn (fun i => fun u : ℝ =>
      ckGammaSlope (N := dim i) (by have := hD i;omega) p β u.toNNReal s)
        (fun u : ℝ => gammaSlope μ K R (u.toNNReal : ℝ) s) l
          (uIcc (a : ℝ) (t : ℝ)))
    (t : ℝ≥0) (htT : t≤T) :
    ∀ v ∈ Icc 0 (t : ℝ),R t v=1+∫ u in v..(t : ℝ),responseSlope μ K R u v := by
  intro v hv
  have he := actual_response_row_limit dim hDim hD hp β T hT hμ hK hR hGlim hRlim hSlim t htT v hv
  let vn := v.toNNReal
  have hev : (vn : ℝ)=v := Real.coe_toNNReal _ hv.1
  have hvt : vn≤t := by change (vn : ℝ)≤t;rw [hev];exact hv.2
  have hvT := hvt.trans htT
  have hd := actual_response_diagonal_limit dim hDim hD (by omega : 2≤p) β vn
    (by simpa only [min_self] using hRlim vn hvT vn hvT)
  simp only [hev] at hd
  rw [hd] at he
  linarith

end SphericalAging.ActualResponseCKPrimitiveLimit
