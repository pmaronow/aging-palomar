module

public import SphericalAging.ResponsePrimitiveLimitIdentification

public section

/-! A vanishing actual Γ row defect and a uniform integrable slope limit
identify the limiting two-terminal Γ row. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace SphericalAging.GammaDifferenceLimitIdentification
open ResponsePrimitiveLimitIdentification
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

theorem row_eq_of_residual_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {Gn : ι → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    {Sn : ι → ℝ → ℝ → ℝ} {S : ℝ → ℝ → ℝ} {t a s : ℝ}
    (hGt : Tendsto (fun i => Gn i t s) l (𝓝 (G t s)))
    (hGa : Tendsto (fun i => Gn i a s) l (𝓝 (G a s)))
    (hSn : ∀ᶠ i in l,IntervalIntegrable (fun u => Sn i u s) volume a t)
    (hS : IntervalIntegrable (fun u => S u s) volume a t)
    (hSlim : TendstoUniformlyOn (fun i => fun u => Sn i u s)
      (fun u => S u s) l (uIcc a t))
    (hres : Tendsto (fun i => Gn i t s-Gn i a s-∫ u in a..t,Sn i u s) l (𝓝 0)) :
    G t s-G a s=∫ u in a..t,S u s := by
  have hInt := intervalIntegral_tendsto_of_uniform_integrable hSn hS hSlim
  have hh := tendsto_nhds_unique ((hGt.sub hGa).sub hInt) hres
  exact sub_eq_zero.mp hh

end SphericalAging.GammaDifferenceLimitIdentification
