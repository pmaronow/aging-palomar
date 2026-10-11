module

public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! Ordered finite-dimensional error transfer. These scalar lemmas prove
lower energy and upper pairing limits from quantitative preceding errors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace SphericalAging.AsymptoticErrorTransfer

theorem energy_liminf_lower {mean algorithm a b : ℕ→ℝ}
    {h γ ε κ ρ D : ℝ} (hρ : 0≤ρ) (hD : 0≤D)
    (hpoint : ∀n,ρ*mean n-D*(a n+b n)≤algorithm n)
    (hAlgBound : IsBoundedUnder (·≤·) atTop algorithm)
    (hMeanBound : IsBoundedUnder (·≤·) atTop (fun n => |mean n-h|))
    (haBound : IsBoundedUnder (·≤·) atTop a) (hbBound : IsBoundedUnder (·≤·) atTop b)
    (hMean : limsup (fun n => |mean n-h|) atTop≤γ)
    (ha : limsup a atTop≤ε) (hb : limsup b atTop≤κ) :
    ρ*(h-γ)-D*(ε+κ)≤liminf algorithm atTop := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ξ : ℝ := η/(ρ+2*D+1)
  have hden : 0<ρ+2*D+1 := by positivity
  have hξ : 0<ξ := div_pos hη hden
  have hME := eventually_lt_of_limsup_lt
    (hMean.trans_lt (show γ<γ+ξ by linarith)) hMeanBound
  have hAE := eventually_lt_of_limsup_lt
    (ha.trans_lt (show ε<ε+ξ by linarith)) haBound
  have hBE := eventually_lt_of_limsup_lt
    (hb.trans_lt (show κ<κ+ξ by linarith)) hbBound
  have hp : ∀ᶠn in atTop,ρ*(h-γ)-D*(ε+κ)-(ρ+2*D)*ξ≤algorithm n := by
    filter_upwards [hME,hAE,hBE] with n hm ha' hb'
    have hmean : h-γ-ξ≤mean n := by linarith [neg_abs_le (mean n-h)]
    have h1 := mul_le_mul_of_nonneg_left hmean hρ
    have h2 := mul_le_mul_of_nonneg_left (add_le_add ha'.le hb'.le) hD
    linarith [hpoint n]
  have hh := le_liminf_of_le hAlgBound.isCoboundedUnder_ge hp
  have hx : (ρ+2*D)*ξ≤η := by
    have he : (ρ+2*D+1)*ξ=η := by dsimp only [ξ];field_simp
    nlinarith
  linarith

theorem pairing_limit_upper {f g a b : ℕ→ℝ} {z G ε κ : ℝ}
    (hf : Tendsto f atTop (𝓝 z)) (hpoint : ∀n,f n≤g n+a n+b n)
    (hgBound : IsBoundedUnder (·≤·) atTop g)
    (haBound : IsBoundedUnder (·≤·) atTop a) (hbBound : IsBoundedUnder (·≤·) atTop b)
    (hg : limsup g atTop≤G) (ha : limsup a atTop≤ε) (hb : limsup b atTop≤κ) :
    z≤G+ε+κ := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hξ : 0<η/3 := by positivity
  have hGE := eventually_lt_of_limsup_lt
    (hg.trans_lt (show G<G+η/3 by linarith)) hgBound
  have hAE := eventually_lt_of_limsup_lt
    (ha.trans_lt (show ε<ε+η/3 by linarith)) haBound
  have hBE := eventually_lt_of_limsup_lt
    (hb.trans_lt (show κ<κ+η/3 by linarith)) hbBound
  apply le_of_tendsto hf
  filter_upwards [hGE,hAE,hBE] with n hg' ha' hb'
  linarith [hpoint n]

theorem limsup_sqrt_eq {m : ℕ→ℝ}
    (hBound : IsBoundedUnder (·≤·) atTop m) (hnonneg : ∀n,0≤m n) :
    limsup (fun n => Real.sqrt (m n)) atTop=Real.sqrt (limsup m atTop) := by
  have hmono : Monotone Real.sqrt := fun _ _ h => Real.sqrt_le_sqrt h
  exact (hmono.map_limsup_of_continuousAt m Real.continuous_sqrt.continuousAt hBound
    (isCoboundedUnder_le_of_le atTop hnonneg)).symm

theorem limsup_sqrt_le {m : ℕ→ℝ} {ε : ℝ} (hε : 0≤ε)
    (hBound : IsBoundedUnder (·≤·) atTop m) (hnonneg : ∀n,0≤m n)
    (hm : limsup m atTop≤ε^2) :
    limsup (fun n => Real.sqrt (m n)) atTop≤ε := by
  rw [limsup_sqrt_eq hBound hnonneg]
  exact (Real.sqrt_le_sqrt hm).trans_eq (Real.sqrt_sq hε)

end SphericalAging.AsymptoticErrorTransfer
