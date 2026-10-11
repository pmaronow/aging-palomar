module

public import SphericalAging.AsymptoticErrorTransfer
public import SphericalAging.CurriedLimitTransfer

public section

/-! The literal source10.7 algorithm energy deficit and its saturation
under genuine finite-dimensional normalized-center energy transfer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AlgorithmEnergyDeficit
open Filter
open scoped Topology

@[expose] def deficit (E : ℝ) (a : ℕ→ℝ) : ℝ := max 0 (E-liminf a atTop)

theorem deficit_nonnegative (E : ℝ) (a : ℕ→ℝ) : 0≤deficit E a := le_max_left _ _

theorem energy_lower (E : ℝ) (a : ℕ→ℝ) : E-deficit E a≤liminf a atTop := by
  have h := le_max_right (0:ℝ) (E-liminf a atTop)
  dsimp only [deficit]
  linarith

theorem deficit_le_transfer {E r error : ℝ} {a : ℕ→ℝ}
    (h : r-error≤liminf a atTop) : deficit E a≤max 0 (E-r+error) := by
  apply max_le_max le_rfl
  linarith

theorem deficit_tendsto_zero {Θ : Type*} {l : Filter Θ} {E : ℝ}
    {a : Θ→ℕ→ℝ} {r error : Θ→ℝ}
    (hLower : ∀θ,r θ-error θ≤liminf (a θ) atTop)
    (hReference : Tendsto r l (𝓝 E)) (hError : Tendsto error l (𝓝 0)) :
    Tendsto (fun θ => deficit E (a θ)) l (𝓝 0) := by
  have hUpper : Tendsto (fun θ => max 0 (E-r θ+error θ)) l (𝓝 0) := by
    simpa only [sub_self,zero_add,max_self] using
      ((tendsto_const_nhds : Tendsto (fun _ : Θ => (0:ℝ)) l (𝓝 0)).max
        (((tendsto_const_nhds : Tendsto (fun _ : Θ => E) l (𝓝 E)).sub hReference).add hError))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun θ => deficit_nonnegative E (a θ))
    (fun θ => deficit_le_transfer (hLower θ))

theorem deficit_tendsto_of_normalized_energy {Θ : Type*} {l : Filter Θ} {E ρ₀ D₀ : ℝ}
    {algorithm mean firstError secondError : Θ→ℕ→ℝ}
    {ρ D h γ ε κ : Θ→ℝ}
    (hρ : ∀θ,0≤ρ θ ∧ ρ θ≤ρ₀) (hD : ∀θ,0≤D θ ∧ D θ≤D₀)
    (hγ : ∀θ,0≤γ θ) (hε : ∀θ,0≤ε θ) (hκ : ∀θ,0≤κ θ)
    (hpoint : ∀θ n,ρ θ*mean θ n-D θ*(firstError θ n+secondError θ n)≤algorithm θ n)
    (hAlgBound : ∀θ,IsBoundedUnder (·≤·) atTop (algorithm θ))
    (hMeanBound : ∀θ,IsBoundedUnder (·≤·) atTop (fun n => |mean θ n-h θ|))
    (hFirstBound : ∀θ,IsBoundedUnder (·≤·) atTop (firstError θ))
    (hSecondBound : ∀θ,IsBoundedUnder (·≤·) atTop (secondError θ))
    (hMean : ∀θ,limsup (fun n => |mean θ n-h θ|) atTop≤γ θ)
    (hFirst : ∀θ,limsup (firstError θ) atTop≤ε θ)
    (hSecond : ∀θ,limsup (secondError θ) atTop≤κ θ)
    (hSaturation : Tendsto (fun θ => ρ θ*h θ) l (𝓝 E))
    (hγLimit : Tendsto γ l (𝓝 0)) (hεLimit : Tendsto ε l (𝓝 0))
    (hκLimit : Tendsto κ l (𝓝 0)) :
    Tendsto (fun θ => deficit E (algorithm θ)) l (𝓝 0) := by
  apply deficit_tendsto_zero (r := fun θ => ρ θ*h θ)
    (error := fun θ => ρ₀*γ θ+D₀*(ε θ+κ θ)) _ hSaturation
      (by simpa only [mul_zero,zero_add] using
        (hγLimit.const_mul ρ₀).add ((hεLimit.add hκLimit).const_mul D₀))
  intro θ
  have hh := AsymptoticErrorTransfer.energy_liminf_lower (hρ θ).1 (hD θ).1
    (hpoint θ) (hAlgBound θ) (hMeanBound θ) (hFirstBound θ) (hSecondBound θ)
    (hMean θ) (hFirst θ) (hSecond θ)
  have hr := mul_le_mul_of_nonneg_right (hρ θ).2 (hγ θ)
  have hd := mul_le_mul_of_nonneg_right (hD θ).2 (add_nonneg (hε θ) (hκ θ))
  linarith

end SphericalAging.AlgorithmEnergyDeficit
