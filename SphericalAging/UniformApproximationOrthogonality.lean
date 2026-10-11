module

public import SphericalAging.FiniteStateOrthogonalityLimit

public section

/-! Ordered overlap transfer with a parameter-dependent Euler error and a uniform mesh bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.UniformApproximationOrthogonality
open Filter Set SphericalAging.FiniteStateOrthogonalityLimit
open scoped Topology

theorem ordered_uniform_approximation_limit {Θ : Type*} {l : Filter Θ} {a : Θ→ℕ→ℝ}
    {b : ℕ→Θ→ℕ→ℝ} {e : ℕ→Θ→ℕ→ℝ}
    (ha : ∀θ n,0≤a θ n ∧ a θ n≤1)
    (hb : ∀M θ n,0≤b M θ n ∧ b M θ n≤1)
    (he : ∀M θ n,0≤e M θ n ∧ e M θ n≤4)
    (hcmp : ∀M θ n,a θ n≤2*b M θ n+2*e M θ n)
    (hspan : ∀M,0<M→Tendsto (fun θ => limsup (b M θ) atTop) l (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hEuler : ∀M,0<M→∀θ,limsup (e M θ) atTop≤C/(M:ℝ)) :
    Tendsto (fun θ => limsup (a θ) atTop) l (𝓝 0) := by
  have hab θ : IsBoundedUnder (·≤·) atTop (a θ) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (ha θ n).2)
  have hnonneg θ : 0≤limsup (a θ) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun n => (ha θ n).1) (hab θ)
  have hrate : Tendsto (fun M : ℕ => 2*C/(M:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
        tendsto_natCast_atTop_atTop).const_mul (2*C))
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact Eventually.of_forall fun θ => hz.trans_le (hnonneg θ)
  · intro z hz
    have hm := hrate.eventually (eventually_lt_nhds (by linarith : (0:ℝ)<z/2))
    obtain ⟨M,hM,hMr⟩ := (hm.and (eventually_gt_atTop 0)).exists
    have hbe := (hspan M hMr).eventually (eventually_lt_nhds (by linarith : (0:ℝ)<z/4))
    filter_upwards [hbe] with θ hθ
    have hh := limsup_comparison (ha θ) (hb M θ) (he M θ) (hcmp M θ) (hEuler M hMr θ)
    have hr : 2*(C/(M:ℝ))=2*C/(M:ℝ) := by ring
    rw [hr] at hh
    linarith

end SphericalAging.UniformApproximationOrthogonality
