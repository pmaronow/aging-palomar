module

public import SphericalAging.FiniteStateOrthogonalityBounds

public section

/-! The ordered dimension/algorithm/mesh limit used in the finite-fork waiting-state argument.
The two inputs are precisely the preceding finite-span orthogonality
and Euler mean-square approximation, rather than waiting-state targets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteStateOrthogonalityLimit
open Filter Set
open scoped Topology

theorem limsup_comparison {a b e : ℕ→ℝ} {E : ℝ}
    (ha : ∀n,0≤a n ∧ a n≤1) (hb : ∀n,0≤b n ∧ b n≤1)
    (he : ∀n,0≤e n ∧ e n≤4)
    (hcmp : ∀n,a n≤2*b n+2*e n) (hE : limsup e atTop≤E) :
    limsup a atTop≤2*limsup b atTop+2*E := by
  have hab : IsBoundedUnder (·≤·) atTop a :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (ha n).2)
  have hbb : IsBoundedUnder (·≤·) atTop b :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hb n).2)
  have heb : IsBoundedUnder (·≤·) atTop e :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (he n).2)
  apply (limsup_le_iff (isCoboundedUnder_le_of_le atTop fun n => (ha n).1) hab).mpr
  intro z hz
  let ε := (z-(2*limsup b atTop+2*E))/8
  have hε : 0<ε := by dsimp [ε];linarith
  have hbe := eventually_lt_add_pos_of_limsup_le hbb (le_refl (limsup b atTop)) hε
  have hee := eventually_lt_add_pos_of_limsup_le heb hE hε
  filter_upwards [hbe,hee] with n hn hen
  have hc := hcmp n
  dsimp only [ε] at *
  linarith

theorem ordered_approximation_limit {Θ : Type*} {l : Filter Θ} {a : Θ→ℕ→ℝ}
    {b : ℕ→Θ→ℕ→ℝ} {e : ℕ→ℕ→ℝ}
    (ha : ∀θ n,0≤a θ n ∧ a θ n≤1)
    (hb : ∀M θ n,0≤b M θ n ∧ b M θ n≤1)
    (he : ∀M n,0≤e M n ∧ e M n≤4)
    (hcmp : ∀M θ n,a θ n≤2*b M θ n+2*e M n)
    (hspan : ∀M,0<M→Tendsto (fun θ => limsup (b M θ) atTop) l (𝓝 0))
    {C : ℝ} (hC : 0≤C)
    (hEuler : ∀M,0<M→limsup (e M) atTop≤C/(M:ℝ)) :
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
    have hh := limsup_comparison (ha θ) (hb M θ) (he M) (hcmp M θ) (hEuler M hMr)
    have hr : 2*(C/(M:ℝ))=2*C/(M:ℝ) := by ring
    rw [hr] at hh
    linarith

end SphericalAging.FiniteStateOrthogonalityLimit
