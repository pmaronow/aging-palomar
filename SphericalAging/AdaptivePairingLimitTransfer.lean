module

public import SphericalAging.AsymptoticErrorTransfer
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

/-! The scalar passage from the genuine conditional field-cost estimate
to the printed adaptive projection recursion in source10.7. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptivePairingLimitTransfer
open Filter Set
open scoped Topology

theorem penalty_limsup_le {e m : ℕ→ℝ} {E D β : ℝ} (hβ : 0<β)
    (heBelow : IsBoundedUnder (·≥·) atTop e) (hm : ∀n,0≤m n)
    (hcost : ∀ε>0,∀ᶠn in atTop,e n+β*m n≤E+ε)
    (henergy : E-D≤liminf e atTop) : limsup m atTop≤D/β := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hε : 0<β*η/2 := by positivity
  have hevent := eventually_lt_of_lt_liminf
    (henergy.trans_lt' (show E-D-β*η/2<E-D by linarith)) heBelow
  have hpoint : ∀ᶠn in atTop,m n≤D/β+η := by
    filter_upwards [hcost (β*η/2) hε,hevent] with n hc he
    have hid : (D/β+η)*β=D+β*η := by field_simp
    have hb : m n*β≤(D/β+η)*β := by rw [hid];linarith
    exact le_of_mul_le_mul_right hb hβ
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hm) hpoint

theorem limsup_rpow_eq {m : ℕ→ℝ} {q : ℝ} (hq : 0≤q)
    (hBound : IsBoundedUnder (·≤·) atTop m) (hm : ∀n,0≤m n) :
    limsup (fun n => (m n)^q) atTop=(limsup m atTop)^q := by
  let f : ℝ→ℝ := fun x => (max 0 x)^q
  have hf : Monotone f := fun x y hxy =>
    Real.rpow_le_rpow (le_max_left _ _) (max_le_max le_rfl hxy) hq
  have hc : Continuous f :=
    (Real.continuous_rpow_const hq).comp (continuous_const.max continuous_id)
  have hL : 0≤limsup m atTop := le_limsup_of_frequently_le (Eventually.of_forall hm).frequently hBound
  have hh := (hf.map_limsup_of_continuousAt m hc.continuousAt hBound
    (isCoboundedUnder_le_of_le atTop hm)).symm
  simpa only [f,Function.comp_def,max_eq_right (hm _),max_eq_right hL] using hh

theorem projection_limsup_recursion {a b m : ℕ→ℝ} {q R : ℝ} (hq : 0≤q)
    (ha : ∀n,0≤a n ∧ a n≤1) (hb : ∀n,0≤b n ∧ b n≤1)
    (hm : ∀n,0≤m n ∧ m n≤1) (hpoint : ∀n,b n≤a n+(m n)^q)
    (hM : limsup m atTop≤R) :
    limsup b atTop≤limsup a atTop+R^q := by
  have haAbove : IsBoundedUnder (·≤·) atTop a := isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (ha n).2)
  have haBelow : IsBoundedUnder (·≥·) atTop a := isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => (ha n).1)
  have hbAbove : IsBoundedUnder (·≤·) atTop b := isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hb n).2)
  have hmAbove : IsBoundedUnder (·≤·) atTop m := isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hm n).2)
  have hqnon n : 0≤(m n)^q := Real.rpow_nonneg (hm n).1 _
  have hqAbove : IsBoundedUnder (·≤·) atTop (fun n => (m n)^q) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => show (m n)^q≤1 from by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (hm n).1 (hm n).2 hq)
  have habove : IsBoundedUnder (·≤·) atTop (fun n => a n+(m n)^q) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => show a n+(m n)^q≤2 from by
      have ht : (m n)^q≤1 := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow (hm n).1 (hm n).2 hq
      linarith [(ha n).2])
  have hmono := limsup_le_limsup (Eventually.of_forall hpoint)
    (isCoboundedUnder_le_of_le atTop (fun n => (hb n).1)) habove
  have hadd := limsup_add_le haBelow haAbove
    (isCoboundedUnder_le_of_le atTop hqnon) hqAbove
  have hL : 0≤limsup m atTop := le_limsup_of_frequently_le
    (Eventually.of_forall fun n => (hm n).1).frequently hmAbove
  calc
    limsup b atTop≤limsup (fun n => a n+(m n)^q) atTop := hmono
    _≤limsup a atTop+limsup (fun n => (m n)^q) atTop := hadd
    _=limsup a atTop+(limsup m atTop)^q := by rw [limsup_rpow_eq hq hmAbove (fun n => (hm n).1)]
    _≤limsup a atTop+R^q := add_le_add_right (Real.rpow_le_rpow hL hM hq) _

theorem vanishing_projection_recursion {Θ : Type*} {l : Filter Θ}
    {ψ : ℕ→Θ→ℝ} {δ : Θ→ℝ} {β C q : ℝ} (hβ : 0<β) (hq : 0<q)
    (hψ : ∀j θ,0≤ψ j θ) (hδ : Tendsto δ l (𝓝 0))
    (hzero : Tendsto (ψ 0) l (𝓝 0))
    (hstep : ∀j θ,ψ (j+1) θ≤ψ j θ+((δ θ+C*Real.sqrt (ψ j θ))/β)^q) (j : ℕ) :
    Tendsto (ψ j) l (𝓝 0) := by
  induction j with
  | zero => exact hzero
  | succ j ih =>
    have hs := (Real.continuous_sqrt.continuousAt.tendsto.comp ih)
    have hv : Tendsto (fun θ => (δ θ+C*Real.sqrt (ψ j θ))/β) l (𝓝 0) := by
      simpa only [Function.comp_def,Real.sqrt_zero,mul_zero,add_zero,zero_div] using
        (hδ.add (hs.const_mul C)).div_const β
    have hp := (Real.continuous_rpow_const hq.le).continuousAt.tendsto.comp hv
    have hu : Tendsto (fun θ => ψ j θ+((δ θ+C*Real.sqrt (ψ j θ))/β)^q) l (𝓝 0) := by
      simpa only [Function.comp_def,Real.zero_rpow hq.ne',add_zero] using ih.add hp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (hψ (j+1)) (hstep j)

end SphericalAging.AdaptivePairingLimitTransfer
