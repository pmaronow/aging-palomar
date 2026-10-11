module

public import SphericalAging.AsymptoticErrorTransfer
public import SphericalAging.AlgorithmEnergyDeficit

public section

/-! Actual ordered scalar transfer used in the general-spin forgetting
argument. The assumptions are preceding dimension bridges and quantitative
algorithm approximation/orthogonality, not correlation forgetting. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ForkForgettingLimit
open Filter
open scoped Topology

theorem mean_overlap_limit_le {f moment distance : ℕ→ℝ} {c Q D : ℝ}
    (hQ : 0<Q) (hf : Tendsto f atTop (𝓝 c))
    (hm : ∀n,0≤moment n ∧ moment n≤1)
    (hd : ∀n,0≤distance n ∧ distance n≤D)
    (hpoint : ∀n,f n/Real.sqrt Q≤Real.sqrt (moment n)+distance n) :
    c/Real.sqrt Q≤Real.sqrt (limsup moment atTop)+limsup distance atTop := by
  have hmB : IsBoundedUnder (·≤·) atTop moment :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hm n).2)
  have hdB : IsBoundedUnder (·≤·) atTop distance :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hd n).2)
  have hgB : IsBoundedUnder (·≤·) atTop (fun n => Real.sqrt (moment n)) := by
    have he : ∀ᶠn in atTop,Real.sqrt (moment n)≤(1:ℝ) :=
      Eventually.of_forall fun n => (Real.sqrt_le_sqrt (hm n).2).trans_eq (by norm_num)
    exact isBoundedUnder_of_eventually_le he
  have hh := AsymptoticErrorTransfer.pairing_limit_upper
    (hf.div_const (Real.sqrt Q)) (fun n => by simpa using hpoint n) hgB hdB
    (isBoundedUnder_of_eventually_le (Eventually.of_forall (fun _ : ℕ => le_refl (0:ℝ))))
    (le_refl (limsup (fun n => Real.sqrt (moment n)) atTop))
    (le_refl (limsup distance atTop)) (by simp : limsup (fun _ : ℕ => (0:ℝ)) atTop≤0)
  rw [AsymptoticErrorTransfer.limsup_sqrt_eq hmB (fun n => (hm n).1)] at hh
  simpa only [add_zero] using hh

theorem correlation_limit_from_fork {Θ : Type*} {l : Filter Θ}
    {c Q : Θ→ℝ} {mean moment distance : Θ→ℕ→ℝ} {D : ℝ}
    (hc : ∀θ,0≤c θ) (hQ : ∀θ,0<Q θ ∧ Q θ≤1)
    (hMean : ∀θ,Tendsto (mean θ) atTop (𝓝 (c θ)))
    (hMoment : ∀θ n,0≤moment θ n ∧ moment θ n≤1)
    (hDistance : ∀θ n,0≤distance θ n ∧ distance θ n≤D)
    (hpoint : ∀θ n,mean θ n/Real.sqrt (Q θ)≤Real.sqrt (moment θ n)+distance θ n)
    (hOrthogonality : Tendsto (fun θ => limsup (moment θ) atTop) l (𝓝 0))
    (hApproximation : Tendsto (fun θ => limsup (distance θ) atTop) l (𝓝 0)) :
    Tendsto c l (𝓝 0) := by
  have hUpper : Tendsto (fun θ => Real.sqrt (limsup (moment θ) atTop)+
      limsup (distance θ) atTop) l (𝓝 0) := by
    simpa only [Real.sqrt_zero,zero_add] using hOrthogonality.sqrt.add hApproximation
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper hc
  intro θ
  have hh := mean_overlap_limit_le (hQ θ).1 (hMean θ) (hMoment θ) (hDistance θ) (hpoint θ)
  have hr : Real.sqrt (Q θ)≤1 :=
    (Real.sqrt_le_sqrt (hQ θ).2).trans_eq (by norm_num)
  have hrp : 0<Real.sqrt (Q θ) := Real.sqrt_pos.mpr (hQ θ).1
  have hn : c θ≤c θ/Real.sqrt (Q θ) := by
    apply (le_div_iff₀ hrp).mpr
    exact mul_le_of_le_one_right (hc θ) hr
  exact hn.trans hh

end SphericalAging.ForkForgettingLimit
