module

public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic

public section

/-! A bounded continuous real trajectory whose late sequential limits lie
in a finite set converges. This supplies the actual multiplier limit argument
without assuming that the trajectory or its cluster set already converges. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.ContinuousLateLimit

theorem interior_level_late_sequence {f : ℝ→ℝ} (hf : ContinuousOn f (Ici 0))
    (hupper : IsBoundedUnder (·≤·) atTop f)
    (hlower : IsBoundedUnder (·≥·) atTop f) {y : ℝ}
    (hy : y∈Ioo (liminf f atTop) (limsup f atTop)) :
    ∃T : ℕ→ℝ,Tendsto T atTop atTop ∧ ∀n,f (T n)=y := by
  have hlo : ∃ᶠt : ℝ in atTop,f t<y :=
    frequently_lt_of_liminf_lt hupper.isCobounded_ge hy.1
  have hhi : ∃ᶠt : ℝ in atTop,y<f t :=
    frequently_lt_of_lt_limsup hlower.isCobounded_le hy.2
  have hex (n : ℕ) : ∃t : ℝ,(n:ℝ)≤t ∧ f t=y := by
    obtain ⟨a,hfa,ha⟩ := (hlo.and_eventually
      (eventually_ge_atTop (max 0 (n:ℝ)))).exists
    obtain ⟨b,hfb,hb⟩ := (hhi.and_eventually
      (eventually_ge_atTop (max 0 (n:ℝ)))).exists
    have ha0 : 0≤a := (le_max_left _ _).trans ha
    have hb0 : 0≤b := (le_max_left _ _).trans hb
    have hcont : ContinuousOn f (uIcc a b) := hf.mono (by
      intro t ht
      exact (le_min ha0 hb0).trans ht.1)
    obtain ⟨t,ht,hft⟩ := intermediate_value_uIcc hcont (by
      rw [uIcc_of_le (hfa.le.trans hfb.le)]
      exact ⟨hfa.le,hfb.le⟩)
    refine ⟨t,?_,hft⟩
    have han : (n:ℝ)≤a := (le_max_right _ _).trans ha
    have hbn : (n:ℝ)≤b := (le_max_right _ _).trans hb
    exact (le_min han hbn).trans ht.1
  choose T hT he using hex
  refine ⟨T,?_,he⟩
  exact tendsto_atTop_mono hT tendsto_natCast_atTop_atTop

theorem converges_of_finite_late_limits {f : ℝ→ℝ} (hf : ContinuousOn f (Ici 0))
    (hupper : IsBoundedUnder (·≤·) atTop f)
    (hlower : IsBoundedUnder (·≥·) atTop f) {K : Set ℝ} (hK : K.Finite)
    (hclass : ∀(T : ℕ→ℝ),Tendsto T atTop atTop→∀ell : ℝ,
      Tendsto (f∘T) atTop (𝓝 ell)→ell∈K) :
    ∃ell∈K,Tendsto f atTop (𝓝 ell) := by
  have hin : Ioo (liminf f atTop) (limsup f atTop)⊆K := by
    intro y hy
    obtain ⟨T,hT,he⟩ := interior_level_late_sequence hf hupper hlower hy
    apply hclass T hT y
    exact tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (he n).symm))
  have hle : liminf f atTop≤limsup f atTop := liminf_le_limsup hupper hlower
  have heq : liminf f atTop=limsup f atTop := by
    apply le_antisymm hle
    by_contra hn
    have hlt : liminf f atTop<limsup f atTop := lt_of_not_ge hn
    exact (Ioo_infinite hlt) (hK.subset hin)
  have hlim := tendsto_of_liminf_eq_limsup heq rfl hupper hlower
  obtain ⟨T,hconv,hT⟩ := exists_seq_tendsto_limsup hlower.isCobounded_le hupper
  exact ⟨limsup f atTop,hclass T hT _ hconv,hlim⟩

end SphericalAging.ContinuousLateLimit
