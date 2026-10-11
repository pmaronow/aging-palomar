module

public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-! Literal suprema over the full late causal triangle. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.LateTriangleSup

@[expose] def lateRegion (D S : ℝ) : Set (ℝ×ℝ) := {z | S≤z.2 ∧ z.2+D≤z.1}
@[expose] def lateSup (f : ℝ→ℝ→ℝ) (D S : ℝ) : ℝ :=
  sSup ((fun z : ℝ×ℝ => f z.1 z.2) '' lateRegion D S)

theorem lateRegion_nonempty (D S : ℝ) : (lateRegion D S).Nonempty :=
  ⟨(S+D,S),le_rfl,le_rfl⟩

theorem lateSup_le {f : ℝ→ℝ→ℝ} {D S B : ℝ}
    (hb : ∀t s : ℝ,S≤s→s+D≤t→f t s≤B) : lateSup f D S≤B := by
  apply csSup_le ((lateRegion_nonempty D S).image _)
  rintro x ⟨⟨t,s⟩,hs,rfl⟩
  exact hb t s hs.1 hs.2

/-- A single nonnegative actual point gives nonnegative supremum, including
the conditional-supremum convention when the range is unbounded. -/
theorem lateSup_nonneg {f : ℝ→ℝ→ℝ} {D S : ℝ}
    (hn : 0≤f (S+D) S) : 0≤lateSup f D S := by
  by_cases hb : BddAbove ((fun z : ℝ×ℝ => f z.1 z.2) '' lateRegion D S)
  · exact hn.trans (le_csSup hb ⟨(S+D,S),⟨le_rfl,le_rfl⟩,rfl⟩)
  · simp only [lateSup,csSup_of_not_bddAbove hb,Real.sSup_empty,le_refl]

/-- A uniform eventual estimate on the actual triangle yields its literal
inner limsup, with no global boundedness premise. -/
theorem lateSup_limsup_le {f : ℝ→ℝ→ℝ} {D B : ℝ}
    (hn : ∀ᶠS : ℝ in atTop,0≤lateSup f D S)
    (hb : ∀ε : ℝ,0<ε→∀ᶠS : ℝ in atTop,
      ∀t s : ℝ,S≤s→s+D≤t→f t s≤B+ε) :
    limsup (lateSup f D) atTop≤B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hn)
    ((hb ε hε).mono (fun _ hS => lateSup_le hS))

end SphericalAging.LateTriangleSup
