module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

/-! A positive additive semigroup whose difference group is dense is
uniformly dense on sufficiently late parts of the positive ray. -/
open Set
namespace SphericalAging.SemigroupTailDensity
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The genuine difference group of an additive submonoid. -/
@[expose] def differenceGroup (S : AddSubmonoid ℝ) : AddSubgroup ℝ where
  carrier := {x : ℝ | ∃a∈S,∃b∈S,x=a-b}
  zero_mem' := ⟨0,S.zero_mem,0,S.zero_mem,by ring⟩
  add_mem' := by
    rintro x y ⟨a,ha,b,hb,rfl⟩ ⟨c,hc,d,hd,rfl⟩
    exact ⟨a+c,S.add_mem ha hc,b+d,S.add_mem hb hd,by ring⟩
  neg_mem' := by
    rintro x ⟨a,ha,b,hb,rfl⟩
    exact ⟨b,hb,a,ha,by ring⟩

theorem mem_differenceGroup (S : AddSubmonoid ℝ) (x : ℝ) :
    x∈differenceGroup S ↔ ∃a∈S,∃b∈S,x=a-b := Iff.rfl

theorem submonoid_subset_differenceGroup (S : AddSubmonoid ℝ) :
    (S:Set ℝ)⊆differenceGroup S := fun x hx => ⟨x,hx,0,S.zero_mem,by ring⟩

/-- Density constructs two actual positive semigroup elements with an
arbitrarily small positive difference. -/
theorem positive_close_pair (S : AddSubmonoid ℝ) (hn : ∀x∈S,0≤x)
    (hd : Dense (differenceGroup S : Set ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∃α∈S,∃d : ℝ,0<α ∧ 0<d ∧ d<ε ∧ α+d∈S := by
  obtain ⟨g,hg,hgI⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hε)
  obtain ⟨a,ha,b,hb,hgEq⟩ := hg
  change 0<g ∧ g<ε at hgI
  have ha0 : 0<a := by linarith [hn b hb]
  refine ⟨a+b,S.add_mem ha hb,g,by linarith [hn b hb],hgI.1,hgI.2,?_⟩
  have heq : a+b+g=a+a := by rw [hgEq];ring
  rw [heq]
  exact S.add_mem ha ha

/-- The exact tail density conclusion: every sufficiently large real t is
within ε above an actual element of S. -/
theorem eventually_left_approximation (S : AddSubmonoid ℝ) (hn : ∀x∈S,0≤x)
    (hd : Dense (differenceGroup S : Set ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∃T : ℝ,∀t : ℝ,T≤t → ∃y∈S,y≤t ∧ t-y<ε := by
  obtain ⟨α,hα,d,hα0,hd0,hdε,hαd⟩ := positive_close_pair S hn hd hε
  let T : ℝ := (α/d+1)*α
  refine ⟨T,?_⟩
  intro t ht
  have hT0 : 0<T := by dsimp [T];positivity
  have ht0 : 0<t := hT0.trans_le ht
  let n : ℕ := ⌊t/α⌋₊
  have hnlo : (n:ℝ)*α≤t := (le_div_iff₀ hα0).mp (Nat.floor_le (div_nonneg ht0.le hα0.le))
  have hnhi : t<((n:ℝ)+1)*α := (div_lt_iff₀ hα0).mp (Nat.lt_floor_add_one (t/α))
  have htdiv : α/d+1≤t/α := (le_div_iff₀ hα0).mpr ht
  have hnd : α<(n:ℝ)*d := by
    have hfloor : t/α<(n:ℝ)+1 := Nat.lt_floor_add_one (t/α)
    have hratio : α/d<(n:ℝ) := by linarith
    exact (div_lt_iff₀ hd0).mp hratio
  let r : ℝ := t-(n:ℝ)*α
  have hr0 : 0≤r := sub_nonneg.mpr hnlo
  have hrα : r<α := by dsimp [r];nlinarith
  let k : ℕ := ⌊r/d⌋₊
  have hklo : (k:ℝ)*d≤r := (le_div_iff₀ hd0).mp (Nat.floor_le (div_nonneg hr0 hd0.le))
  have hkhi : r<((k:ℝ)+1)*d := (div_lt_iff₀ hd0).mp (Nat.lt_floor_add_one (r/d))
  have hknr : (k:ℝ)<(n:ℝ) := by nlinarith
  have hkn : k≤n := (Nat.cast_le (α:=ℝ)).mp hknr.le
  let y : ℝ := (n:ℝ)*α+(k:ℝ)*d
  have hy : y∈S := by
    have heq : y=((n-k:ℕ):ℝ)*α+(k:ℝ)*(α+d) := by
      dsimp [y]
      rw [Nat.cast_sub hkn]
      ring
    rw [heq]
    have hleft := S.nsmul_mem hα (n-k)
    have hright := S.nsmul_mem hαd k
    simpa only [nsmul_eq_mul] using S.add_mem hleft hright
  refine ⟨y,hy,?_,?_⟩
  · dsimp [y]
    dsimp [r] at hklo
    linarith
  · have hr : r-(k:ℝ)*d<d := by nlinarith
    dsimp [y]
    dsimp [r] at hr
    linarith

end
end SphericalAging.SemigroupTailDensity
