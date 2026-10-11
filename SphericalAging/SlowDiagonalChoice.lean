module

public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-! A constructive integer-age diagonal selection from honest fixed-age
eventual assertions. The selected waiting times exceed the selected ages. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.SlowDiagonalChoice

theorem exists_integer_ages (P : ℕ → ℝ → Prop)
    (hP : ∀ k, ∀ᶠ T : ℝ in atTop, P k T)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ (N : ℕ) (i : ℕ → ℕ), Tendsto i atTop atTop ∧
      ∀ n, (i n+1:ℝ)≤t (n+N)-(i n+1:ℝ) ∧
        P (i n) (t (n+N)-(i n+1:ℝ)) := by
  classical
  choose M hM using fun k => eventually_atTop.mp (hP k)
  let B : ℕ → ℝ := fun k => max (M k+(k+1:ℝ)) (2*(k+1:ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (B 0)))
  let i : ℕ → ℕ := fun n => Nat.findGreatest (fun k => B k≤t (n+N)) n
  have hi (n : ℕ) : B (i n)≤t (n+N) := by
    exact Nat.findGreatest_spec (P:=fun k => B k≤t (n+N)) (Nat.zero_le n)
      (hN (n+N) (Nat.le_add_left N n))
  refine ⟨N,i,?_,?_⟩
  · apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k,
      ((ht.comp (tendsto_add_atTop_nat N)).eventually (eventually_ge_atTop (B k)))] with n hn htn
    exact Nat.le_findGreatest hn htn
  · intro n
    have hb := hi n
    have h1 := (le_max_left (M (i n)+(i n+1:ℝ)) (2*(i n+1:ℝ))).trans hb
    have h2 := (le_max_right (M (i n)+(i n+1:ℝ)) (2*(i n+1:ℝ))).trans hb
    exact ⟨by linarith,hM (i n) _ (by linarith)⟩

end SphericalAging.SlowDiagonalChoice
