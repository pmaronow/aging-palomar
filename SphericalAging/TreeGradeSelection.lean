module

public import SphericalAging.TreePrefixAlignment

public section

/-! Genuine good-grade selection from actual positive tree overlaps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace Topology
open Set Filter
namespace SphericalAging.TreeGradeSelection
open CausalTree TreePairDeficit TreePrefixAlignment ProductTransfer

theorem crossBelow_monotone (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) :
    Monotone (crossBelow v w) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [crossBelow_succ]
  exact le_add_of_nonneg_right (hd n)

theorem crossBelow_le_inner (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) (n : ℕ) :
    crossBelow v w n≤ inner ℝ v w := by
  rw [crossBelow_eq_sum,←crossMass_tsum]
  exact (crossMass_summable v w).sum_le_tsum (Finset.range n) (fun j _=>hd j)

theorem inner_nonneg (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) : 0≤ inner ℝ v w := by
  rw [←crossMass_tsum]
  exact tsum_nonneg hd

theorem inner_le_one (v w : Space 2) (hv : ‖v‖=1) (hw : ‖w‖=1) : inner ℝ v w≤1 := by
  have hi := real_inner_le_norm v w
  simpa only [hv,hw,one_mul] using hi

theorem crossBelow_tendsto (v w : Space 2) :
    Tendsto (crossBelow v w) atTop (𝓝 (inner ℝ v w)) := by
  simpa only [←crossBelow_eq_sum,crossMass_tsum] using (crossMass_summable v w).hasSum.tendsto_sum_nat

/-- Actual grade with almost all the pair's overlap captured and smoothed
alignment controlled by its genuine pair deficit. -/
theorem grade_choice (v w : Space 2) (hd : ∀ j,0≤crossMass v w j)
    {η : ℝ} (hη : 0<η) (hc : η< inner ℝ v w) :
    ∃ H : ℕ, inner ℝ v w-η≤crossBelow v w (H+1) ∧
      0<crossMass v w H ∧ 1-rho v w H≤pairDeficit v w/η := by
  let c := inner ℝ v w
  have hex : ∃ n,c-η≤crossBelow v w n := by
    have hev := (crossBelow_tendsto v w).eventually (Ioi_mem_nhds (show c-η<c by linarith))
    obtain ⟨n,hn⟩ := hev.exists
    exact ⟨n,hn.le⟩
  let N := Nat.find hex
  have hN : c-η≤crossBelow v w N := Nat.find_spec hex
  have hNpos : 0<N := by
    by_contra hn
    have hz : N=0 := by omega
    rw [hz] at hN
    simp only [crossBelow,prefixBelow,inner_zero_left] at hN
    linarith
  let n0 := N-1
  have hprev : crossBelow v w n0<c-η :=
    lt_of_not_ge (Nat.find_min hex (show n0<N by omega))
  have hmSum : Summable (fun j=>crossMass v w (j+n0)) :=
    (summable_nat_add_iff n0).mpr (crossMass_summable v w)
  have heSum : Summable (fun j=>crossMass v w (j+n0)*(1-rho v w (j+n0))) :=
    (summable_nat_add_iff n0).mpr (pairDeficit_summable v w hd)
  have hmass : η<(∑' j,crossMass v w (j+n0)) := by
    have hsplit := (crossMass_summable v w).sum_add_tsum_nat_add n0
    rw [←crossBelow_eq_sum,crossMass_tsum] at hsplit
    change crossBelow v w n0+(∑' j,crossMass v w (j+n0))=c at hsplit
    linarith
  have hdef : (∑' j,crossMass v w (j+n0)*(1-rho v w (j+n0)))≤pairDeficit v w := by
    have hsplit := (pairDeficit_summable v w hd).sum_add_tsum_nat_add n0
    have hnon : 0≤(∑ j ∈ Finset.range n0,crossMass v w j*(1-rho v w j)) :=
      Finset.sum_nonneg (fun j _=>mul_nonneg (hd j) (sub_nonneg.mpr (rho_bounds v w hd j).2))
    change _=pairDeficit v w at hsplit
    linarith
  obtain ⟨j,hjpos,hjgood⟩ := summable_grade_choice (fun j=>hd (j+n0)) hmSum heSum
    (pairDeficit_nonneg v w hd) hη hmass hdef
  refine ⟨j+n0,?_,hjpos,hjgood⟩
  exact hN.trans (crossBelow_monotone v w hd (show N≤j+n0+1 by omega))

end SphericalAging.TreeGradeSelection
