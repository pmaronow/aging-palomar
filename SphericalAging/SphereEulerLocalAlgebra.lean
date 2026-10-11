module

public import SphericalAging.SphereEulerInterpolationAlgebra

public section

/-! The exact local Euler defect is one genuine Brownian elementary block. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped BigOperators NNReal InnerProductSpace
namespace SphericalAging.SphereEulerLocalAlgebra
open HardSphereDynamics SphereEulerCoefficients SphereEulerPredictable SphereEulerInterpolationAlgebra
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
variable (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p) (x : State N)

theorem interpolant_sub_node {M k : ℕ} (hk : k<M) {t : ℝ≥0}
    (ht : t∈Ioc (grid h k) (grid h (k+1))) (omega : Ω) :
    interpolant D β h J x M t omega-node D β h J x k omega=block D β h J x k t omega := by
  have he : interpolant D β h J x M t omega-node D β h J x k omega=
      ∑j ∈ Finset.range M,(block D β h J x j t omega-block D β h J x j (grid h k) omega) := by
    rw [←interpolant_grid D β h J x (Nat.le_of_lt hk) omega]
    unfold interpolant
    rw [Finset.sum_sub_distrib]
    abel
  rw [he,Finset.sum_eq_single k]
  · rw [block_eq_zero D β h J x le_rfl,sub_zero]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with hjk|hkj
    · have hbefore := grid_mono h (Nat.succ_le_of_lt hjk)
      rw [block_eq_full D β h J x (hbefore.trans ht.1.le),
        block_eq_full D β h J x hbefore,sub_self]
    · have hafter := grid_mono h (Nat.succ_le_of_lt hkj)
      rw [block_eq_zero D β h J x (ht.2.trans hafter),
        block_eq_zero D β h J x ((grid_mono h (Nat.le_succ k)).trans hafter),sub_self]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hk))

theorem local_time_gap_le {k : ℕ} {t : ℝ≥0}
    (ht : t∈Ioc (grid h k) (grid h (k+1))) :
    0≤(t:ℝ)-(grid h k:ℝ) ∧ (t:ℝ)-(grid h k:ℝ)≤h := by
  have hg := grid_gap h k
  exact ⟨sub_nonneg.mpr ht.1.le,by have hh : (t:ℝ)≤grid h (k+1) := ht.2;linarith⟩
end SphericalAging.SphereEulerLocalAlgebra
