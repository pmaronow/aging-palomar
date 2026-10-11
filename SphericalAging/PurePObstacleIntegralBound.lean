module

public import SphericalAging.PurePFieldContinuumProfile
public import SphericalAging.SqrtMassIntegralPartition
public import SphericalAging.UpperUnitGrid

public section

/-! A true nonnegative density with the pure-p cumulative obstacle has the
printed low-field variational ceiling. The grids and their limits are constructed;
neither a variational bound nor a finite-sum convergence is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace SphericalAging.PurePObstacleIntegralBound
open UniformMonotoneQuadrature PurePBranchingVariationalBound PurePBranchingContinuumBound
open PurePFieldObstacle PurePFieldContinuumProfile SqrtMassIntegralPartition ExternalFieldElementaryPenalty
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem fieldSquared_monotoneOn {p : ℕ} (hp : 3≤p) : MonotoneOn (fieldSquared p) (Ici 0) := by
  intro x hx y hy hxy
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _)
    (mul_nonneg (Nat.cast_nonneg p) (by linarith))

theorem lowFieldValue_continuous {p : ℕ} (hp : 3≤p) : Continuous (lowFieldValue p) := by
  exact continuous_const.add ((continuous_const.mul continuous_const).mul
    (Real.continuous_rpow_const (by positivity : 0≤(p:ℝ)/2)))

theorem integral_sqrt_le_lowFieldValue {p : ℕ} (hp : 3≤p) (a : ℝ→ℝ)
    (ha : IntervalIntegrable a volume 0 1) (han : ∀x∈Icc 0 1,0≤a x)
    (hs : IntervalIntegrable (fun x => Real.sqrt (a x)) volume 0 1)
    {κ t : ℝ} (ht : t∈Icc 0 1) (hfield : κ^2≤fieldSquared p t)
    (hcap : ∀x∈Icc 0 1,mass a x≤κ^2+prime p x) :
    (∫x in (0:ℝ)..1,Real.sqrt (a x))≤lowFieldValue p t := by
  have hbound (n : ℕ) : (∫x in (0:ℝ)..1,Real.sqrt (a x))≤
      lowFieldValue p (UpperUnitGrid.point (n+1) t)+Real.sqrt ((p:ℝ)*((p:ℝ)-1))/((n+1:ℕ):ℝ) := by
    have hD : 0<n+1 := by omega
    let j := UpperUnitGrid.cut (n+1) t
    have hj : 0<j := UpperUnitGrid.cut_pos _ _
    have hjD : j≤n+1 := UpperUnitGrid.cut_le hD ht
    have hpt : t≤grid (n+1) j := UpperUnitGrid.le_point hD t
    have hm := hfield.trans (fieldSquared_monotoneOn hp ht.1 (grid_nonneg (n+1) j) hpt)
    have hzero : mass a (grid (n+1) 0)=0 := by simp [mass,grid_zero]
    have hc := cumulative_sqrt_sum_le_obstacle (by omega : 2≤p) hD hj hjD
      (fun i => mass a (grid (n+1) i)) hzero
      (fun i hi => mass_increment_nonneg hD a ha han hi)
      (fun i hi hiD => by have hh := hcap _ (grid_mem hD hiD);linarith)
    have hl := (integral_sqrt_le_cumulative_sum hD a ha han hs).trans hc
    have ho := obstacleSum_le_matchingValue_add_mesh hp hD hj hjD
    rw [matchingValue_eq_lowFieldValue hp (grid_nonneg (n+1) j)] at ho
    exact hl.trans ho
  have hpoint := UpperUnitGrid.point_tendsto t ht.1
  have hmesh : Tendsto (fun n : ℕ => Real.sqrt ((p:ℝ)*((p:ℝ)-1))/((n+1:ℕ):ℝ))
      atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hl := ((lowFieldValue_continuous hp).tendsto t).comp hpoint
  have hlim := hl.add hmesh
  simp only [add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

theorem integral_sqrt_le_algorithmicField_matched {p : ℕ} (hp : 3≤p) (a : ℝ→ℝ)
    (ha : IntervalIntegrable a volume 0 1) (han : ∀x∈Icc 0 1,0≤a x)
    (hs : IntervalIntegrable (fun x => Real.sqrt (a x)) volume 0 1)
    {t : ℝ} (ht : t∈Icc 0 1)
    (hcap : ∀x∈Icc 0 1,mass a x≤fieldSquared p t+prime p x) :
    (∫x in (0:ℝ)..1,Real.sqrt (a x))≤algorithmicField p (Real.sqrt (fieldSquared p t)) := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hb : 0≤fieldSquared p t := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg p) (by linarith)) (pow_nonneg ht.1 _)
  have h := integral_sqrt_le_lowFieldValue hp a ha han hs ht
    (by rw [Real.sq_sqrt hb]) (by simpa only [Real.sq_sqrt hb] using hcap)
  rw [lowFieldValue_eq_algorithmicField hp ht] at h
  exact h

end SphericalAging.PurePObstacleIntegralBound
