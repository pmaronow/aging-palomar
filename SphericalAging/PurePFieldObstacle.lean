module

public import SphericalAging.PurePBranchingContinuumBound
public import SphericalAging.FiniteObstacleVariationalComparison

public section

/-! The actual low-field pure-p obstacle: a matching straight line below t
and κ²+ξ' above t, where κ²=p(p−2)t^(p−1). Its dual slopes and the cumulative
comparison are proved directly from the monomial. -/
noncomputable section
open Set
open scoped BigOperators
namespace SphericalAging.PurePFieldObstacle
open UniformMonotoneQuadrature PurePBranchingVariationalBound
open PurePBranchingContinuumBound FiniteObstacleVariationalComparison
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

@[expose] def fieldSquared (p : ℕ) (t : ℝ) : ℝ := (p:ℝ)*((p:ℝ)-2)*t^(p-1)
@[expose] def obstacleMass (p D cut i : ℕ) : ℝ :=
  if i ≤ cut then curvature p (grid D cut)*grid D i
  else fieldSquared p (grid D cut)+prime p (grid D i)
@[expose] def obstacleSum (p D cut : ℕ) : ℝ :=
  ∑i∈Finset.range D,Real.sqrt ((1/(D:ℝ))*(obstacleMass p D cut (i+1)-obstacleMass p D cut i))

theorem matching_identity {p : ℕ} (hp : 2≤p) (t : ℝ) :
    curvature p t*t=fieldSquared p t+prime p t := by
  have he : p-1=p-2+1 := by omega
  unfold curvature fieldSquared prime
  rw [he,pow_succ]
  ring

theorem obstacleMass_zero (p D cut : ℕ) : obstacleMass p D cut 0=0 := by
  simp [obstacleMass,grid_zero]
theorem obstacleMass_of_le (p D : ℕ) {cut i : ℕ} (hi : i ≤ cut) :
    obstacleMass p D cut i=curvature p (grid D cut)*grid D i := by simp [obstacleMass,hi]
theorem obstacleMass_of_ge {p : ℕ} (hp : 2≤p) (D : ℕ) {cut i : ℕ} (hi : cut ≤ i) :
    obstacleMass p D cut i=fieldSquared p (grid D cut)+prime p (grid D i) := by
  by_cases h : i ≤ cut
  · have he : i=cut := le_antisymm h hi
    subst i
    simp only [obstacleMass,le_refl,ite_true]
    exact matching_identity hp _
  · simp [obstacleMass,h]

theorem obstacle_increment_below (p D : ℕ) {cut i : ℕ} (hi : i < cut) :
    obstacleMass p D cut (i+1)-obstacleMass p D cut i=
      (1/(D:ℝ))*curvature p (grid D cut) := by
  rw [obstacleMass_of_le p D (by omega),obstacleMass_of_le p D hi.le]
  rw [←mul_sub,grid_succ_sub]
  ring
theorem obstacle_increment_above {p : ℕ} (hp : 2≤p) (D : ℕ) {cut i : ℕ} (hi : cut ≤ i) :
    obstacleMass p D cut (i+1)-obstacleMass p D cut i=
      prime p (grid D (i+1))-prime p (grid D i) := by
  rw [obstacleMass_of_ge hp D (by omega),obstacleMass_of_ge hp D hi]
  ring

theorem curvature_pos {p : ℕ} (hp : 2≤p) {x : ℝ} (hx : 0<x) : 0<curvature p x := by
  have hpR : 2≤(p:ℝ) := by exact_mod_cast hp
  unfold curvature
  exact mul_pos (mul_pos (by linarith) (by linarith)) (pow_pos hx _)

theorem obstacle_increment_pos {p D cut : ℕ} (hp : 2≤p) (hD : 0<D) (hcut : 0<cut) (i : ℕ) :
    0<obstacleMass p D cut (i+1)-obstacleMass p D cut i := by
  by_cases h : i < cut
  · rw [obstacle_increment_below p D h]
    exact mul_pos (by positivity) (curvature_pos hp (by
      unfold grid;exact div_pos (Nat.cast_pos.mpr hcut) (Nat.cast_pos.mpr hD)))
  · rw [obstacle_increment_above hp D (by omega)]
    exact reference_increment_pos hp hD i

theorem reference_increment_ge_left {p D : ℕ} (hp : 2≤p) (hD : 0<D) (i : ℕ) :
    (1/(D:ℝ))*curvature p (grid D i)≤prime p (grid D (i+1))-prime p (grid D i) := by
  have hxy := grid_strictMono hD (Nat.lt_succ_self i)
  have hcont : Continuous (prime p) := continuous_const.mul (continuous_id.pow (p-1))
  obtain ⟨u,hu,he⟩ := exists_deriv_eq_slope (prime p) hxy hcont.continuousOn
    (fun u hu => (prime_hasDerivAt hp u).differentiableAt.differentiableWithinAt)
  rw [(prime_hasDerivAt hp u).deriv] at he
  have hc : curvature p (grid D i)≤curvature p u :=
    curvature_monotoneOn hp (grid_nonneg D i) ((grid_nonneg D i).trans hu.1.le) hu.1.le
  rw [he,grid_succ_sub] at hc
  have hh := (le_div_iff₀ (by positivity : 0<1/(D:ℝ))).mp hc
  simpa only [mul_comm] using hh

theorem obstacle_increment_monotone {p D cut : ℕ} (hp : 2≤p) (hD : 0<D) (i : ℕ) :
    obstacleMass p D cut (i+1)-obstacleMass p D cut i≤
      obstacleMass p D cut (i+2)-obstacleMass p D cut (i+1) := by
  by_cases h : i+1 < cut
  · rw [obstacle_increment_below p D (i:=i) (by omega),
      show obstacleMass p D cut (i+2)-obstacleMass p D cut (i+1)=_
        from obstacle_increment_below p D h]
  · by_cases hi : cut ≤ i
    · rw [obstacle_increment_above hp D hi,
        show obstacleMass p D cut (i+2)-obstacleMass p D cut (i+1)=_
          from obstacle_increment_above hp D (by omega)]
      exact reference_increment_monotone hD i
    · have hc : cut=i+1 := by omega
      rw [obstacle_increment_below p D (i:=i) (by omega),
        show obstacleMass p D cut (i+2)-obstacleMass p D cut (i+1)=_
          from obstacle_increment_above hp D (by omega),hc]
      exact reference_increment_ge_left hp hD (i+1)

theorem cumulative_sqrt_sum_le_obstacle {p D cut : ℕ} (hp : 2≤p) (hD : 0<D)
    (hcut : 0<cut) (hcutD : cut ≤ D) (A : ℕ→ℝ) (hzero : A 0=0)
    (hA : ∀i<D,0≤A (i+1)-A i)
    (hcap : ∀ i, cut ≤ i → i ≤ D → A i≤fieldSquared p (grid D cut)+prime p (grid D i)) :
    (∑i∈Finset.range D,Real.sqrt ((1/(D:ℝ))*(A (i+1)-A i)))≤obstacleSum p D cut := by
  apply sqrt_increment_sum_le_above_cut (fun _ => 1/(D:ℝ)) A (obstacleMass p D cut) D cut hcutD
    (fun i hi => by positivity) hA (fun i hi => obstacle_increment_pos hp hD hcut i)
  · rw [hzero,obstacleMass_zero]
  · intro i hi hiD
    rw [obstacleMass_of_ge hp D hi]
    exact hcap i hi hiD
  · intro i hi
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr (obstacle_increment_pos hp hD hcut i)))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (obstacle_increment_monotone hp hD i)) (by norm_num))
  · intro i hi
    rw [obstacle_increment_below p D (i:=i) (by omega),
      show obstacleMass p D cut (i+2)-obstacleMass p D cut (i+1)=_
        from obstacle_increment_below p D hi]

end SphericalAging.PurePFieldObstacle
