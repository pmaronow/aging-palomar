module

public import SphericalAging.PurePFieldObstacle
public import SphericalAging.UniformPartialQuadrature

public section

/-! The genuine low-field matching profile has the exact printed ALG value.
Its finite obstacle sums have an explicit vanishing mesh error. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SphericalAging.PurePFieldContinuumProfile
open UniformMonotoneQuadrature UniformPartialQuadrature PurePBranchingVariationalBound
open PurePBranchingContinuumBound PurePFieldObstacle ExternalFieldElementaryPenalty
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

@[expose] def matchingValue (p : ℕ) (t : ℝ) : ℝ := t*curvatureRoot p t+∫x in t..1,curvatureRoot p x
@[expose] def lowFieldValue (p : ℕ) (t : ℝ) : ℝ := thresholdEnergy p+
  ((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1))*t^((p:ℝ)/2)

theorem curvatureRoot_integral_prefix {p : ℕ} (hp : 3≤p) {t : ℝ} (ht : 0≤t) :
    (∫x in (0:ℝ)..t,curvatureRoot p x)=
      2*Real.sqrt ((p:ℝ)*((p:ℝ)-1))/(p:ℝ)*t^((p:ℝ)/2) := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have he : (∫x in (0:ℝ)..t,curvatureRoot p x)=
      ∫x in (0:ℝ)..t,Real.sqrt ((p:ℝ)*((p:ℝ)-1))*x^(((p:ℝ)-2)/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ht] at hx
    exact curvatureRoot_eq_rpow (by omega) hx.1
  rw [he,intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith),sub_zero]
  rw [show ((p:ℝ)-2)/2+1=(p:ℝ)/2 by ring]
  field_simp [(by linarith : (p:ℝ)≠0)]

theorem root_times_argument {p : ℕ} (hp : 3≤p) {t : ℝ} (ht : 0≤t) :
    t*curvatureRoot p t=Real.sqrt ((p:ℝ)*((p:ℝ)-1))*t^((p:ℝ)/2) := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  rw [curvatureRoot_eq_rpow (by omega) ht]
  have he : t^((p:ℝ)/2)=t^(((p:ℝ)-2)/2)*t := by
    rw [show (p:ℝ)/2=((p:ℝ)-2)/2+1 by ring,
      Real.rpow_add_of_nonneg ht (by linarith) (by norm_num),Real.rpow_one]
  rw [he]
  ring

theorem matchingValue_eq_lowFieldValue {p : ℕ} (hp : 3≤p) {t : ℝ} (ht : 0≤t) :
    matchingValue p t=lowFieldValue p t := by
  have hg := curvatureRoot_continuous p
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ:=volume) (0:ℝ) t) (hg.intervalIntegrable (μ:=volume) t 1)
  rw [curvatureRoot_integral hp,curvatureRoot_integral_prefix hp ht] at hsplit
  unfold matchingValue lowFieldValue
  rw [root_times_argument hp ht]
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have he : (1-2/(p:ℝ))=((p:ℝ)-2)/(p:ℝ) := by field_simp [(by linarith : (p:ℝ)≠0)]
  rw [←he]
  linear_combination hsplit

theorem matched_fieldOrder {p : ℕ} (hp : 3≤p) {t : ℝ} (ht : 0≤t) :
    fieldOrder p (Real.sqrt (fieldSquared p t))=t := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hb : 0≤fieldSquared p t := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (by linarith)) (pow_nonneg ht _)
  have hbase : (p:ℝ)*((p:ℝ)-2)≠0 := ne_of_gt (mul_pos (by linarith) (by linarith))
  unfold fieldOrder
  rw [Real.sq_sqrt hb]
  have hr : fieldSquared p t/((p:ℝ)*((p:ℝ)-2))=t^(p-1) := by
    unfold fieldSquared
    field_simp [(by linarith : (p:ℝ)≠0),(by linarith : (p:ℝ)-2≠0)]
  rw [hr,←Real.rpow_natCast,←Real.rpow_mul ht]
  have hc : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  rw [hc,show ((p:ℝ)-1)*(1/((p:ℝ)-1))=1 by
    field_simp [(by linarith : (p:ℝ)-1≠0)],Real.rpow_one]

theorem lowFieldValue_eq_algorithmicField {p : ℕ} (hp : 3≤p) {t : ℝ} (ht : t∈Icc 0 1) :
    lowFieldValue p t=algorithmicField p (Real.sqrt (fieldSquared p t)) := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hb : 0≤fieldSquared p t := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (by linarith)) (pow_nonneg ht.1 _)
  have hlow : (Real.sqrt (fieldSquared p t))^2≤(p:ℝ)*((p:ℝ)-2) := by
    rw [Real.sq_sqrt hb]
    unfold fieldSquared
    exact mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg p) (by linarith)) (pow_le_one₀ ht.1 ht.2)
  rw [algorithmicField,ite_eq_left hlow,matched_fieldOrder hp ht.1]
  rfl

theorem obstacle_term_below {p D cut : ℕ} (hp : 2≤p) (hD : 0<D) (hcut : 0<cut)
    {i : ℕ} (hi : i<cut) :
    Real.sqrt ((1/(D:ℝ))*(obstacleMass p D cut (i+1)-obstacleMass p D cut i))=
      (1/(D:ℝ))*curvatureRoot p (grid D cut) := by
  rw [obstacle_increment_below p D hi]
  unfold curvatureRoot
  rw [show (1/(D:ℝ))*((1/(D:ℝ))*curvature p (grid D cut))=
      (1/(D:ℝ))^2*curvature p (grid D cut) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0≤1/(D:ℝ))]

theorem obstacleSum_le_matchingValue_add_mesh {p D cut : ℕ} (hp : 3≤p) (hD : 0<D)
    (hcut : 0<cut) (hcutD : cut ≤ D) :
    obstacleSum p D cut≤matchingValue p (grid D cut)+
      Real.sqrt ((p:ℝ)*((p:ℝ)-1))/(D:ℝ) := by
  let g := curvatureRoot p
  have hg : Continuous g := curvatureRoot_continuous p
  have hgm : MonotoneOn g (Icc 0 1) := (curvatureRoot_monotoneOn (by omega : 2≤p)).mono Icc_subset_Ici_self
  have hpre : (∑i∈Finset.range cut,
      Real.sqrt ((1/(D:ℝ))*(obstacleMass p D cut (i+1)-obstacleMass p D cut i)))=
        grid D cut*g (grid D cut) := by
    rw [Finset.sum_congr rfl (fun i hi => obstacle_term_below (by omega) hD hcut (Finset.mem_range.mp hi))]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    unfold grid
    ring
  have hpost : (∑i∈Finset.Ico cut D,
      Real.sqrt ((1/(D:ℝ))*(obstacleMass p D cut (i+1)-obstacleMass p D cut i)))≤
      ∑i∈Finset.Ico cut D,(1/(D:ℝ))*g (grid D (i+1)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [obstacle_increment_above (by omega) D (Finset.mem_Ico.mp hi).1]
    exact reference_term_le_right (by omega) hD i
  have hright := right_sum_le_integral_add hD g hg hgm
  have hprefix := integral_le_right_partial_sum hD hcutD g hg hgm
  rw [←Finset.sum_range_add_sum_Ico _ hcutD] at hright
  have hg0 : g 0=0 := by simp [g,curvatureRoot,curvature,show p-2≠0 by omega]
  have hg1 : g 1=Real.sqrt ((p:ℝ)*((p:ℝ)-1)) := by simp [g,curvatureRoot,curvature]
  rw [hg0,hg1,sub_zero] at hright
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ:=volume) (0:ℝ) (grid D cut))
    (hg.intervalIntegrable (μ:=volume) (grid D cut) 1)
  unfold obstacleSum
  rw [←Finset.sum_range_add_sum_Ico _ hcutD,hpre]
  unfold matchingValue
  change grid D cut*g (grid D cut)+_≤grid D cut*g (grid D cut)+_+_
  linarith

theorem obstacleSum_le_algorithmicField_add_mesh {p D cut : ℕ} (hp : 3≤p) (hD : 0<D)
    (hcut : 0<cut) (hcutD : cut ≤ D) :
    obstacleSum p D cut≤algorithmicField p (Real.sqrt (fieldSquared p (grid D cut)))+
      Real.sqrt ((p:ℝ)*((p:ℝ)-1))/(D:ℝ) := by
  have h := obstacleSum_le_matchingValue_add_mesh hp hD hcut hcutD
  rw [matchingValue_eq_lowFieldValue hp (grid_nonneg D cut),
    lowFieldValue_eq_algorithmicField hp (grid_mem hD hcutD)] at h
  exact h

end SphericalAging.PurePFieldContinuumProfile
