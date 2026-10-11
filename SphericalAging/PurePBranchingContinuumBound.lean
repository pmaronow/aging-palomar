module

public import SphericalAging.PurePBranchingVariationalBound

public section

/-! Exact continuum normalization and quantitative finite-mesh comparison
for the no-field pure-p branching functional. This proves the scalar limiting
ALG value from its actual increment functional. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace SphericalAging.PurePBranchingContinuumBound
open UniformMonotoneQuadrature PurePBranchingVariationalBound
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem curvatureRoot_continuous (p : ℕ) : Continuous (curvatureRoot p) := by
  exact Real.continuous_sqrt.comp ((continuous_const.mul continuous_const).mul (continuous_id.pow (p-2)))

theorem curvatureRoot_monotoneOn {p : ℕ} (hp : 2≤p) : MonotoneOn (curvatureRoot p) (Ici 0) := by
  intro x hx y hy hxy
  exact Real.sqrt_le_sqrt (curvature_monotoneOn hp hx hy hxy)

theorem curvatureRoot_eq_rpow {p : ℕ} (hp : 2≤p) {x : ℝ} (hx : 0≤x) :
    curvatureRoot p x=Real.sqrt ((p:ℝ)*((p:ℝ)-1))*x^(((p:ℝ)-2)/2) := by
  have hpR : 2≤(p:ℝ) := by exact_mod_cast hp
  unfold curvatureRoot curvature
  rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg p) (by linarith))]
  rw [Real.sqrt_eq_rpow (x^(p-2)),←Real.rpow_natCast x (p-2),←Real.rpow_mul hx]
  congr 2
  rw [Nat.cast_sub hp]
  push_cast
  ring

theorem curvatureRoot_integral {p : ℕ} (hp : 3≤p) :
    (∫x in (0:ℝ)..1,curvatureRoot p x)=ExternalFieldElementaryPenalty.thresholdEnergy p := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have he : (∫x in (0:ℝ)..1,curvatureRoot p x)=
      ∫x in (0:ℝ)..1,Real.sqrt ((p:ℝ)*((p:ℝ)-1))*x^(((p:ℝ)-2)/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hx
    exact curvatureRoot_eq_rpow (by omega) hx.1
  rw [he,intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith))]
  rw [Real.one_rpow,Real.zero_rpow (by linarith),sub_zero,ExternalFieldSharpScalar.thresholdEnergy_eq hp]
  field_simp [(by linarith : (p:ℝ)≠0)]
  ring

theorem reference_term_le_right {p D : ℕ} (hp : 2≤p) (hD : 0<D) (i : ℕ) :
    Real.sqrt ((1/(D:ℝ))*(prime p (grid D (i+1))-prime p (grid D i)))≤
      (1/(D:ℝ))*curvatureRoot p (grid D (i+1)) := by
  let x := grid D i
  let y := grid D (i+1)
  have hxy : x<y := grid_strictMono hD (Nat.lt_succ_self i)
  have hcont : Continuous (prime p) := continuous_const.mul (continuous_id.pow (p-1))
  obtain ⟨u,hu,he⟩ := exists_deriv_eq_slope (prime p) hxy hcont.continuousOn
    (fun u hu => (prime_hasDerivAt hp u).differentiableAt.differentiableWithinAt)
  rw [(prime_hasDerivAt hp u).deriv] at he
  have hcurv : curvature p u≤curvature p y :=
    curvature_monotoneOn hp ((grid_nonneg D i).trans hu.1.le) (grid_nonneg D (i+1)) hu.2.le
  have hstep : y-x=1/(D:ℝ) := grid_succ_sub D i
  have hb : prime p y-prime p x≤(1/(D:ℝ))*curvature p y := by
    rw [he,hstep] at hcurv
    have h := (div_le_iff₀ (by positivity : 0<1/(D:ℝ))).mp hcurv
    simpa only [mul_comm] using h
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb (by positivity : 0≤1/(D:ℝ)))
  have hc : 0≤curvature p y := by
    have hpR : 2≤(p:ℝ) := by exact_mod_cast hp
    unfold curvature
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (by linarith)) (pow_nonneg (grid_nonneg D (i+1)) _)
  have hr : Real.sqrt ((1/(D:ℝ))*((1/(D:ℝ))*curvature p y))=
      (1/(D:ℝ))*curvatureRoot p y := by
    unfold curvatureRoot
    rw [show (1/(D:ℝ))*((1/(D:ℝ))*curvature p y)=(1/(D:ℝ))^2*curvature p y by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0≤1/(D:ℝ))]
  rw [hr] at hs
  exact hs

theorem referenceSum_le_threshold_add_mesh {p D : ℕ} (hp : 3≤p) (hD : 0<D) :
    referenceSum p D≤ExternalFieldElementaryPenalty.thresholdEnergy p+
      Real.sqrt ((p:ℝ)*((p:ℝ)-1))/(D:ℝ) := by
  have hsum : referenceSum p D≤∑i∈Finset.range D,(1/(D:ℝ))*curvatureRoot p (grid D (i+1)) := by
    exact Finset.sum_le_sum (fun i hi => reference_term_le_right (by omega) hD i)
  have hquad := right_sum_le_integral_add hD (curvatureRoot p) (curvatureRoot_continuous p)
    ((curvatureRoot_monotoneOn (by omega : 2≤p)).mono Icc_subset_Ici_self)
  have hzero : curvatureRoot p 0=0 := by simp [curvatureRoot,curvature,show p-2≠0 by omega]
  have hone : curvatureRoot p 1=Real.sqrt ((p:ℝ)*((p:ℝ)-1)) := by simp [curvatureRoot,curvature]
  rw [curvatureRoot_integral hp,hzero,hone,sub_zero] at hquad
  exact hsum.trans hquad

theorem branchingSum_le_threshold_add_mesh {p D : ℕ} (hp : 3≤p) (hD : 0<D)
    (c : ℕ→ℝ) (hc : ∀i,0≤c i ∧ c i≤1) (hcm : Monotone c) :
    branchingSum p D c≤ExternalFieldElementaryPenalty.thresholdEnergy p+
      Real.sqrt ((p:ℝ)*((p:ℝ)-1))/(D:ℝ) :=
  (branchingSum_le_referenceSum (by omega) hD c hc hcm).trans (referenceSum_le_threshold_add_mesh hp hD)

end SphericalAging.PurePBranchingContinuumBound
