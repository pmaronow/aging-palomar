module

public import SphericalAging.FiniteBranchingVariationalComparison
public import SphericalAging.UniformMonotoneQuadrature
public import SphericalAging.ExternalFieldSharpScalar
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

/-! The literal pure-p deterministic branching functional. Actual admissible
correlation schedules are compared with the fully correlated schedule, and
its finite sums are bounded by a continuum integral plus an explicit mesh error.
The Gaussian small-increment estimate is a separate preceding ingredient. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace SphericalAging.PurePBranchingVariationalBound
open UniformMonotoneQuadrature FiniteBranchingVariationalComparison
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

@[expose] def prime (p : ℕ) (x : ℝ) : ℝ := (p:ℝ)*x^(p-1)
@[expose] def curvature (p : ℕ) (x : ℝ) : ℝ := (p:ℝ)*((p:ℝ)-1)*x^(p-2)
@[expose] def curvatureRoot (p : ℕ) (x : ℝ) : ℝ := Real.sqrt (curvature p x)
@[expose] def cumulative (p D : ℕ) (c : ℕ→ℝ) (i : ℕ) : ℝ := c i*prime p (grid D i)
@[expose] def branchingSum (p D : ℕ) (c : ℕ→ℝ) : ℝ :=
  ∑i∈Finset.range D,Real.sqrt ((1/(D:ℝ))*(cumulative p D c (i+1)-cumulative p D c i))
@[expose] def referenceSum (p D : ℕ) : ℝ :=
  ∑i∈Finset.range D,Real.sqrt ((1/(D:ℝ))*(prime p (grid D (i+1))-prime p (grid D i)))

theorem prime_nonneg (p : ℕ) {x : ℝ} (hx : 0≤x) : 0≤prime p x := by unfold prime;positivity
theorem prime_monotoneOn (p : ℕ) : MonotoneOn (prime p) (Ici 0) := by
  intro x hx y hy hxy
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (Nat.cast_nonneg p)
theorem prime_strictMonoOn {p : ℕ} (hp : 2≤p) : StrictMonoOn (prime p) (Ici 0) := by
  intro x hx y hy hxy
  exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy hx (by omega)) (by exact_mod_cast (by omega : 0<p))
theorem prime_convex (p : ℕ) : ConvexOn ℝ (Ici 0) (prime p) := by
  refine ⟨convex_Ici _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := mul_le_mul_of_nonneg_left ((convexOn_pow (p-1) (𝕜:=ℝ)).2 hx hy ha hb hab)
    (Nat.cast_nonneg p)
  simp only [smul_eq_mul] at h ⊢
  unfold prime
  convert h using 1 <;> ring
theorem prime_hasDerivAt {p : ℕ} (hp : 2≤p) (x : ℝ) :
    HasDerivAt (prime p) (curvature p x) x := by
  have he : p-1-1=p-2 := by omega
  have hc : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  convert (hasDerivAt_pow (p-1) x).const_mul (p:ℝ) using 1
  · rfl
  · simp only [curvature,he,hc]
    ring

theorem curvature_monotoneOn {p : ℕ} (hp : 2≤p) : MonotoneOn (curvature p) (Ici 0) := by
  intro x hx y hy hxy
  have hpR : 2≤(p:ℝ) := by exact_mod_cast hp
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _)
    (mul_nonneg (Nat.cast_nonneg p) (by linarith))

theorem reference_increment_pos {p D : ℕ} (hp : 2≤p) (hD : 0<D) (i : ℕ) :
    0<prime p (grid D (i+1))-prime p (grid D i) := by
  exact sub_pos.mpr (prime_strictMonoOn hp (grid_nonneg D i) (grid_nonneg D (i+1))
    (grid_strictMono hD (Nat.lt_succ_self i)))

theorem reference_increment_monotone {p D : ℕ} (hD : 0<D) (i : ℕ) :
    prime p (grid D (i+1))-prime p (grid D i)≤
      prime p (grid D (i+2))-prime p (grid D (i+1)) := by
  have hs := (prime_convex p).slope_mono_adjacent (grid_nonneg D i) (grid_nonneg D (i+2))
    (grid_strictMono hD (Nat.lt_succ_self i)) (grid_strictMono hD (by omega : i+1 < i+2))
  rw [grid_succ_sub,show grid D (i+2)-grid D (i+1)=1/(D:ℝ) from grid_succ_sub D (i+1)] at hs
  exact (div_le_div_iff_of_pos_right (by positivity : 0<1/(D:ℝ))).mp hs

theorem branchingSum_le_referenceSum {p D : ℕ} (hp : 2≤p) (hD : 0<D) (c : ℕ→ℝ)
    (hc : ∀i,0≤c i ∧ c i≤1) (hcm : Monotone c) :
    branchingSum p D c≤referenceSum p D := by
  have hzero : cumulative p D c 0=prime p (grid D 0) := by
    simp [cumulative,prime,grid_zero,pow_zero,show p-1≠0 by omega]
  apply sqrt_increment_sum_le (fun _ => 1/(D:ℝ)) (cumulative p D c)
    (fun i => prime p (grid D i)) D
  · intro i hi;positivity
  · intro i hi
    apply sub_nonneg.mpr
    exact mul_le_mul (hcm (Nat.le_succ i))
      (prime_monotoneOn p (grid_nonneg D i) (grid_nonneg D (i+1))
        (grid_strictMono hD (Nat.lt_succ_self i)).le)
      (prime_nonneg p (grid_nonneg D i)) (hc (i+1)).1
  · intro i hi;exact reference_increment_pos hp hD i
  · exact hzero
  · intro i hi
    exact mul_le_of_le_one_left (prime_nonneg p (grid_nonneg D i)) (hc i).2
  · intro i hi
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr (reference_increment_pos hp hD i)))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (reference_increment_monotone hD i)) (by norm_num))

end SphericalAging.PurePBranchingVariationalBound
