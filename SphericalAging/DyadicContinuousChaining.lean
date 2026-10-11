module

public import StochasticCalculus.ItoMaximal
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

public section

/-! Deterministic dyadic chaining for genuine continuous sample paths.
The estimate controls a whole compact interval by adjacent grid increments. -/
noncomputable section
open Set Filter Topology StochasticCalculus
open scoped NNReal
namespace SphericalAging.DyadicContinuousChaining
set_option maxHeartbeats 800000

@[expose] def timeApprox (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) : ℝ≥0 :=
  uniformPartitionTime T (2^n) (dyadicApproxIndex s T n)

theorem dyadicApproxIndex_parent (s T : ℝ≥0) (n : ℕ) :
    dyadicApproxIndex s T (n+1)/2 = dyadicApproxIndex s T n := by
  unfold dyadicApproxIndex
  rw [pow_succ,←mul_assoc]
  exact Nat.mul_cast_floor_div_cancel (by decide : (2:ℕ)≠0) _

theorem uniformPartitionTime_double (T : ℝ≥0) (n k : ℕ) :
    uniformPartitionTime T (2^(n+1)) (2*k) = uniformPartitionTime T (2^n) k := by
  unfold uniformPartitionTime
  push_cast
  rw [pow_succ]
  field_simp
  <;> ring

theorem timeApprox_step_le {E : Type*} [PseudoMetricSpace E]
    (f : ℝ≥0 → E) (T : ℝ≥0) (s : ℝ≥0) (hs : s ≤ T) (n : ℕ) (d : ℝ)
    (hd : 0 ≤ d)
    (hstep : ∀ k : ℕ, k < 2^(n+1) →
      dist (f (uniformPartitionTime T (2^(n+1)) k))
        (f (uniformPartitionTime T (2^(n+1)) (k+1))) ≤ d) :
    dist (f (timeApprox T n s)) (f (timeApprox T (n+1) s)) ≤ d := by
  let k := dyadicApproxIndex s T (n+1)
  let j := dyadicApproxIndex s T n
  have hdiv : k/2=j := dyadicApproxIndex_parent s T n
  have hk : k ≤ 2^(n+1) := dyadicApproxIndex_le_pow hs (n+1)
  have hrem : k=2*j ∨ k=2*j+1 := by omega
  rcases hrem with he|ho
  · change dist (f (uniformPartitionTime T (2^n) j))
      (f (uniformPartitionTime T (2^(n+1)) k)) ≤ d
    rw [←uniformPartitionTime_double T n j]
    change dist (f (uniformPartitionTime T (2^(n+1)) (2*j)))
      (f (uniformPartitionTime T (2^(n+1)) k)) ≤ d
    rw [he,dist_self]
    exact hd
  · change dist (f (uniformPartitionTime T (2^n) j))
      (f (uniformPartitionTime T (2^(n+1)) k)) ≤ d
    rw [←uniformPartitionTime_double T n j]
    change dist (f (uniformPartitionTime T (2^(n+1)) (2*j)))
      (f (uniformPartitionTime T (2^(n+1)) k)) ≤ d
    rw [ho]
    exact hstep (2*j) (by omega)

theorem path_distance_to_grid_le_tail {E : Type*} [PseudoMetricSpace E]
    (f : ℝ≥0 → E) (hf : Continuous f) (T : ℝ≥0) (d : ℕ → ℝ)
    (hd : ∀n,0 ≤ d n) (hsum : Summable d)
    (hstep : ∀n k : ℕ,k < 2^n →
      dist (f (uniformPartitionTime T (2^n) k))
        (f (uniformPartitionTime T (2^n) (k+1))) ≤ d n)
    (m : ℕ) (s : ℝ≥0) (hs : s ≤ T) :
    dist (f (timeApprox T m s)) (f s) ≤ ∑'j : ℕ,d (m+j+1) := by
  have hsumm : Summable (fun j : ℕ => d (m+j+1)) := by
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      (summable_nat_add_iff (m+1)).mpr hsum
  have ht : Tendsto (fun i : ℕ => f (timeApprox T (m+i) s)) atTop (𝓝 (f s)) := by
    apply hf.continuousAt.tendsto.comp
    exact (tendsto_uniformPartitionTime_dyadicApproxIndex hs).comp (by simpa only [Nat.add_comm] using (tendsto_add_atTop_nat m))
  have hb (i : ℕ) : dist (f (timeApprox T m s)) (f (timeApprox T (m+i) s)) ≤
      ∑'j : ℕ,d (m+j+1) := by
    have hh := dist_le_range_sum_of_dist_le (f:=fun j : ℕ => f (timeApprox T (m+j) s)) i
      (d:=fun j : ℕ => d (m+j+1)) (fun {j} _ => by
        simpa only [Nat.add_assoc] using
          timeApprox_step_le f T s hs (m+j) (d (m+j+1)) (hd _) (hstep _))
    simp only [Nat.add_zero] at hh
    exact hh.trans (hsumm.sum_le_tsum (Finset.range i) (fun j _ => hd _))
  exact le_of_tendsto (tendsto_const_nhds.dist ht) (.of_forall hb)

end SphericalAging.DyadicContinuousChaining
