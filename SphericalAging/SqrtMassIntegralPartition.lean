module

public import SphericalAging.UniformMonotoneQuadrature
public import SphericalAging.ResponseTransport

public section

/-! A genuine integrable nonnegative density is compared with its actual
cumulative-mass finite sums by interval Cauchy--Schwarz. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SphericalAging.SqrtMassIntegralPartition
open UniformMonotoneQuadrature
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

@[expose] def mass (a : ℝ→ℝ) (x : ℝ) : ℝ := ∫y in (0:ℝ)..x,a y

theorem mass_increment {D : ℕ} (hD : 0<D) (a : ℝ→ℝ)
    (ha : IntervalIntegrable a volume 0 1) {i : ℕ} (hi : i<D) :
    mass a (grid D (i+1))-mass a (grid D i)=∫x in grid D i..grid D (i+1),a x := by
  have hm i' (hi' : i'≤D) : grid D i'∈Icc 0 1 := grid_mem hD hi'
  have h0i := ha.mono_set (by
    rw [uIcc_of_le (grid_nonneg D i),uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc le_rfl (hm i hi.le).2)
  have hii := ha.mono_set (by
    rw [uIcc_of_le (grid_strictMono hD (Nat.lt_succ_self i)).le,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc (grid_nonneg D i) (hm (i+1) (by omega)).2)
  have h := intervalIntegral.integral_add_adjacent_intervals h0i hii
  unfold mass
  linarith

theorem mass_increment_nonneg {D : ℕ} (hD : 0<D) (a : ℝ→ℝ)
    (ha : IntervalIntegrable a volume 0 1) (han : ∀x∈Icc 0 1,0≤a x) {i : ℕ} (hi : i<D) :
    0≤mass a (grid D (i+1))-mass a (grid D i) := by
  rw [mass_increment hD a ha hi]
  apply intervalIntegral.integral_nonneg
    (grid_strictMono hD (Nat.lt_succ_self i)).le
  intro x hx
  exact han x ⟨(grid_nonneg D i).trans hx.1,
    hx.2.trans (grid_mem hD (by omega : i+1≤D)).2⟩

theorem integral_sqrt_le_cumulative_sum {D : ℕ} (hD : 0<D) (a : ℝ→ℝ)
    (ha : IntervalIntegrable a volume 0 1) (han : ∀x∈Icc 0 1,0≤a x)
    (hs : IntervalIntegrable (fun x => Real.sqrt (a x)) volume 0 1) :
    (∫x in (0:ℝ)..1,Real.sqrt (a x))≤
      ∑i∈Finset.range D,Real.sqrt ((1/(D:ℝ))*(mass a (grid D (i+1))-mass a (grid D i))) := by
  have hcell i (hi : i<D) : uIcc (grid D i) (grid D (i+1))⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (grid_strictMono hD (Nat.lt_succ_self i)).le,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc (grid_nonneg D i) (grid_mem hD (by omega : i+1≤D)).2
  calc
    _=∑i∈Finset.range D,∫x in grid D i..grid D (i+1),Real.sqrt (a x) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hs.mono_set (hcell i hi)),
        grid_zero,grid_self hD]
    _≤_ := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hat := ha.mono_set (hcell i hi')
      have hsqt : IntervalIntegrable (fun x => Real.sqrt (a x)^2) volume (grid D i) (grid D (i+1)) := by
        apply hat.congr
        intro x hx
        rw [uIoc_of_le (grid_strictMono hD (Nat.lt_succ_self i)).le] at hx
        exact (Real.sq_sqrt (han x ⟨(grid_nonneg D i).trans hx.1.le,
          hx.2.trans (grid_mem hD (by omega : i+1≤D)).2⟩)).symm
      have h := ResponseTransport.interval_square_bound (grid_strictMono hD (Nat.lt_succ_self i))
        (hs.mono_set (hcell i hi')) hsqt
      have he : (∫x in grid D i..grid D (i+1),Real.sqrt (a x)^2)=
          ∫x in grid D i..grid D (i+1),a x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact Real.sq_sqrt (han x (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using (hcell i hi') hx))
      rw [he,grid_succ_sub,←mass_increment hD a ha hi'] at h
      exact Real.le_sqrt_of_sq_le h

end SphericalAging.SqrtMassIntegralPartition
