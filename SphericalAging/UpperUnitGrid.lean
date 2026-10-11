module

public import SphericalAging.UniformMonotoneQuadrature
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! Constructed positive upper grid points for every t∈[0,1], including t=0. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.UpperUnitGrid
open UniformMonotoneQuadrature
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def cut (D : ℕ) (t : ℝ) : ℕ := max 1 ⌈(D:ℝ)*t⌉₊
@[expose] def point (D : ℕ) (t : ℝ) : ℝ := grid D (cut D t)

theorem cut_pos (D : ℕ) (t : ℝ) : 0<cut D t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
theorem cut_le {D : ℕ} (hD : 0<D) {t : ℝ} (ht : t∈Icc 0 1) : cut D t≤D := by
  unfold cut
  apply max_le
  · omega
  · have hm : (D:ℝ)*t≤(D:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg D)
    exact Nat.ceil_le.mpr hm
theorem point_mem {D : ℕ} (hD : 0<D) {t : ℝ} (ht : t∈Icc 0 1) : point D t∈Icc 0 1 :=
  grid_mem hD (cut_le hD ht)
theorem le_point {D : ℕ} (hD : 0<D) (t : ℝ) : t≤point D t := by
  unfold point grid
  apply (le_div_iff₀ (Nat.cast_pos.mpr hD)).mpr
  have hc : (⌈(D:ℝ)*t⌉₊:ℝ)≤(cut D t:ℝ) := Nat.cast_le.mpr (le_max_right _ _)
  have hh := (Nat.le_ceil ((D:ℝ)*t)).trans hc
  simpa only [mul_comm] using hh
theorem point_le_add_mesh {D : ℕ} (hD : 0<D) {t : ℝ} (ht : 0≤t) :
    point D t≤t+1/(D:ℝ) := by
  unfold point grid
  apply (div_le_iff₀ (Nat.cast_pos.mpr hD)).mpr
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg D) ht)).le
  have hone : (1:ℝ)≤(D:ℝ)*t+1 := by linarith [mul_nonneg (Nat.cast_nonneg D) ht]
  have hmax : (cut D t:ℝ)≤(D:ℝ)*t+1 := by
    unfold cut
    rw [Nat.cast_max,Nat.cast_one]
    exact max_le hone hceil
  have he : (t+1/(D:ℝ))*(D:ℝ)=(D:ℝ)*t+1 := by
    field_simp [(Nat.cast_pos.mpr hD).ne']
  rw [he]
  exact hmax

theorem point_tendsto (t : ℝ) (ht : 0≤t) :
    Tendsto (fun n : ℕ => point (n+1) t) atTop (𝓝 t) := by
  have hdiv : Tendsto (fun n : ℕ => 1/((n+1:ℕ):ℝ)) atTop (𝓝 (0:ℝ)) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto (fun n : ℕ => t+1/((n+1:ℕ):ℝ)) atTop (𝓝 (t+0)) := tendsto_const_nhds.add hdiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hu)
  · intro n;exact le_point (by omega) t
  · intro n;exact point_le_add_mesh (by omega) ht

end SphericalAging.UpperUnitGrid
