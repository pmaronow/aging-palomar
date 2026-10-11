module

public import SphericalAging.AlgorithmicNoiseCalibration

public section

/-! A finite mesh of actual overlap values with uniform deterministic
spacing, including flat correlation functions and nonzero endpoints. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.ClampedUniformOverlapMesh
open Set

@[expose] def clamp (lo hi x : ℝ) : ℝ := max lo (min hi x)

@[expose] def mesh (lo hi : ℝ) (D l : ℕ) : ℝ := clamp lo hi ((l:ℝ)/(D:ℝ))

theorem clamp_mem (lo hi x : ℝ) (h : lo≤hi) : clamp lo hi x∈Icc lo hi :=
  ⟨le_max_left _ _,max_le h (min_le_left _ _)⟩

theorem clamp_monotone (lo hi : ℝ) : Monotone (clamp lo hi) :=
  fun _ _ h => max_le_max_left _ (min_le_min_left _ h)

theorem clamp_lipschitz (lo hi : ℝ) : LipschitzWith 1 (clamp lo hi) :=
  (LipschitzWith.id.const_min hi).const_max lo

theorem mesh_mem (lo hi : ℝ) (h : lo≤hi) (D l : ℕ) : mesh lo hi D l∈Icc lo hi :=
  clamp_mem lo hi _ h

theorem mesh_monotone (lo hi : ℝ) (D : ℕ) : Monotone (mesh lo hi D) := by
  intro i j hij
  exact clamp_monotone lo hi (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg D))

theorem mesh_zero (lo hi : ℝ) (hlo : 0≤lo) (hlohi : lo≤hi) (D : ℕ) : mesh lo hi D 0=lo := by
  simp only [mesh,clamp,Nat.cast_zero,zero_div,min_eq_right (hlo.trans hlohi),max_eq_left hlo]

theorem mesh_terminal (lo hi : ℝ) (hlohi : lo≤hi) (hhi : hi≤1) (D : ℕ) (hD : 0<D) :
    mesh lo hi D D=hi := by
  have hn : (D:ℝ)≠0 := (Nat.cast_pos.mpr hD).ne'
  simp only [mesh,clamp,div_self hn,min_eq_left hhi,max_eq_right hlohi]

theorem mesh_gap (lo hi : ℝ) (D l : ℕ) (hD : 0<D) :
    mesh lo hi D (l+1)-mesh lo hi D l≤1/(D:ℝ) := by
  have hn : 0<(D:ℝ) := Nat.cast_pos.mpr hD
  have hm := (clamp_lipschitz lo hi).dist_le_mul (((l+1:ℕ):ℝ)/(D:ℝ)) ((l:ℝ)/(D:ℝ))
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hm
  have he : (((l+1:ℕ):ℝ)/(D:ℝ))-((l:ℝ)/(D:ℝ))=1/(D:ℝ) := by
    rw [Nat.cast_add,Nat.cast_one,add_div];ring
  rw [he] at hm
  rw [abs_of_nonneg (div_nonneg (by norm_num : (0:ℝ)≤1) hn.le)] at hm
  exact (le_abs_self _).trans hm

theorem actual_uniform_calibration (χ : ℝ→ℝ) (hχ : ContinuousOn χ (Icc 0 1))
    (hm : MonotoneOn χ (Icc 0 1)) (hr : ∀s∈Icc (0:ℝ) 1,χ s∈Icc (0:ℝ) 1)
    (D : ℕ) (hD : 0<D) :
    let q := mesh (χ 0) (χ 1) D
    let V := AlgorithmicNoiseCalibration.varianceSchedule χ hχ q D
    Monotone q ∧ q 0=χ 0 ∧ q D=χ 1 ∧ (∀l,q l∈Icc (χ 0) (χ 1)) ∧
    (∀l,q (l+1)-q l≤1/(D:ℝ)) ∧ V 0=1 ∧ V D=0 ∧
    (∀j,V j∈Icc 0 1) ∧ (∀j,V (j+1)≤V j) ∧ ∀l,l≤D→χ (V (D-l))=q l := by
  have hzero : (0:ℝ)∈Icc (0:ℝ) 1 := by norm_num
  have hone : (1:ℝ)∈Icc (0:ℝ) 1 := by norm_num
  have hlohi : χ 0≤χ 1 := hm hzero hone (by norm_num)
  let q := mesh (χ 0) (χ 1) D
  have hq := mesh_monotone (χ 0) (χ 1) D
  have hq0 := mesh_zero (χ 0) (χ 1) (hr 0 hzero).1 hlohi D
  have hqD := mesh_terminal (χ 0) (χ 1) hlohi (hr 1 hone).2 D hD
  have hmem := mesh_mem (χ 0) (χ 1) hlohi D
  have hc := AlgorithmicNoiseCalibration.actual_calibrated_variance_schedule χ hχ hm q hq hmem D hD hq0 hqD
  exact ⟨hq,hq0,hqD,hmem,fun l => mesh_gap _ _ D l hD,hc⟩

end SphericalAging.ClampedUniformOverlapMesh
