module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

/-! Actual piecewise constant mass density for a finite nondecreasing mesh.
Repeated nodes are allowed: their zero-length cells carry no integral mass.
The square-root integral is exactly the discrete branching functional. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SphericalAging.MeshMassInterpolation
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

@[expose] def density (D : ℕ) (q A : ℕ→ℝ) (x : ℝ) : ℝ :=
  ∑i∈Finset.range D,if x∈Ioc (q i) (q (i+1)) then (A (i+1)-A i)/(q (i+1)-q i) else 0

theorem density_eq_cell (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q)
    {i : ℕ} (hi : i<D) {x : ℝ} (hx : x∈Ioc (q i) (q (i+1))) :
    density D q A x=(A (i+1)-A i)/(q (i+1)-q i) := by
  classical
  unfold density
  rw [Finset.sum_eq_single i]
  · simp only [ite_eq_left hx]
  · intro j hj hji
    have hnot : x∉Ioc (q j) (q (j+1)) := by
      intro h
      by_cases hij : j < i
      · have hh := hq (show j+1 ≤ i by omega)
        linarith [hx.1,h.2]
      · have hh := hq (show i+1 ≤ j by omega)
        linarith [hx.2,h.1]
    simp only [ite_eq_right hnot]
  · intro h
    exact (h (Finset.mem_range.mpr hi)).elim

theorem density_nonneg (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q)
    (hA : ∀i<D,0≤A (i+1)-A i) (x : ℝ) : 0≤density D q A x := by
  apply Finset.sum_nonneg
  intro i hi
  exact ite_nonneg (div_nonneg (hA i (Finset.mem_range.mp hi))
    (sub_nonneg.mpr (hq (Nat.le_succ i)))) le_rfl

theorem density_cell_integrable (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q)
    {i : ℕ} (hi : i<D) : IntervalIntegrable (density D q A) volume (q i) (q (i+1)) := by
  apply (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => (A (i+1)-A i)/(q (i+1)-q i)) volume (q i) (q (i+1))).congr
  intro x hx
  rw [uIoc_of_le (hq (Nat.le_succ i))] at hx
  exact (density_eq_cell D q A hq hi hx).symm

theorem sqrt_density_cell_integrable (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q)
    {i : ℕ} (hi : i<D) :
    IntervalIntegrable (fun x => Real.sqrt (density D q A x)) volume (q i) (q (i+1)) := by
  apply (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => Real.sqrt ((A (i+1)-A i)/(q (i+1)-q i))) volume (q i) (q (i+1))).congr
  intro x hx
  rw [uIoc_of_le (hq (Nat.le_succ i))] at hx
  exact congrArg Real.sqrt (density_eq_cell D q A hq hi hx).symm

theorem density_integrable (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q) :
    IntervalIntegrable (density D q A) volume (q 0) (q D) :=
  IntervalIntegrable.trans_iterate (fun i hi => density_cell_integrable D q A hq hi)

theorem sqrt_density_integrable (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q) :
    IntervalIntegrable (fun x => Real.sqrt (density D q A x)) volume (q 0) (q D) :=
  IntervalIntegrable.trans_iterate (fun i hi => sqrt_density_cell_integrable D q A hq hi)

theorem density_cell_integral (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q)
    {i : ℕ} (hi : i<D) :
    (∫x in q i..q (i+1),density D q A x)=
      (q (i+1)-q i)*((A (i+1)-A i)/(q (i+1)-q i)) := by
  have he : (∫x in q i..q (i+1),density D q A x)=
      ∫x in q i..q (i+1),(A (i+1)-A i)/(q (i+1)-q i) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [uIoc_of_le (hq (Nat.le_succ i))] at hx
    exact density_eq_cell D q A hq hi hx
  rw [he,intervalIntegral.integral_const,smul_eq_mul]

theorem scalar_sqrt_mass {a h : ℝ} (ha : 0≤a) (hh : 0≤h) :
    h*Real.sqrt (a/h)=Real.sqrt (h*a) := by
  by_cases hz : h=0
  · simp [hz]
  · have hp : 0<h := lt_of_le_of_ne hh (Ne.symm hz)
    rw [Real.sqrt_div ha,Real.sqrt_mul hh]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hp)]
    rw [Real.sq_sqrt hh]
    ring

theorem sqrt_density_cell_integral (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q)
    (hA : ∀i<D,0≤A (i+1)-A i) {i : ℕ} (hi : i<D) :
    (∫x in q i..q (i+1),Real.sqrt (density D q A x))=
      Real.sqrt ((q (i+1)-q i)*(A (i+1)-A i)) := by
  have he : (∫x in q i..q (i+1),Real.sqrt (density D q A x))=
      ∫x in q i..q (i+1),Real.sqrt ((A (i+1)-A i)/(q (i+1)-q i)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [uIoc_of_le (hq (Nat.le_succ i))] at hx
    rw [density_eq_cell D q A hq hi hx]
  rw [he,intervalIntegral.integral_const,smul_eq_mul]
  exact scalar_sqrt_mass (hA i hi) (sub_nonneg.mpr (hq (Nat.le_succ i)))

theorem integral_sqrt_eq_sum (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q)
    (hA : ∀i<D,0≤A (i+1)-A i) :
    (∫x in q 0..q D,Real.sqrt (density D q A x))=
      ∑i∈Finset.range D,Real.sqrt ((q (i+1)-q i)*(A (i+1)-A i)) := by
  rw [←intervalIntegral.sum_integral_adjacent_intervals (a:=q) (n:=D)
    (f:=fun x => Real.sqrt (density D q A x))
    (fun i hi => sqrt_density_cell_integrable D q A hq hi)]
  apply Finset.sum_congr rfl
  intro i hi
  exact sqrt_density_cell_integral D q A hq hA (Finset.mem_range.mp hi)

theorem mass_at_node_le (D : ℕ) (q A : ℕ→ℝ) (hq : Monotone q) (hzero : A 0=0)
    (hA : ∀i<D,0≤A (i+1)-A i) {j : ℕ} (hj : j≤D) :
    (∫x in q 0..q j,density D q A x)≤A j := by
  rw [←intervalIntegral.sum_integral_adjacent_intervals (a:=q) (n:=j) (f:=density D q A)
    (fun i hi => density_cell_integrable D q A hq (hi.trans_le hj))]
  calc
    _ ≤ (∑ i∈Finset.range j,(A (i+1)-A i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiD := (Finset.mem_range.mp hi).trans_le hj
      rw [density_cell_integral D q A hq hiD]
      by_cases hz : q (i+1)-q i=0
      · simpa only [hz,div_zero,mul_zero] using hA i hiD
      · rw [mul_div_cancel₀ _ hz]
    _=A j := by rw [Finset.sum_range_sub A j,hzero,sub_zero]

theorem exists_cell (D : ℕ) (q : ℕ→ℝ) {x : ℝ} (hx : x∈Ioc (q 0) (q D)) :
    ∃i<D,x∈Ioc (q i) (q (i+1)) := by
  induction D with
  | zero => exact (not_lt_of_ge hx.2 hx.1).elim
  | succ D ih =>
    by_cases hh : x≤q D
    · obtain ⟨i,hi,hxi⟩ := ih ⟨hx.1,hh⟩
      exact ⟨i,by omega,hxi⟩
    · exact ⟨D,Nat.lt_succ_self D,lt_of_not_ge hh,hx.2⟩

end SphericalAging.MeshMassInterpolation
