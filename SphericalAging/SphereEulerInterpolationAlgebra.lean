module

public import SphericalAging.SphereEulerPredictable

public section

/-! Literal continuous-prefix Euler interpolation and exact grid identities.
The input to every coefficient is the actual query recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped BigOperators NNReal InnerProductSpace
namespace SphericalAging.SphereEulerInterpolationAlgebra
open HardSphereDynamics SphereEulerCoefficients SphereEulerPredictable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem grid_succ (h : ℝ≥0) (k : ℕ) : grid h (k+1)=grid h k+h := by
  simp only [grid,Nat.cast_add,Nat.cast_one,mul_add,mul_one]
theorem grid_gap (h : ℝ≥0) (k : ℕ) : (grid h (k+1):ℝ)-(grid h k:ℝ)=h := by
  rw [grid_succ,NNReal.coe_add]
  ring

@[expose] def stoppedIncrement (D : BrownianDriver N P F) (h : ℝ≥0) (k : ℕ) (t : ℝ≥0)
    (omega : Ω) : State N :=
  ∑j : Fin N,(D.coordinate j (min t (grid h (k+1))) omega-
    D.coordinate j (min t (grid h k)) omega) • basisVector j

@[expose] def fullBlock (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (x : State N) (k : ℕ) (omega : Ω) : State N :=
  (h:ℝ) • SphereEulerCoefficients.drift β J (node D β h J x k omega)+
    Real.sqrt 2 • projection (clip (node D β h J x k omega)) (increment D h k omega)

@[expose] def block (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (x : State N) (k : ℕ) (t : ℝ≥0) (omega : Ω) : State N :=
  (((min t (grid h (k+1)) : ℝ≥0):ℝ)-((min t (grid h k):ℝ≥0):ℝ)) •
      SphereEulerCoefficients.drift β J (node D β h J x k omega)+
    Real.sqrt 2 • projection (clip (node D β h J x k omega)) (stoppedIncrement D h k t omega)

@[expose] def interpolant (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (x : State N) (M : ℕ) (t : ℝ≥0) (omega : Ω) : State N :=
  x+∑k ∈ Finset.range M,block D β h J x k t omega

variable (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p) (x : State N)

theorem block_eq_full {k : ℕ} {t : ℝ≥0} (ht : grid h (k+1)≤t) (omega : Ω) :
    block D β h J x k t omega=fullBlock D β h J x k omega := by
  have ha : grid h k≤t := (grid_mono h (Nat.le_succ k)).trans ht
  simp only [block,fullBlock,stoppedIncrement,min_eq_right ht,min_eq_right ha,grid_gap,increment]

theorem block_eq_zero {k : ℕ} {t : ℝ≥0} (ht : t≤grid h k) (omega : Ω) :
    block D β h J x k t omega=0 := by
  have hb : t≤grid h (k+1) := ht.trans (grid_mono h (Nat.le_succ k))
  simp only [block,stoppedIncrement,min_eq_left ht,min_eq_left hb,sub_self,zero_smul,
    Finset.sum_const_zero]
  simp [projection]

theorem node_succ (k : ℕ) (omega : Ω) :
    node D β h J x (k+1) omega=node D β h J x k omega+fullBlock D β h J x k omega := by
  change SphereEulerQuerySpan.step β h J _ _=_
  unfold SphereEulerQuerySpan.step fullBlock
  abel

theorem node_eq_sum (k : ℕ) (omega : Ω) :
    node D β h J x k omega=x+∑j ∈ Finset.range k,fullBlock D β h J x j omega := by
  induction k with
  | zero => simp [node,SphereEulerQuerySpan.state]
  | succ k ih => rw [node_succ,ih,Finset.sum_range_succ];abel

theorem interpolant_grid {k M : ℕ} (hk : k≤M) (omega : Ω) :
    interpolant D β h J x M (grid h k) omega=node D β h J x k omega := by
  rw [interpolant,node_eq_sum]
  congr 1
  have hs : (∑j ∈ Finset.range k,block D β h J x j (grid h k) omega)=
      ∑j ∈ Finset.range M,block D β h J x j (grid h k) omega := by
    apply Finset.sum_subset (Finset.range_mono hk)
    intro j _ hj
    exact block_eq_zero D β h J x (grid_mono h (Nat.le_of_not_gt (by simpa using hj))) omega
  rw [←hs]
  apply Finset.sum_congr rfl
  intro j hj
  exact block_eq_full D β h J x (grid_mono h (Nat.succ_le_of_lt (Finset.mem_range.mp hj))) omega

theorem exists_interval (M : ℕ) {t : ℝ≥0} (ht0 : 0<t) (htM : t≤grid h M) :
    ∃k,k<M ∧ grid h k<t ∧ t≤grid h (k+1) := by
  induction M with
  | zero =>
    have hz : t≤0 := by simpa only [grid,Nat.cast_zero,mul_zero] using htM
    exact False.elim (not_lt_of_ge hz ht0)
  | succ M ih =>
    by_cases ht : t≤grid h M
    · obtain ⟨k,hk,hkt,htk⟩ := ih ht
      exact ⟨k,Nat.lt_trans hk (Nat.lt_succ_self M),hkt,htk⟩
    · exact ⟨M,Nat.lt_succ_self M,lt_of_not_ge ht,htM⟩

theorem interval_disjoint {j k : ℕ} (hjk : j≠k) {t : ℝ≥0}
    (hk : t∈Ioc (grid h k) (grid h (k+1))) : t∉Ioc (grid h j) (grid h (j+1)) := by
  intro hj
  rcases lt_or_gt_of_ne hjk with hjk|hkj
  · exact (not_lt_of_ge (hj.2.trans (grid_mono h (Nat.succ_le_of_lt hjk)))) hk.1
  · exact (not_lt_of_ge (hk.2.trans (grid_mono h (Nat.succ_le_of_lt hkj)))) hj.1

end SphericalAging.SphereEulerInterpolationAlgebra
