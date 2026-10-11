module

public import SphericalAging.SphereEulerBlockEnergy
public import SphericalAging.SphereEulerStepFields

public section

/-! Uniform genuine Euler local interpolation error. Its moment bound is
derived from the actual elementary Brownian block at the current interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped BigOperators NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereEulerLocalMoment
open HardSphereDynamics SphereEulerPredictable SphereEulerInterpolationAlgebra
open SphereEulerStepFields SphereEulerLocalAlgebra SphereEulerBlockEnergy
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def leftState (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (x : State N) (M : ℕ) (t : ℝ≥0) (omega : Ω) : State N :=
  if t=0 then x else leftStep h M (node D β h J x) t omega

variable (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p) (x : State N) (M : ℕ)

theorem leftState_joint_measurable : Measurable (fun q : ℝ≥0×Ω => leftState D β h J x M q.1 q.2) := by
  exact measurable_const.ite ((measurableSet_singleton (0:ℝ≥0)).preimage measurable_fst)
    (leftStep_measurable h M _ (fun k => node_measurable D β h J x k))
theorem leftState_measurable (t : ℝ≥0) : Measurable (leftState D β h J x M t) :=
  (leftState_joint_measurable D β h J x M).comp (measurable_const.prodMk measurable_id)

theorem leftState_zero (omega : Ω) : leftState D β h J x M 0 omega=x := by simp [leftState]

theorem leftState_eq_node {k : ℕ} (hk : k<M) {t : ℝ≥0}
    (ht : t∈Ioc (grid h k) (grid h (k+1))) (omega : Ω) :
    leftState D β h J x M t omega=node D β h J x k omega := by
  have ht0 : 0<t := lt_of_le_of_lt (show (0:ℝ≥0)≤grid h k from bot_le) ht.1
  rw [leftState,if_neg ht0.ne',leftStep_eq _ hk ht]

theorem interpolant_zero (omega : Ω) : interpolant D β h J x M 0 omega=x := by
  unfold interpolant
  have hh : (∑k ∈ Finset.range M,block D β h J x k 0 omega)=0 :=
    Finset.sum_eq_zero (fun k _ => block_eq_zero D β h J x bot_le omega)
  rw [hh,add_zero]

@[expose] def localCeiling : ℝ≥0 :=
  ⟨(2*(grid h M:ℝ)*(driftCap β J:ℝ)^2+4*(N:ℝ))*(h:ℝ),by positivity⟩

theorem local_defect_memLp (hN : 0<N) (t : ℝ≥0) (ht : t≤grid h M) :
    MemLp (fun omega => interpolant D β h J x M t omega-leftState D β h J x M t omega) 2 P := by
  by_cases ht0 : t=0
  · subst t
    simpa only [interpolant_zero,leftState_zero,sub_self] using (memLp_const (0:State N) : MemLp (fun _ : Ω => (0:State N)) 2 P)
  · obtain ⟨k,hk,hkt,htk⟩ := exists_interval h M (lt_of_le_of_ne bot_le (Ne.symm ht0)) ht
    have hb := grid_mono h (Nat.succ_le_of_lt hk)
    have he := blockClass_ae hN D β h J x k (grid h M) hb t
    apply (Lp.memLp (blockClass hN D β h J x k (grid h M) t)).ae_eq
    filter_upwards [he] with omega he
    rw [he,leftState_eq_node D β h J x M hk ⟨hkt,htk⟩,
      interpolant_sub_node D β h J x hk ⟨hkt,htk⟩]

theorem local_defect_secondMoment (hN : 0<N) (t : ℝ≥0) (ht : t≤grid h M) :
    (∫ omega,‖interpolant D β h J x M t omega-leftState D β h J x M t omega‖^2 ∂P)≤
      (localCeiling β h J M:ℝ) := by
  by_cases ht0 : t=0
  · subst t
    simp only [interpolant_zero,leftState_zero,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero]
    exact (localCeiling β h J M).coe_nonneg
  · obtain ⟨k,hk,hkt,htk⟩ := exists_interval h M (lt_of_le_of_ne bot_le (Ne.symm ht0)) ht
    have hb := grid_mono h (Nat.succ_le_of_lt hk)
    have he := blockClass_ae hN D β h J x k (grid h M) hb t
    calc
      _=∫ omega,‖blockClass hN D β h J x k (grid h M) t omega‖^2 ∂P := by
        apply integral_congr_ae
        filter_upwards [he] with omega he
        rw [he,leftState_eq_node D β h J x M hk ⟨hkt,htk⟩,
          interpolant_sub_node D β h J x hk ⟨hkt,htk⟩]
      _=‖blockClass hN D β h J x k (grid h M) t‖^2 := PredictableFamilyLift.integral_norm_sq_Lp _
      _≤_ := blockClass_norm_sq_le hN D β h J x k (grid h M) hb ht ⟨hkt,htk⟩
end SphericalAging.SphereEulerLocalMoment
