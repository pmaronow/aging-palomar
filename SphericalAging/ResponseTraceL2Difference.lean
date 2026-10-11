module

public import SphericalAging.TwoTimeResponseTrace
public import SphericalAging.L2ProbabilityExpectation

public section

/-! A true normalized expected trace difference is controlled by its
actual L² column differences, with no dimension factor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ResponseTraceL2Difference
open HardSphereDynamics LocalSDE TwoTimeResponseTrace L2ProbabilityExpectation
set_option maxHeartbeats 1400000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem normalizedTrace_eq_expectation_trace (M : State N→L[ℝ] Lp (State N) 2 P) :
    normalizedTrace M=(∑i,⟪basisVector i,expectation (M (basisVector i))⟫_ℝ)/(N:ℝ) := by
  have hi (i : Fin N) : Integrable (fun omega => ⟪basisVector i,M (basisVector i) omega⟫_ℝ) P :=
    ((Lp.memLp (M (basisVector i))).continuousLinearMap_comp (innerSL ℝ (basisVector i))).integrable (by norm_num)
  rw [normalizedTrace,integral_div,integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simpa only [expectation_apply,innerSL_apply_apply] using
    (innerSL ℝ (basisVector i)).integral_comp_comm ((Lp.memLp (M (basisVector i))).integrable (by norm_num))

theorem normalizedTrace_sub (M L : State N→L[ℝ] Lp (State N) 2 P) :
    normalizedTrace (M-L)=normalizedTrace M-normalizedTrace L := by
  simp only [normalizedTrace_eq_expectation_trace,ContinuousLinearMap.sub_apply,map_sub,
    inner_sub_right,Finset.sum_sub_distrib,sub_div]

theorem normalizedTrace_difference_le (hN : 0<N)
    (M L : State N→L[ℝ] Lp (State N) 2 P) (C : ℝ) (hC : 0≤C)
    (hb : ∀i : Fin N,‖M (basisVector i)-L (basisVector i)‖^2≤C) :
    |normalizedTrace M-normalizedTrace L|≤Real.sqrt C := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  rw [←normalizedTrace_sub,normalizedTrace_eq_expectation_trace,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _≤∑i : Fin N,|⟪basisVector i,expectation ((M-L) (basisVector i))⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑_i : Fin N,Real.sqrt C := by
      apply Finset.sum_le_sum
      intro i _
      have hLp : ‖M (basisVector i)-L (basisVector i)‖≤Real.sqrt C :=
        (Real.le_sqrt (norm_nonneg _) hC).mpr (hb i)
      have he := norm_integral_le_L2 (M (basisVector i)-L (basisVector i))
      have hi := norm_inner_le_norm (𝕜:=ℝ) (basisVector i) (expectation ((M-L) (basisVector i)))
      simp only [basisVector,EuclideanSpace.norm_single,norm_one,one_mul,Real.norm_eq_abs] at hi
      refine hi.trans ?_
      change ‖expectation (M (basisVector i)-L (basisVector i))‖≤Real.sqrt C
      exact he.trans hLp
    _=Real.sqrt C*(N:ℝ) := by simp [mul_comm]

end SphericalAging.ResponseTraceL2Difference
