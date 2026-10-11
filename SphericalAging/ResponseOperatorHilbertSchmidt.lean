module

public import SphericalAging.ActualResponseTimeOperatorIntegrability

public section

/-! True finite-column Hilbert–Schmidt control of physical response
operator norms, with the dimension factor made explicit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ResponseOperatorHilbertSchmidt
open HardSphereDynamics FiniteModel ResponseMatrixEnergyContraction FiniteCorrelationIto
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma norm_sq_le_sum_basis_sq {N : ℕ} (U : State N →L[ℝ] State N) :
    ‖U‖^2≤∑ i : Fin N,‖U (basisVector i)‖^2 := by
  let S := ∑ i : Fin N,‖U (basisVector i)‖^2
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hs := Real.sq_sqrt hS
  have hv (v : State N) : ‖U v‖^2≤‖v‖^2*S := by
    have hn := norm_sum_le Finset.univ (fun i : Fin N => v i • U (basisVector i))
    have he : U v=∑ i : Fin N,v i • U (basisVector i) := by
      conv_lhs => rw [← LocalSDE.state_sum_basis v,map_sum]
      simp only [map_smul]
    rw [← he] at hn
    simp only [norm_smul,Real.norm_eq_abs] at hn
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin N => |v i|) (fun i : Fin N => ‖U (basisVector i)‖)
    simp only [sq_abs,coordinate_square_sum,real_inner_self_eq_norm_sq] at hc
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc
  have hop : ‖U‖≤Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound U (Real.sqrt_nonneg S)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg S) (norm_nonneg v))).mp
    rw [mul_pow,hs,mul_comm]
    exact hv v
  exact (pow_le_pow_left₀ (norm_nonneg _) hop 2).trans_eq hs

/-- Actual operator second moments follow from column fourth moments,
with the sharp dimension dependence needed for finite-rank errors. -/
theorem matrix_secondMoment_from_columns {N : ℕ} {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    (U : A → (State N →L[ℝ] State N)) (hU : AEStronglyMeasurable U μ)
    (B : ℝ) (hM : ∀ i : Fin N,MemLp (fun a => U a (basisVector i)) 4 μ)
    (hB : ∀ i : Fin N,(∫ a,‖U a (basisVector i)‖^4 ∂μ)≤B) :
    MemLp U 2 μ ∧ (∫ a,‖U a‖^2 ∂μ)≤(N : ℝ)*(1+B) := by
  have hcol (i : Fin N) : Integrable (fun a => ‖U a (basisVector i)‖^2) μ :=
    ((hM i).mono_exponent (by norm_num : (2 : ℝ≥0∞)≤4)).integrable_norm_pow'
  have hsum : Integrable (fun a => ∑ i : Fin N,‖U a (basisVector i)‖^2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hcol i)
  have hi : Integrable (fun a => ‖U a‖^2) μ := by
    apply hsum.mono' (hU.norm.pow 2)
    exact .of_forall (fun a => by
      change ‖‖U a‖^2‖≤_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact norm_sq_le_sum_basis_sq _)
  have hm : MemLp U 2 μ := by
    apply (integrable_norm_rpow_iff hU (by norm_num : (2 : ℝ≥0∞)≠0)
      (by norm_num : (2 : ℝ≥0∞)≠∞)).mp
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hi
  refine ⟨hm,(integral_mono_ae hi hsum (.of_forall (fun a => norm_sq_le_sum_basis_sq _))).trans ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hcol i)]
  calc
    _ ≤ ∑ _i : Fin N,(1+B) := by
      apply Finset.sum_le_sum
      intro i _
      have h₁ : (∫ a,‖U a (basisVector i)‖^2 ∂μ)≤1+(∫ a,‖U a (basisVector i)‖^4 ∂μ) := by
        have hp : ∀ a,‖U a (basisVector i)‖^2≤1+‖U a (basisVector i)‖^4 := by
          intro a
          nlinarith [sq_nonneg (‖U a (basisVector i)‖^2-1)]
        have hh := integral_mono_ae (hcol i) ((integrable_const 1).add (hM i).integrable_norm_pow') (.of_forall hp)
        change (∫ a,‖U a (basisVector i)‖^2 ∂μ)≤∫ a,1+‖U a (basisVector i)‖^4 ∂μ at hh
        rw [integral_add (integrable_const 1) (hM i).integrable_norm_pow'] at hh
        simpa only [integral_const,measure_univ,Measure.real_def,ENNReal.toReal_one,one_smul] using hh
      exact h₁.trans (add_le_add le_rfl (hB i))
    _ = _ := by simp;ring

end SphericalAging.ResponseOperatorHilbertSchmidt
