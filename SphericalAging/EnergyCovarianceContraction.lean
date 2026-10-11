module

public import SphericalAging.HamiltonianDerivativeCovariance
public import SphericalAging.FiniteCorrelationIto

public section

/-! Actual finite-N coefficient-gradient contractions in the energy
integration-by-parts identity, including the dimension-vanishing rank-one
correction. The covariance tensor is calculated from the real ordered
Hamiltonian; it is not a premise of any theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace
namespace SphericalAging.EnergyCovarianceContraction
open FiniteModel HardSphereDynamics GaussianIntegrationByParts
open HamiltonianDerivativeCovariance FiniteCorrelationIto
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Contraction of the actual coefficient-gradient covariance with a real
finite-dimensional response operator. The transpose order is explicit. -/
theorem coefficient_gradient_contraction_trace {N p : ℕ} (x y : Vector N)
    (U : Vector N →L[ℝ] Vector N) :
    (∑ I : TensorIndex N p, inner ℝ (gradient (hamiltonianCoefficient I) x)
      (U (gradient (hamiltonianCoefficient I) y))) =
      operatorTrace (U.comp (gradientCrossOperator (p := p) y x)) := by
  have he : U.comp (gradientCrossOperator (p := p) y x)=
      ∑ I : TensorIndex N p, (innerSL ℝ (gradient (hamiltonianCoefficient I) x)).smulRight
        (U (gradient (hamiltonianCoefficient I) y)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [gradientCrossOperator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply,map_sum,map_smul]
  rw [he,operatorTrace,ContinuousLinearMap.toLinearMap_sum,map_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [show ((innerSL ℝ (gradient (hamiltonianCoefficient I) x)).smulRight
      (U (gradient (hamiltonianCoefficient I) y))).toLinearMap=
      (innerSL ℝ (gradient (hamiltonianCoefficient I) x)).toLinearMap.smulRight
      (U (gradient (hamiltonianCoefficient I) y)) from rfl,LinearMap.trace_smulRight]
  rfl

/-- Exact trace plus rank-one split in Chapter 4, evaluated on the genuine
ordered-tensor coefficients. -/
theorem coefficient_gradient_contraction {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y : Vector N) (U : Vector N →L[ℝ] Vector N) :
    (∑ I : TensorIndex N p, inner ℝ (gradient (hamiltonianCoefficient I) x)
      (U (gradient (hamiltonianCoefficient I) y))) =
      (p : ℝ)*(overlap x y)^(p-1)*operatorTrace U+
        (((p : ℝ)*((p : ℝ)-1)/N)*(overlap x y)^(p-2))*inner ℝ y (U x) := by
  rw [coefficient_gradient_contraction_trace,gradientCrossOperator_trace hN hp]
  simp only [overlap,real_inner_comm y x]

/-- A normalized genuine finite-dimensional trace. -/
@[expose] def normalizedTrace {N : ℕ} (U : Vector N →L[ℝ] Vector N) : ℝ := operatorTrace U/N

lemma operatorTrace_abs_le {N : ℕ} (U : Vector N →L[ℝ] Vector N) :
    |operatorTrace U| ≤ (N : ℝ)*‖U‖ := by
  rw [operatorTrace,LinearMap.trace_eq_sum_inner U.toLinearMap (EuclideanSpace.basisFun (Fin N) ℝ)]
  calc
    _ ≤ ∑ i : Fin N, |inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i)
      (U (EuclideanSpace.basisFun (Fin N) ℝ i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ‖U‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : ‖EuclideanSpace.basisFun (Fin N) ℝ i‖=1 :=
        (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one i
      calc
        _ ≤ ‖EuclideanSpace.basisFun (Fin N) ℝ i‖*‖U (EuclideanSpace.basisFun (Fin N) ℝ i)‖ :=
          norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ ‖EuclideanSpace.basisFun (Fin N) ℝ i‖*(‖U‖*‖EuclideanSpace.basisFun (Fin N) ℝ i‖) := by
          exact mul_le_mul_of_nonneg_left (U.le_opNorm _) (norm_nonneg _)
        _ = _ := by rw [hn]; ring
    _ = _ := by simp

lemma normalizedTrace_abs_le {N : ℕ} (hN : 0 < N) (U : Vector N →L[ℝ] Vector N) :
    |normalizedTrace U| ≤ ‖U‖ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [normalizedTrace,abs_div,abs_of_pos hn,div_le_iff₀ hn]
  simpa only [mul_comm] using operatorTrace_abs_le U

lemma sphere_response_pairing_abs_le {N : ℕ} {x y : Vector N}
    (hx : OnSphere x) (hy : OnSphere y) (U : Vector N →L[ℝ] Vector N) :
    |inner ℝ y (U x)| ≤ (N : ℝ)*‖U‖ := by
  calc
    _ ≤ ‖y‖*‖U x‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ ≤ ‖y‖*(‖U‖*‖x‖) := mul_le_mul_of_nonneg_left (U.le_opNorm x) (norm_nonneg _)
    _ = _ := by
      rw [sphere_norm hx,sphere_norm hy]
      calc
        Real.sqrt N*(‖U‖*Real.sqrt N)=(Real.sqrt N)^2*‖U‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The exact normalized correction left after the trace response term. -/
@[expose] def energyCorrection {N p : ℕ} (x y : Vector N) (U : Vector N →L[ℝ] Vector N) : ℝ :=
  ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*(overlap x y)^(p-2)*inner ℝ y (U x)

lemma normalized_contraction_eq {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y : Vector N) (U : Vector N →L[ℝ] Vector N) :
    (∑ I : TensorIndex N p, inner ℝ (gradient (hamiltonianCoefficient I) x)
      (U (gradient (hamiltonianCoefficient I) y)))/N =
      (p : ℝ)*(overlap x y)^(p-1)*normalizedTrace U+energyCorrection (p := p) x y U := by
  rw [coefficient_gradient_contraction hN hp,normalizedTrace,energyCorrection]
  ring

/-- The rank-one correction is bounded by `p(p−1)‖U‖/N` on the actual
sphere, precisely the dimension-vanishing error in the manuscript. -/
theorem energyCorrection_abs_le {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    {x y : Vector N} (hx : OnSphere x) (hy : OnSphere y) (U : Vector N →L[ℝ] Vector N) :
    |energyCorrection (p := p) x y U| ≤ (p : ℝ)*((p : ℝ)-1)/N*‖U‖ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpc : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p from by omega)
  have hpm : 0 ≤ (p : ℝ)-1 := by linarith
  have hc : |overlap x y|^(p-2) ≤ 1 := pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one hN hx hy)
  have hK : 0 ≤ (p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2 := by positivity
  rw [energyCorrection,abs_mul,abs_mul,abs_of_nonneg hK,abs_pow]
  calc
    _ ≤ ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*1*((N : ℝ)*‖U‖) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc hK) (sphere_response_pairing_abs_le hx hy U)
        (abs_nonneg _) (mul_nonneg hK (by norm_num))
    _ = _ := by field_simp

/-- The genuine signed normalized trace is controlled by the actual
operator norm, even when the response trace changes sign. -/
theorem weighted_trace_replacement_le {N : ℕ} (hN : 0 < N) (n : ℕ)
    {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (U : Vector N →L[ℝ] Vector N) :
    |(a^n-b^n)*normalizedTrace U| ≤ (n : ℝ)*|a-b| *‖U‖ := by
  have hp : |a^n-b^n| ≤ (n : ℝ)*|a-b| := by
    calc
      _ ≤ |a-b| *(n : ℝ)*(max |a| |b|)^(n-1) := abs_pow_sub_pow_le a b n
      _ ≤ |a-b| *(n : ℝ)*1^(n-1) := by gcongr; exact max_le ha hb
      _ = _ := by simp; ring
  rw [abs_mul]
  exact (mul_le_mul hp (normalizedTrace_abs_le hN U) (abs_nonneg _) (by positivity)).trans_eq (by ring)

end SphericalAging.EnergyCovarianceContraction
