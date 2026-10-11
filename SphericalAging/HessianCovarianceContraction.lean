module

public import SphericalAging.EnergyCovarianceContraction
public import SphericalAging.MixedHamiltonianObservableDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public section

/-! Actual mixed Hessian/gradient ordered tensor contractions are
spatial derivatives of the proved coefficient covariance, with their
explicit dimension-vanishing correction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators InnerProductSpace
namespace SphericalAging.HessianCovarianceContraction
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
  HamiltonianDerivativeCovariance EnergyCovarianceContraction MixedHamiltonianObservableDerivative
  FiniteCorrelationIto
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma overlap_hasFDerivAt_left {N : ℕ} (x y : State N) :
    HasFDerivAt (fun z : State N => overlap z y) ((1/(N : ℝ)) • innerSL ℝ y) x := by
  have hi : HasFDerivAt (fun z : State N => inner ℝ z y) (innerSL ℝ y) x := by
    convert (innerSL ℝ y).hasFDerivAt (x := x) using 1
    funext z
    exact real_inner_comm _ _
  convert hi.const_mul (1/(N : ℝ)) using 1
  funext z
  simp only [overlap]
  ring

lemma gradient_contraction_hasFDerivAt {N p : ℕ} (x y : State N)
    (U : State N →L[ℝ] State N) :
    HasFDerivAt (fun z : State N => ∑ I : TensorIndex N p,
      inner ℝ (gradient (hamiltonianCoefficient I) z) (U (gradient (hamiltonianCoefficient I) y)))
      (∑ I : TensorIndex N p,(innerSL ℝ (U (gradient (hamiltonianCoefficient I) y))).comp
        (fderiv ℝ (gradient (hamiltonianCoefficient I)) x)) x := by
  apply HasFDerivAt.fun_sum
  intro I _
  have hd := (coefficientGradient_contDiff I).differentiable (by simp)
  have h := (innerSL ℝ (U (gradient (hamiltonianCoefficient I) y))).hasFDerivAt.comp x
    hd.differentiableAt.hasFDerivAt
  convert h using 1
  funext z
  exact real_inner_comm _ _

/-- Exact derivative of the genuine coefficient-gradient covariance. -/
theorem hessian_gradient_contraction {N p : ℕ} (hN : 0 < N) (hp : 3 ≤ p)
    (x y z : State N) (U : State N →L[ℝ] State N) :
    (∑ I : TensorIndex N p,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) x z)
      (U (gradient (hamiltonianCoefficient I) y)))=
      (p : ℝ)*((p-1 : ℕ) : ℝ)*(overlap x y)^(p-2)*(overlap z y)*operatorTrace U+
      ((p : ℝ)*((p : ℝ)-1)/N)*
        (((p-2 : ℕ) : ℝ)*(overlap x y)^(p-3)*(overlap z y)*inner ℝ y (U x)+
          (overlap x y)^(p-2)*inner ℝ y (U z)) := by
  have hc := overlap_hasFDerivAt_left x y
  have hi : HasFDerivAt (fun w : State N => inner ℝ y (U w)) ((innerSL ℝ y).comp U) x :=
    (innerSL ℝ y).hasFDerivAt.comp x U.hasFDerivAt
  have h₁ := ((hc.pow (p-1)).const_mul (p : ℝ)).mul_const (operatorTrace U)
  have h₂ := (((hc.pow (p-2)).mul hi).const_mul ((p : ℝ)*((p : ℝ)-1)/N))
  have he : (fun w : State N => ∑ I : TensorIndex N p,
      inner ℝ (gradient (hamiltonianCoefficient I) w) (U (gradient (hamiltonianCoefficient I) y)))=
      (fun w : State N => (p : ℝ)*(overlap w y)^(p-1)*operatorTrace U+
        ((p : ℝ)*((p : ℝ)-1)/N)*(overlap w y)^(p-2)*inner ℝ y (U w)) := by
    funext w
    exact coefficient_gradient_contraction (p := p) hN (by omega) w y U
  have hl := gradient_contraction_hasFDerivAt (p := p) x y U
  rw [he] at hl
  have hright := h₁.add h₂
  simp only [Pi.add_apply,Pi.mul_apply,← mul_assoc] at hright
  have hder := congrArg (fun L : State N →L[ℝ] ℝ => L z) (hl.unique hright)
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul] at hder
  simp only [show p-1-1=p-2 by omega,show p-2-1=p-3 by omega] at hder
  have hov : (1/(N : ℝ))*inner ℝ y z=overlap z y := by
    rw [overlap,real_inner_comm y z]
    ring
  rw [hov] at hder
  simp only [nsmul_eq_mul] at hder
  calc
    _ = ∑ I : TensorIndex N p,inner ℝ (U (gradient (hamiltonianCoefficient I) y))
        (fderiv ℝ (gradient (hamiltonianCoefficient I)) x z) :=
      Finset.sum_congr rfl (fun I _ => real_inner_comm _ _)
    _ = _ := hder.trans (by ring)

lemma coefficient_hessian_symmetric {N p : ℕ} (I : TensorIndex N p) (x a b : State N) :
    inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) x a) b=
      inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) x b) a := by
  have hi (v w : State N) : inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) x v) w=
      fderiv ℝ (fderiv ℝ (hamiltonianCoefficient I)) x v w := by
    change inner ℝ (fderiv ℝ ((InnerProductSpace.toDual ℝ (State N)).symm ∘
      fderiv ℝ (hamiltonianCoefficient I)) x v) w=_
    rw [LinearIsometryEquiv.comp_fderiv]
    change inner ℝ ((InnerProductSpace.toDual ℝ (State N)).symm
      (fderiv ℝ (fderiv ℝ (hamiltonianCoefficient I)) x v)) w=_
    rw [← InnerProductSpace.toDual_apply_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [hi,hi]
  exact ((coefficient_contDiff I).contDiffAt.isSymmSndFDerivAt (by simp)).eq a b

/-- The transpose order actually produced by mixed Gaussian Stein is
identified using the proved symmetry of each true coefficient Hessian. -/
theorem correlation_hessian_contraction {N p : ℕ} (hN : 0 < N) (hp : 3 ≤ p)
    (x y z : State N) (U : State N →L[ℝ] State N) :
    (∑ I : TensorIndex N p,inner ℝ
      (fderiv ℝ (gradient (hamiltonianCoefficient I)) x
        (U (gradient (hamiltonianCoefficient I) y))) z)=
      (p : ℝ)*((p-1 : ℕ) : ℝ)*(overlap x y)^(p-2)*(overlap z y)*operatorTrace U+
      ((p : ℝ)*((p : ℝ)-1)/N)*
        (((p-2 : ℕ) : ℝ)*(overlap x y)^(p-3)*(overlap z y)*inner ℝ y (U x)+
          (overlap x y)^(p-2)*inner ℝ y (U z)) := by
  simp_rw [coefficient_hessian_symmetric]
  exact hessian_gradient_contraction hN hp x y z U

/-- Explicit correction in the normalized correlation Hessian memory. -/
@[expose] def hessianCorrection {N p : ℕ} (x y z : State N) (U : State N →L[ℝ] State N) : ℝ :=
  ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*
    (((p-2 : ℕ) : ℝ)*(overlap x y)^(p-3)*(overlap z y)*inner ℝ y (U x)+
      (overlap x y)^(p-2)*inner ℝ y (U z))

/-- Exact normalized CK memory term plus the genuine finite-N error. -/
theorem normalized_correlation_hessian_contraction {N p : ℕ} (hN : 0 < N) (hp : 3 ≤ p)
    (x y z : State N) (U : State N →L[ℝ] State N) :
    (∑ I : TensorIndex N p,inner ℝ
      (fderiv ℝ (gradient (hamiltonianCoefficient I)) x
        (U (gradient (hamiltonianCoefficient I) y))) z)/(N : ℝ)=
      (p : ℝ)*((p-1 : ℕ) : ℝ)*(overlap x y)^(p-2)*(overlap z y)*normalizedTrace U+
        hessianCorrection (p := p) x y z U := by
  rw [correlation_hessian_contraction hN hp,normalizedTrace,hessianCorrection]
  ring

/-- The actual correction is O(‖U‖/N) on the three physical sphere states. -/
theorem hessianCorrection_abs_le {N p : ℕ} (hN : 0 < N) (hp : 3 ≤ p)
    {x y z : State N} (hx : OnSphere x) (hy : OnSphere y) (hz : OnSphere z)
    (U : State N →L[ℝ] State N) :
    |hessianCorrection (p := p) x y z U| ≤ (p : ℝ)*((p : ℝ)-1)^2/N*‖U‖ := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hpc : (2 : ℝ)≤p := by exact_mod_cast (show 2≤p by omega)
  have hpm : 0≤(p : ℝ)-1 := by linarith
  have hK : 0≤(p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2 := by positivity
  have hpow (n : ℕ) : |overlap x y|^n≤1 :=
    pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one hN hx hy)
  have hzy : |overlap z y|≤1 := overlap_abs_le_one hN hz hy
  have hfirst : |((p-2 : ℕ) : ℝ)*(overlap x y)^(p-3)*(overlap z y)*inner ℝ y (U x)|≤
      ((p-2 : ℕ) : ℝ)*((N : ℝ)*‖U‖) := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow]
    calc
      _ ≤ ((p-2 : ℕ) : ℝ)*1*1*((N : ℝ)*‖U‖) := by
        gcongr
        · exact hpow _
        · exact sphere_response_pairing_abs_le hx hy U
      _ = _ := by ring
  have hsecond : |(overlap x y)^(p-2)*inner ℝ y (U z)|≤(N : ℝ)*‖U‖ := by
    rw [abs_mul,abs_pow]
    calc
      _ ≤ 1*((N : ℝ)*‖U‖) := mul_le_mul (hpow _)
        (sphere_response_pairing_abs_le hz hy U) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hnat : ((p-2 : ℕ) : ℝ)=(p : ℝ)-2 := by rw [Nat.cast_sub (by omega : 2≤p)]; norm_num
  rw [hessianCorrection,abs_mul,abs_of_nonneg hK]
  calc
    _ ≤ ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*
        (|((p-2 : ℕ) : ℝ)*(overlap x y)^(p-3)*(overlap z y)*inner ℝ y (U x)|+
          |(overlap x y)^(p-2)*inner ℝ y (U z)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hK
    _ ≤ ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*
        (((p-2 : ℕ) : ℝ)*((N : ℝ)*‖U‖)+(N : ℝ)*‖U‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hK
    _ = _ := by rw [hnat]; field_simp; ring

end SphericalAging.HessianCovarianceContraction
