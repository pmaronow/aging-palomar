module

public import SphericalAging.HessianCovarianceContraction

public section

/-! Exact finite-N Hessian covariance contraction against an arbitrary
Brownian direction, together with its sharp norm correction bound. The
Brownian vector is not required to lie on the sphere. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.BrownianHessianCovarianceContraction
open HardSphereDynamics FiniteModel GaussianIntegrationByParts FiniteCorrelationIto HessianCovarianceContraction
  EnergyCovarianceContraction HamiltonianDerivativeCovariance
set_option maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def brownianPairing (x b : State N) : ℝ := inner ℝ x b/(Real.sqrt 2*(N : ℝ))

 theorem normalized_brownian_hessian_contraction (hN : 0<N) (hp : 3≤p)
    (x y b : State N) (U : State N →L[ℝ] State N) :
    (∑ I : TensorIndex N p,inner ℝ
      (fderiv ℝ (gradient (hamiltonianCoefficient I)) x
        (U (gradient (hamiltonianCoefficient I) y))) b)/(Real.sqrt 2*(N : ℝ))=
      (p : ℝ)*((p-1 : ℕ) : ℝ)*(overlap x y)^(p-2)*brownianPairing y b*normalizedTrace U+
        hessianCorrection (p := p) x y b U/Real.sqrt 2 := by
  have hh := normalized_correlation_hessian_contraction hN hp x y b U
  have he : overlap b y/Real.sqrt 2=brownianPairing y b := by
    unfold overlap brownianPairing
    rw [real_inner_comm b y]
    ring
  calc
    _=((∑ I : TensorIndex N p,inner ℝ
      (fderiv ℝ (gradient (hamiltonianCoefficient I)) x
        (U (gradient (hamiltonianCoefficient I) y))) b)/(N : ℝ))/Real.sqrt 2 := by ring
    _=((p : ℝ)*((p-1 : ℕ) : ℝ)*(overlap x y)^(p-2)*(overlap b y)*normalizedTrace U+
      hessianCorrection (p := p) x y b U)/Real.sqrt 2 := congrArg (fun z => z/Real.sqrt 2) hh
    _=(p : ℝ)*((p-1 : ℕ) : ℝ)*(overlap x y)^(p-2)*(overlap b y/Real.sqrt 2)*normalizedTrace U+
      hessianCorrection (p := p) x y b U/Real.sqrt 2 := by ring
    _=_ := by rw [he]

lemma overlap_brownian_sphere_abs_le (hN : 0<N) (y b : State N) (hy : OnSphere y) :
    |overlap b y|≤‖b‖/Real.sqrt N := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  rw [overlap,abs_div,abs_of_pos hn]
  calc
    _≤(‖b‖*Real.sqrt N)/(N : ℝ) :=
      div_le_div_of_nonneg_right (by simpa only [sphere_norm hy] using abs_real_inner_le_norm b y) hn.le
    _=‖b‖/Real.sqrt N := by field_simp;rw [Real.sq_sqrt hn.le]

 theorem brownian_hessianCorrection_abs_le (hN : 0<N) (hp : 3≤p)
    {x y : State N} (hx : OnSphere x) (hy : OnSphere y)
    (b : State N) (U : State N →L[ℝ] State N) :
    |hessianCorrection (p := p) x y b U|≤
      (p : ℝ)*((p : ℝ)-1)^2/(N : ℝ)*‖U‖*(‖b‖/Real.sqrt N) := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hpm : 0≤(p : ℝ)-1 := by
    have hh : (1 : ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
    linarith
  have hK : 0≤(p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2 := by positivity
  have hpow (n : ℕ) : |overlap x y|^n≤1 :=
    pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one hN hx hy)
  have hby := overlap_brownian_sphere_abs_le hN y b hy
  have hbU : |inner ℝ y (U b)|≤(N : ℝ)*‖U‖*(‖b‖/Real.sqrt N) := by
    calc
      _≤‖y‖*‖U b‖ := abs_real_inner_le_norm _ _
      _≤Real.sqrt N*(‖U‖*‖b‖) := by rw [sphere_norm hy];gcongr;exact U.le_opNorm b
      _=_ := by field_simp;rw [Real.sq_sqrt hn.le];ring
  have hfirst : |((p-2 : ℕ) : ℝ)*(overlap x y)^(p-3)*(overlap b y)*inner ℝ y (U x)|≤
      ((p-2 : ℕ) : ℝ)*((N : ℝ)*‖U‖*(‖b‖/Real.sqrt N)) := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow]
    calc
      _≤((p-2 : ℕ) : ℝ)*1*(‖b‖/Real.sqrt N)*((N : ℝ)*‖U‖) := by
        gcongr
        · exact hpow _
        · exact sphere_response_pairing_abs_le hx hy U
      _=_ := by ring
  have hsecond : |(overlap x y)^(p-2)*inner ℝ y (U b)|≤(N : ℝ)*‖U‖*(‖b‖/Real.sqrt N) := by
    rw [abs_mul,abs_pow]
    exact (mul_le_mul (hpow _) hbU (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnat : ((p-2 : ℕ) : ℝ)=(p : ℝ)-2 := by rw [Nat.cast_sub (by omega : 2≤p)];norm_num
  rw [hessianCorrection,abs_mul,abs_of_nonneg hK]
  calc
    _≤((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*
      (|((p-2 : ℕ) : ℝ)*(overlap x y)^(p-3)*(overlap b y)*inner ℝ y (U x)|+
        |(overlap x y)^(p-2)*inner ℝ y (U b)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hK
    _≤((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*
      (((p-2 : ℕ) : ℝ)*((N : ℝ)*‖U‖*(‖b‖/Real.sqrt N))+
        (N : ℝ)*‖U‖*(‖b‖/Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hK
    _=_ := by rw [hnat];field_simp;ring

end SphericalAging.BrownianHessianCovarianceContraction
