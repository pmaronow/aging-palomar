module

public import SphericalAging.MixedHamiltonianObservableDerivative

public section

/-! Actual coefficient gradient and Hessian-response L² classes on
physical sphere support, with genuine deterministic operator bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.HamiltonianCoefficientL2Classes
open HardSphereDynamics FiniteModel GaussianIntegrationByParts HamiltonianCoefficientBounds
  MixedHamiltonianObservableDerivative
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma coefficient_hessian_sphere_bound (I : TensorIndex N p) :
    ∃ C : ℝ≥0,∀ x : State N,OnSphere x → ‖fderiv ℝ (gradient (hamiltonianCoefficient I)) x‖≤C := by
  have hc := (coefficientGradient_contDiff I).continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : State N) (Real.sqrt N)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⟨max C 0,le_max_right _ _⟩,fun x hx => (hC x ?_).trans (le_max_left _ _)⟩
  simpa only [Metric.mem_closedBall,dist_zero_right,FiniteCorrelationIto.sphere_norm hx] using
    (le_rfl : Real.sqrt (N : ℝ)≤Real.sqrt N)

@[expose] noncomputable def hessianCeiling (I : TensorIndex N p) : ℝ≥0 :=
  (coefficient_hessian_sphere_bound I).choose

lemma hessianCeiling_bound (I : TensorIndex N p) (x : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (gradient (hamiltonianCoefficient I)) x‖≤hessianCeiling I :=
  (coefficient_hessian_sphere_bound I).choose_spec x hx

@[expose] def hessianField (I : TensorIndex N p) (X V : Lp (State N) 2 P) (ω : Ω) : State N :=
  fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω) (V ω)

lemma hessianField_stronglyMeasurable (I : TensorIndex N p) (X V : Lp (State N) 2 P) :
    StronglyMeasurable (hessianField I X V) := by
  have hA := ((coefficientGradient_contDiff I).continuous_fderiv (by simp)).comp_stronglyMeasurable
    (Lp.stronglyMeasurable X)
  exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hA.prodMk (Lp.stronglyMeasurable V))

lemma hessianField_memLp (I : TensorIndex N p) (X V : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) : MemLp (hessianField I X V) 2 P := by
  apply (Lp.memLp V).of_le_mul (c := hessianCeiling I) (hessianField_stronglyMeasurable I X V).aestronglyMeasurable
  filter_upwards [hX] with ω hx
  exact ((fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω)).le_opNorm (V ω)).trans
    (mul_le_mul_of_nonneg_right (hessianCeiling_bound I (X ω) hx) (norm_nonneg _))

@[expose] def hessianClass (I : TensorIndex N p) (X V : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) : Lp (State N) 2 P :=
  (hessianField_memLp I X V hX).toLp (hessianField I X V)

lemma hessianClass_ae (I : TensorIndex N p) (X V : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) :
    (hessianClass I X V hX : Ω → State N)=ᵐ[P] hessianField I X V :=
  (hessianField_memLp I X V hX).coeFn_toLp

lemma hessianClass_norm_le (I : TensorIndex N p) (X V : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) : ‖hessianClass I X V hX‖≤(hessianCeiling I : ℝ)*‖V‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hessianClass_ae I X V hX,hX] with ω hω hx
  rw [hω]
  exact ((fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω)).le_opNorm (V ω)).trans
    (mul_le_mul_of_nonneg_right (hessianCeiling_bound I (X ω) hx) (norm_nonneg _))

lemma gradientField_memLp (hN : 0<N) (I : TensorIndex N p) (X : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) :
    MemLp (fun ω => gradient (hamiltonianCoefficient I) (X ω)) 2 P := by
  apply MemLp.of_bound ((coefficientGradient_contDiff I).continuous.comp_stronglyMeasurable
    (Lp.stronglyMeasurable X)).aestronglyMeasurable p
  filter_upwards [hX] with ω hx
  exact coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hx)

@[expose] def coefficientGradientClass (hN : 0<N) (I : TensorIndex N p) (X : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) : Lp (State N) 2 P :=
  (gradientField_memLp hN I X hX).toLp (fun ω => gradient (hamiltonianCoefficient I) (X ω))

lemma coefficientGradientClass_ae (hN : 0<N) (I : TensorIndex N p) (X : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) :
    (coefficientGradientClass hN I X hX : Ω → State N)=ᵐ[P]
      (fun ω => gradient (hamiltonianCoefficient I) (X ω)) :=
  (gradientField_memLp hN I X hX).coeFn_toLp

lemma coefficientGradientClass_norm_le (hN : 0<N)
    (I : TensorIndex N p) (X : Lp (State N) 2 P) (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) :
    ‖coefficientGradientClass hN I X hX‖≤p := by
  have hb := Lp.norm_le_of_ae_bound (f := coefficientGradientClass hN I X hX) (Nat.cast_nonneg p) (by
    filter_upwards [coefficientGradientClass_ae hN I X hX,hX] with ω hω hx
    rw [hω]
    exact coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hx))
  simpa only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,Real.one_rpow,mul_one,one_mul] using hb

lemma coefficientGradientClass_pairing (hN : 0<N) (I : TensorIndex N p)
    (X Y : Lp (State N) 2 P) (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) :
    inner ℝ (coefficientGradientClass hN I X hX) Y=
      ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (Y ω) ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientGradientClass_ae hN I X hX] with ω hω
  rw [hω]

lemma hessianClass_pairing (I : TensorIndex N p) (X V Y : Lp (State N) 2 P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) :
    inner ℝ (hessianClass I X V hX) Y=
      ∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω) (V ω)) (Y ω) ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hessianClass_ae I X V hX] with ω hω
  rw [hω]
  rfl

end SphericalAging.HamiltonianCoefficientL2Classes
