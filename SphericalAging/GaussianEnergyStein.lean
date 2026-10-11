module

public import SphericalAging.HamiltonianObservableDerivative
public import SphericalAging.DisorderExponentialIntegrability
public import SphericalAging.AffineSDESecondLocalization
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Deriv.Pi

public section

/-! Exact finite-N scalar-observable Gaussian Stein bridge. Its inputs
are genuine L² terminal-state derivatives and their exponential growth
bound. It does not assert that an unspecified state family solves an SDE;
the actual variational equations supply those separate inputs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace NNReal ENNReal BigOperators
namespace SphericalAging.GaussianEnergyStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  HamiltonianObservableDerivative HamiltonianCoefficientBounds DisorderExponentialIntegrability
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The actual coefficient gradient pairing has the L² bound needed for
Gaussian integrability of the scalar observable derivative. -/
theorem coefficient_pairing_bound (hN : 0 < N) (I : TensorIndex N p)
    (X V : StateL2 N P) (hsphere : ∀ᵐ ω ∂P,‖X ω‖^2=(N : ℝ)) :
    ‖∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (V ω) ∂P‖ ≤
      (p : ℝ)*‖V‖ := by
  have hg := HamiltonianDerivativeCovariance.coefficient_contDiff I
  have hc : Continuous (gradient (hamiltonianCoefficient I)) :=
    (InnerProductSpace.toDual ℝ (State N)).symm.continuous.comp (hg.continuous_fderiv (by simp))
  have hm : MemLp (fun ω => gradient (hamiltonianCoefficient I) (X ω)) 2 P := by
    apply MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable X)) (p : ℝ)
    filter_upwards [hsphere] with ω hω
    exact coefficient_gradient_sphere_bound hN I _ hω
  let G : StateL2 N P := hm.toLp _
  have hGbound : ‖G‖ ≤ (p : ℝ) := by
    have hh := Lp.norm_le_of_ae_bound (f := G) (Nat.cast_nonneg p) (by
      filter_upwards [hm.coeFn_toLp,hsphere] with ω hω hs
      rw [show G ω=gradient (hamiltonianCoefficient I) (X ω) from hω]
      exact coefficient_gradient_sphere_bound hN I _ hs)
    simpa only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,Real.one_rpow,one_mul] using hh
  have he : inner ℝ G V=∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (V ω) ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with ω hω
    rw [show G ω=gradient (hamiltonianCoefficient I) (X ω) from hω]
  rw [← he]
  exact (norm_inner_le_norm G V).trans (mul_le_mul_of_nonneg_right hGbound (norm_nonneg V))

/-- True coefficientwise Stein equality for an L²-differentiable sphere
state family. Integrability and derivative measurability are proved from
the actual Gaussian law, bounded sphere coefficients, and exponential
growth; they are not supplied as Stein assumptions. -/
theorem coefficient_energy_stein (hN : 0 < N) (hp : 0 < p) (I : TensorIndex N p)
    (X : Disorder N p → StateL2 N P) (DX : Disorder N p → Disorder N p →L[ℝ] StateL2 N P)
    (hX : ∀ J,HasFDerivAt X (DX J) J)
    (hsphere : ∀ J,∀ᵐ ω ∂P,‖X J ω‖^2=(N : ℝ)) (C b : ℝ≥0) (a : ℝ)
    (hgrowth : ∀ J,‖DX J (Pi.single I 1)‖ ≤ C*Real.exp (a+(b : ℝ)*‖J‖)) :
    (∫ J,J I*(∫ ω,hamiltonianCoefficient I (X J ω) ∂P) ∂disorderLaw N p)=
      ∫ J,∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X J ω))
        (DX J (Pi.single I 1) ω) ∂P ∂disorderLaw N p := by
  let F : Disorder N p → ℝ := fun J => ∫ ω,hamiltonianCoefficient I (X J ω) ∂P
  let dF : Disorder N p → ℝ := fun J => fderiv ℝ F J (Pi.single I 1)
  have hFd (J : Disorder N p) : DifferentiableAt ℝ F J := by
    obtain ⟨A,hA,_⟩ := coefficient_expectation_hasFDerivAt I (hX J) hsphere
    exact hA.differentiableAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun J => (hFd J).continuousAt)
  have hFeq (J : Disorder N p) : dF J=∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X J ω))
      (DX J (Pi.single I 1) ω) ∂P := by
    obtain ⟨A,hA,hpair⟩ := coefficient_expectation_hasFDerivAt I (hX J) hsphere
    change fderiv ℝ F J (Pi.single I 1)=_
    rw [hA.fderiv]
    exact hpair _
  have hFb (J : Disorder N p) : ‖F J‖ ≤ Real.sqrt (N : ℝ) := by
    have hi := (coefficient_memLp_of_sphere hN hp I (X J) (Lp.aestronglyMeasurable (X J)) (hsphere J)).integrable (by norm_num)
    calc
      _ ≤ ∫ ω,‖hamiltonianCoefficient I (X J ω)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ _ω : Ω,Real.sqrt (N : ℝ) ∂P := by
        apply integral_mono_ae hi.norm (integrable_const _)
        filter_upwards [hsphere J] with ω hω
        exact coefficient_sphere_bound hN hp I _ hω
      _ = _ := by simp
  have hF2 : MemLp F 2 (disorderLaw N p) := MemLp.of_bound hFc.aestronglyMeasurable
    (Real.sqrt (N : ℝ)) (.of_forall hFb)
  have hFi := hF2.integrable (by norm_num)
  have hIF : Integrable (fun J : Disorder N p => J I*F J) (disorderLaw N p) :=
    memLp_one_iff_integrable.mp ((coordinate_memLp N p I).mul hF2)
  have hdfm : AEStronglyMeasurable dF (disorderLaw N p) :=
    (measurable_fderiv_apply_const ℝ F (Pi.single I 1)).aestronglyMeasurable
  have hdfi : Integrable dF (disorderLaw N p) := by
    apply ((disorder_affine_exp_integrable hN hp a b).const_mul ((p : ℝ)*C)).mono' hdfm
    exact .of_forall (fun J => by
      rw [hFeq J]
      exact (coefficient_pairing_bound hN I (X J) _ (hsphere J)).trans
        ((mul_le_mul_of_nonneg_left (hgrowth J) (Nat.cast_nonneg p)).trans_eq (by ring)))
  have hd (J : Disorder N p) (x : ℝ) : HasDerivAt (fun y => F (Function.update J I y))
      (dF (Function.update J I x)) x := by
    exact (hFd _).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_update J I x)
  have hh := disorder_integration_by_parts I hd hFi hdfi hIF
  exact hh.trans (integral_congr_ae (.of_forall hFeq))

/-- Finite ordered-tensor summation gives the exact Gaussian Hamiltonian
energy identity for the genuine differentiated terminal family. -/
theorem hamiltonian_energy_stein (hN : 0 < N) (hp : 0 < p)
    (X : Disorder N p → StateL2 N P) (DX : Disorder N p → Disorder N p →L[ℝ] StateL2 N P)
    (hX : ∀ J,HasFDerivAt X (DX J) J)
    (hsphere : ∀ J,∀ᵐ ω ∂P,‖X J ω‖^2=(N : ℝ))
    (C b : TensorIndex N p → ℝ≥0) (a : TensorIndex N p → ℝ)
    (hgrowth : ∀ I J,‖DX J (Pi.single I 1)‖ ≤ C I*Real.exp (a I+(b I : ℝ)*‖J‖)) :
    (∫ J,∫ ω,Hamiltonian N p J (X J ω) ∂P ∂disorderLaw N p)=
      ∑ I : TensorIndex N p,∫ J,∫ ω,inner ℝ
        (gradient (hamiltonianCoefficient I) (X J ω)) (DX J (Pi.single I 1) ω) ∂P
          ∂disorderLaw N p := by
  have hcoef (I : TensorIndex N p) (J : Disorder N p) :
      Integrable (fun ω => hamiltonianCoefficient I (X J ω)) P :=
    (coefficient_memLp_of_sphere hN hp I (X J) (Lp.aestronglyMeasurable (X J))
      (hsphere J)).integrable (by norm_num)
  have hH (J : Disorder N p) : (∫ ω,Hamiltonian N p J (X J ω) ∂P)=
      ∑ I : TensorIndex N p,J I*(∫ ω,hamiltonianCoefficient I (X J ω) ∂P) := by
    rw [show (fun ω => Hamiltonian N p J (X J ω))=
      (fun ω => ∑ I : TensorIndex N p,J I*hamiltonianCoefficient I (X J ω)) from
        funext (fun ω => hamiltonian_eq_sum_coefficients J (X J ω)),
      integral_finsetSum Finset.univ (fun I _ => (hcoef I J).const_mul (J I))]
    exact Finset.sum_congr rfl (fun I _ => integral_const_mul _ _)
  have hterm (I : TensorIndex N p) : Integrable
      (fun J : Disorder N p => J I*(∫ ω,hamiltonianCoefficient I (X J ω) ∂P)) (disorderLaw N p) := by
    have hc : Continuous (fun J : Disorder N p => ∫ ω,hamiltonianCoefficient I (X J ω) ∂P) := by
      apply continuous_iff_continuousAt.mpr
      intro J
      obtain ⟨A,hA,_⟩ := coefficient_expectation_hasFDerivAt I (hX J) hsphere
      exact hA.continuousAt
    have hb (J : Disorder N p) : ‖∫ ω,hamiltonianCoefficient I (X J ω) ∂P‖ ≤ Real.sqrt (N : ℝ) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      calc
        _ ≤ ∫ _ω : Ω,Real.sqrt (N : ℝ) ∂P := by
          apply integral_mono_ae (hcoef I J).norm (integrable_const _)
          filter_upwards [hsphere J] with ω hω
          exact coefficient_sphere_bound hN hp I _ hω
        _ = _ := by simp
    have hm : MemLp (fun J : Disorder N p => ∫ ω,hamiltonianCoefficient I (X J ω) ∂P) 2
        (disorderLaw N p) := MemLp.of_bound hc.aestronglyMeasurable (Real.sqrt (N : ℝ)) (.of_forall hb)
    exact memLp_one_iff_integrable.mp ((coordinate_memLp N p I).mul hm)
  calc
    _ = ∫ J,∑ I : TensorIndex N p,J I*(∫ ω,hamiltonianCoefficient I (X J ω) ∂P)
        ∂disorderLaw N p := integral_congr_ae (.of_forall hH)
    _ = ∑ I : TensorIndex N p,∫ J,J I*(∫ ω,hamiltonianCoefficient I (X J ω) ∂P)
        ∂disorderLaw N p := integral_finsetSum Finset.univ (fun I _ => hterm I)
    _ = _ := Finset.sum_congr rfl (fun I _ => coefficient_energy_stein hN hp I X DX
      hX hsphere (C I) (b I) (a I) (hgrowth I))

/-- Actual inhomogeneous variational SDEs imply the Gaussian-integrable
terminal L² growth bound. No moment estimate is an assumption. -/
theorem terminal_norm_growth_of_affine_variation
    (F₀ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (driver : BrownianDriver N P (NullAugmentation.augment F₀ P))
    (K0 K1 Ks B : ℝ≥0) (T t : ℝ≥0) (ht : t ≤ T)
    (rows : ∀ J : Disorder N p,Fin N → PredictableLinearCoefficient.Coefficient
      (N := N) (F := NullAugmentation.augment F₀ P) (P := P) (K0+‖J‖₊*K1))
    (noise : Disorder N p → Fin N → Fin N → PredictableLinearCoefficient.Coefficient
      (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Ks)
    (forcing : Disorder N p → Fin N → InhomogeneousLinearSDE.Forcing
      (F := NullAugmentation.augment F₀ P) (P := P) B)
    (Z : Disorder N p → ℝ≥0 → Ω → State N) (V : Disorder N p → StateL2 N P)
    (hsol : ∀ J,InhomogeneousLinearSDE.IsStrongSolutionOn (rows J) (noise J) (forcing J)
      driver 0 (Z J) T) (hV : ∀ J,(V J : Ω → State N)=ᵐ[P] Z J t) :
    ∀ J,‖V J‖ ≤ B*Real.exp
      (((AffineSDEFourthMoment.affineRadialDriftConstant N K0 Ks : ℝ)*(t : ℝ))/2+
        ((N*K1*t : ℝ≥0) : ℝ)*‖J‖) := by
  intro J
  have hh := (AffineSDESecondLocalization.affine_solution_secondMoment_augmented F₀ (hsol J) t ht).2
  have hn : ‖V J‖^2=(∫ ω,‖Z J t ω‖^2 ∂P) := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hV J] with ω hω
    rw [hω,real_inner_self_eq_norm_sq]
  rw [← hn,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] at hh
  let e : ℝ := ((AffineSDEFourthMoment.affineRadialDriftConstant N K0 Ks : ℝ)*(t : ℝ))/2+
      ((N*K1*t : ℝ≥0) : ℝ)*‖J‖
  have he : (AffineSDEFourthMoment.affineRadialDriftConstant N (K0+‖J‖₊*K1) Ks : ℝ)*(t : ℝ)=e+e := by
    simp only [e,AffineSDEFourthMoment.affineRadialDriftConstant,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_pow,NNReal.coe_natCast,NNReal.coe_ofNat,coe_nnnorm]
    ring
  have hs : (B*Real.exp e)^2=(B : ℝ)^2*Real.exp
      ((AffineSDEFourthMoment.affineRadialDriftConstant N (K0+‖J‖₊*K1) Ks : ℝ)*(t : ℝ)) := by
    rw [he,mul_pow,pow_two (Real.exp e)]
    exact congrArg (fun r : ℝ => (B : ℝ)^2*r) (Real.exp_add e e).symm
  change ‖V J‖ ≤ (B : ℝ)*Real.exp e
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hs]
  exact hh

end SphericalAging.GaussianEnergyStein
