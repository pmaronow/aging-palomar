module

public import SphericalAging.GaussianEnergyStein

public section

/-! Gaussian energy integration by parts for actual sphere-ball families.
Finite fork means lie in the ball, so the sphere-only Stein interface
cannot be applied to them. Compact truncation is removed on the whole ball. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.GaussianBallEnergyStein
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
  GaussianIntegrationByParts HamiltonianObservableDerivative GaussianObservableDerivative
  HamiltonianCoefficientBounds DisorderExponentialIntegrability
open scoped NNReal ENNReal InnerProductSpace Topology BigOperators
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem coefficientCutoff_eq_ball (I : TensorIndex N p) (x : State N)
    (hx : ‖x‖≤Real.sqrt (N:ℝ)) : coefficientCutoff I x=hamiltonianCoefficient I x :=
  coefficientCutoff_eq I x (hx.trans (by unfold cutoffRadius;linarith))

theorem coefficientCutoff_fderiv_eq_ball (I : TensorIndex N p) (x : State N)
    (hx : ‖x‖≤Real.sqrt (N:ℝ)) :
    fderiv ℝ (coefficientCutoff I) x=fderiv ℝ (hamiltonianCoefficient I) x :=
  (coefficientCutoff_eventuallyEq I x (by unfold cutoffRadius;linarith)).fderiv_eq

theorem coefficient_expectation_hasFDerivAt_ball {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (I : TensorIndex N p)
    {X : E→StateL2 N P} {D : E→L[ℝ] StateL2 N P} {x : E}
    (hX : HasFDerivAt X D x) (hball : ∀y,∀ᵐω ∂P,‖X y ω‖≤Real.sqrt (N:ℝ)) :
    ∃A : E→L[ℝ] ℝ,
      HasFDerivAt (fun y => ∫ω,hamiltonianCoefficient I (X y ω) ∂P) A x ∧
      ∀v,A v=∫ω,⟪gradient (hamiltonianCoefficient I) (X x ω),D v ω⟫_ℝ ∂P := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := coefficientCutoff_bounds I
  let g := coefficientCutoff I
  let hg := coefficientCutoff_contDiff I
  let A := (observableDerivative g hg K hK (X x)).comp D
  have hd := observable_family_hasFDerivAt g hg C K L hC hK hL hX
  have he : (fun y => ∫ω,g (X y ω) ∂P)=
      (fun y => ∫ω,hamiltonianCoefficient I (X y ω) ∂P) := by
    funext y
    exact integral_congr_ae ((hball y).mono fun ω hω => coefficientCutoff_eq_ball I _ hω)
  refine ⟨A,he ▸ hd,?_⟩
  intro v
  change observableDerivative g hg K hK (X x) (D v)=_
  rw [observableDerivative_apply]
  apply integral_congr_ae
  filter_upwards [hball x] with ω hω
  rw [coefficientCutoff_fderiv_eq_ball I _ hω]
  exact inner_gradient_left.symm

theorem coefficient_pairing_bound_ball (hN : 0<N) (I : TensorIndex N p)
    (X V : StateL2 N P) (hball : ∀ᵐω ∂P,‖X ω‖≤Real.sqrt (N:ℝ)) :
    ‖∫ω,⟪gradient (hamiltonianCoefficient I) (X ω),V ω⟫_ℝ ∂P‖≤(p:ℝ)*‖V‖ := by
  have hg := HamiltonianDerivativeCovariance.coefficient_contDiff I
  have hc : Continuous (gradient (hamiltonianCoefficient I)) :=
    (InnerProductSpace.toDual ℝ (State N)).symm.continuous.comp (hg.continuous_fderiv (by simp))
  have hm : MemLp (fun ω => gradient (hamiltonianCoefficient I) (X ω)) 2 P :=
    MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable X)) (p:ℝ)
      (hball.mono fun ω hω => coefficient_gradient_ball_bound hN I _ hω)
  let G := hm.toLp (fun ω => gradient (hamiltonianCoefficient I) (X ω))
  have hG : ‖G‖≤(p:ℝ) := by
    have hh := Lp.norm_le_of_ae_bound (f:=G) (Nat.cast_nonneg p) (by
      filter_upwards [hm.coeFn_toLp,hball] with ω hω hb
      rw [show G ω=gradient (hamiltonianCoefficient I) (X ω) from hω]
      exact coefficient_gradient_ball_bound hN I _ hb)
    simpa [measureUnivNNReal] using hh
  have he : ⟪G,V⟫_ℝ=∫ω,⟪gradient (hamiltonianCoefficient I) (X ω),V ω⟫_ℝ ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact hm.coeFn_toLp.mono fun ω hω => by
      change ⟪G ω,V ω⟫_ℝ=⟪gradient (hamiltonianCoefficient I) (X ω),V ω⟫_ℝ
      rw [show G ω=gradient (hamiltonianCoefficient I) (X ω) from hω]
  rw [←he]
  exact (norm_inner_le_norm G V).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg V))

theorem coefficient_energy_stein_ball (hN : 0<N) (hp : 0<p) (I : TensorIndex N p)
    (X : Disorder N p→StateL2 N P) (DX : Disorder N p→Disorder N p→L[ℝ] StateL2 N P)
    (hX : ∀J,HasFDerivAt X (DX J) J)
    (hball : ∀J,∀ᵐω ∂P,‖X J ω‖≤Real.sqrt (N:ℝ)) (C b : ℝ≥0) (a : ℝ)
    (hgrowth : ∀J,‖DX J (Pi.single I 1)‖≤C*Real.exp (a+(b:ℝ)*‖J‖)) :
    (∫J,J I*(∫ω,hamiltonianCoefficient I (X J ω) ∂P) ∂disorderLaw N p)=
      ∫J,∫ω,⟪gradient (hamiltonianCoefficient I) (X J ω),
        DX J (Pi.single I 1) ω⟫_ℝ ∂P ∂disorderLaw N p := by
  let F : Disorder N p→ℝ := fun J => ∫ω,hamiltonianCoefficient I (X J ω) ∂P
  let dF : Disorder N p→ℝ := fun J => fderiv ℝ F J (Pi.single I 1)
  have hFd (J : Disorder N p) : DifferentiableAt ℝ F J := by
    obtain ⟨A,hA,_⟩ := coefficient_expectation_hasFDerivAt_ball I (hX J) hball
    exact hA.differentiableAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun J => (hFd J).continuousAt)
  have hFeq (J : Disorder N p) : dF J=∫ω,⟪gradient (hamiltonianCoefficient I) (X J ω),
      DX J (Pi.single I 1) ω⟫_ℝ ∂P := by
    obtain ⟨A,hA,hpair⟩ := coefficient_expectation_hasFDerivAt_ball I (hX J) hball
    change fderiv ℝ F J (Pi.single I 1)=_
    rw [hA.fderiv]
    exact hpair _
  obtain ⟨C₀,K₀,L₀,hC₀,hK₀,hL₀⟩ := coefficientCutoff_bounds I
  have hFb (J : Disorder N p) : ‖F J‖≤C₀ := by
    have he : F J=∫ω,coefficientCutoff I (X J ω) ∂P :=
      integral_congr_ae ((hball J).mono fun ω hω => (coefficientCutoff_eq_ball I _ hω).symm)
    rw [he]
    exact (norm_integral_le_integral_norm _).trans (by
      simpa using integral_mono
        (observable_integrable _ (coefficientCutoff_contDiff I).continuous C₀ hC₀ (X J)).norm
        (integrable_const (C₀:ℝ)) (fun ω => hC₀ (X J ω)))
  have hF2 : MemLp F 2 (disorderLaw N p) := MemLp.of_bound hFc.aestronglyMeasurable C₀ (.of_forall hFb)
  have hFi := hF2.integrable (by norm_num)
  have hIF : Integrable (fun J : Disorder N p => J I*F J) (disorderLaw N p) :=
    memLp_one_iff_integrable.mp ((coordinate_memLp N p I).mul hF2)
  have hdfm : AEStronglyMeasurable dF (disorderLaw N p) :=
    (measurable_fderiv_apply_const ℝ F (Pi.single I 1)).aestronglyMeasurable
  have hdfi : Integrable dF (disorderLaw N p) := by
    apply ((disorder_affine_exp_integrable hN hp a b).const_mul ((p:ℝ)*C)).mono' hdfm
    exact .of_forall (fun J => by
      rw [hFeq J]
      exact (coefficient_pairing_bound_ball hN I (X J) _ (hball J)).trans
        ((mul_le_mul_of_nonneg_left (hgrowth J) (Nat.cast_nonneg p)).trans_eq (by ring)))
  have hd (J : Disorder N p) (x : ℝ) : HasDerivAt (fun y => F (Function.update J I y))
      (dF (Function.update J I x)) x :=
    (hFd _).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_update J I x)
  exact (disorder_integration_by_parts I hd hFi hdfi hIF).trans
    (integral_congr_ae (.of_forall hFeq))

theorem coefficient_integrable_ball (I : TensorIndex N p) (X : StateL2 N P)
    (hball : ∀ᵐω ∂P,‖X ω‖≤Real.sqrt (N:ℝ)) :
    Integrable (fun ω => hamiltonianCoefficient I (X ω)) P := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := coefficientCutoff_bounds I
  exact (observable_integrable _ (coefficientCutoff_contDiff I).continuous C hC X).congr
    (hball.mono fun ω hω => coefficientCutoff_eq_ball I _ hω)

theorem hamiltonian_energy_stein_ball (hN : 0<N) (hp : 0<p)
    (X : Disorder N p→StateL2 N P) (DX : Disorder N p→Disorder N p→L[ℝ] StateL2 N P)
    (hX : ∀J,HasFDerivAt X (DX J) J)
    (hball : ∀J,∀ᵐω ∂P,‖X J ω‖≤Real.sqrt (N:ℝ))
    (C b : TensorIndex N p→ℝ≥0) (a : TensorIndex N p→ℝ)
    (hgrowth : ∀I J,‖DX J (Pi.single I 1)‖≤C I*Real.exp (a I+(b I:ℝ)*‖J‖)) :
    (∫J,∫ω,Hamiltonian N p J (X J ω) ∂P ∂disorderLaw N p)=
      ∑I : TensorIndex N p,∫J,∫ω,⟪gradient (hamiltonianCoefficient I) (X J ω),
        DX J (Pi.single I 1) ω⟫_ℝ ∂P ∂disorderLaw N p := by
  have hcoef (I : TensorIndex N p) (J : Disorder N p) :=
    coefficient_integrable_ball I (X J) (hball J)
  have hH (J : Disorder N p) : (∫ω,Hamiltonian N p J (X J ω) ∂P)=
      ∑I : TensorIndex N p,J I*(∫ω,hamiltonianCoefficient I (X J ω) ∂P) := by
    rw [show (fun ω => Hamiltonian N p J (X J ω))=
      (fun ω => ∑I : TensorIndex N p,J I*hamiltonianCoefficient I (X J ω)) from
        funext (fun ω => hamiltonian_eq_sum_coefficients J (X J ω)),
      integral_finsetSum Finset.univ (fun I _ => (hcoef I J).const_mul (J I))]
    exact Finset.sum_congr rfl (fun I _ => integral_const_mul _ _)
  have hterm (I : TensorIndex N p) : Integrable
      (fun J : Disorder N p => J I*(∫ω,hamiltonianCoefficient I (X J ω) ∂P)) (disorderLaw N p) := by
    have hc : Continuous (fun J : Disorder N p => ∫ω,hamiltonianCoefficient I (X J ω) ∂P) := by
      apply continuous_iff_continuousAt.mpr
      intro J
      obtain ⟨A,hA,_⟩ := coefficient_expectation_hasFDerivAt_ball I (hX J) hball
      exact hA.continuousAt
    obtain ⟨C₀,K₀,L₀,hC₀,hK₀,hL₀⟩ := coefficientCutoff_bounds I
    have hb (J : Disorder N p) : ‖∫ω,hamiltonianCoefficient I (X J ω) ∂P‖≤C₀ := by
      have he : (∫ω,hamiltonianCoefficient I (X J ω) ∂P)=
          ∫ω,coefficientCutoff I (X J ω) ∂P :=
        integral_congr_ae ((hball J).mono fun ω hω => (coefficientCutoff_eq_ball I _ hω).symm)
      rw [he]
      exact (norm_integral_le_integral_norm _).trans (by
        simpa using integral_mono (observable_integrable _ (coefficientCutoff_contDiff I).continuous
          C₀ hC₀ (X J)).norm (integrable_const (C₀:ℝ)) (fun ω => hC₀ (X J ω)))
    have hm : MemLp (fun J : Disorder N p => ∫ω,hamiltonianCoefficient I (X J ω) ∂P) 2
        (disorderLaw N p) := MemLp.of_bound hc.aestronglyMeasurable C₀ (.of_forall hb)
    exact memLp_one_iff_integrable.mp ((coordinate_memLp N p I).mul hm)
  calc
    _ = ∫J,∑I : TensorIndex N p,J I*(∫ω,hamiltonianCoefficient I (X J ω) ∂P)
        ∂disorderLaw N p := integral_congr_ae (.of_forall hH)
    _ = ∑I : TensorIndex N p,∫J,J I*(∫ω,hamiltonianCoefficient I (X J ω) ∂P)
        ∂disorderLaw N p := integral_finsetSum Finset.univ (fun I _ => hterm I)
    _ = _ := Finset.sum_congr rfl (fun I _ => coefficient_energy_stein_ball hN hp I X DX
      hX hball (C I) (b I) (a I) (hgrowth I))

end SphericalAging.GaussianBallEnergyStein
