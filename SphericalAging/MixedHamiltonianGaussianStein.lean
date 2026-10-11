module

public import SphericalAging.MixedHamiltonianObservableDerivative
public import SphericalAging.HamiltonianEnergySteinActual

public section

/-! True finite-dimensional Gaussian integration by parts for the actual
Hamiltonian gradient at one terminal time paired with the actual state at
another. Both disorder derivative terms and every integrability condition
are proved from the actual terminal variational classes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.MixedHamiltonianGaussianStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  MixedHamiltonianObservableDerivative HamiltonianDisorderTerminalDerivative
  HamiltonianEnergySteinActual HamiltonianDisorderResponseGrowth HamiltonianPredictableForcing
  DisorderExponentialIntegrability
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p M : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma observableDerivative_norm_apply (g : State M → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (K : ℝ≥0) (hK : ∀ z,‖fderiv ℝ g z‖ ≤ K) (U V : StateL2 M P) :
    ‖observableDerivative g hg K hK U V‖ ≤ (K : ℝ)*‖V‖ := by
  have hG : ‖gradientClass g hg K hK U‖ ≤ (K : ℝ) := by
    have hb := Lp.norm_le_of_ae_bound (f := gradientClass g hg K hK U) K.2 (by
      filter_upwards [(gradient_memLp g hg K hK U).coeFn_toLp] with ω hω
      rw [show gradientClass g hg K hK U ω=gradient g (U ω) from hω]
      convert (hK (U ω)) using 1 <;> try rfl
      exact (InnerProductSpace.toDual ℝ (State M)).symm.norm_map _)
    simp only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,
      Real.one_rpow,one_mul] at hb
    exact hb
  exact (norm_inner_le_norm _ V).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg V))

/-- A compact smooth scalar expectation satisfies Gaussian Stein once
its actual terminal derivative has a proved Gaussian-integrable bound. -/
theorem compact_observable_stein (I : TensorIndex N p)
    (g : State M → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (C K L : ℝ≥0)
    (hC : ∀ z,‖g z‖ ≤ C) (hK : ∀ z,‖fderiv ℝ g z‖ ≤ K)
    (hL : LipschitzWith L (fderiv ℝ g))
    (Z : Disorder N p → StateL2 M P)
    (DZ : Disorder N p → Disorder N p →L[ℝ] StateL2 M P)
    (hZ : ∀ J,HasFDerivAt Z (DZ J) J)
    (B : Disorder N p → ℝ) (hBi : Integrable B (disorderLaw N p))
    (hB : ∀ J,‖DZ J (Pi.single I 1)‖ ≤ B J) :
    (∫ J : Disorder N p,J I*(∫ ω,g (Z J ω) ∂P) ∂disorderLaw N p)=
      ∫ J : Disorder N p,fderiv ℝ (fun K : Disorder N p => ∫ ω,g (Z K ω) ∂P)
        J (Pi.single I 1) ∂disorderLaw N p := by
  let f := fun J : Disorder N p => ∫ ω,g (Z J ω) ∂P
  let df := fun J : Disorder N p => fderiv ℝ f J (Pi.single I 1)
  have hfd (J : Disorder N p) : HasFDerivAt f
      ((observableDerivative g hg K hK (Z J)).comp (DZ J)) J :=
    observable_family_hasFDerivAt g hg C K L hC hK hL (hZ J)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun J => (hfd J).continuousAt)
  have hfb (J : Disorder N p) : ‖f J‖ ≤ C := by
    refine (norm_integral_le_integral_norm _).trans ?_
    calc
      _ ≤ ∫ _ω : Ω,(C : ℝ) ∂P := integral_mono_ae
        (observable_integrable g hg.continuous C hC (Z J)).norm (integrable_const _)
        (.of_forall (fun ω => hC (Z J ω)))
      _ = _ := by simp
  have hf2 : MemLp f 2 (disorderLaw N p) := MemLp.of_bound hfc.aestronglyMeasurable C (.of_forall hfb)
  have hfi := hf2.integrable (by norm_num)
  have hif : Integrable (fun J : Disorder N p => J I*f J) (disorderLaw N p) :=
    memLp_one_iff_integrable.mp ((coordinate_memLp N p I).mul hf2)
  have hdfm : AEStronglyMeasurable df (disorderLaw N p) :=
    (measurable_fderiv_apply_const ℝ f (Pi.single I 1)).aestronglyMeasurable
  have hdfi : Integrable df (disorderLaw N p) := by
    apply (hBi.const_mul (K : ℝ)).mono' hdfm
    exact .of_forall (fun J => by
      change ‖fderiv ℝ f J (Pi.single I 1)‖ ≤ _
      rw [(hfd J).fderiv,ContinuousLinearMap.comp_apply]
      exact (observableDerivative_norm_apply g hg K hK _ _).trans
        (mul_le_mul_of_nonneg_left (hB J) K.2))
  have hd (J : Disorder N p) (x : ℝ) :
      HasDerivAt (fun y => f (Function.update J I y)) (df (Function.update J I x)) x :=
    (hfd _).differentiableAt.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_update J I x)
  exact disorder_integration_by_parts I hd hfi hdfi hif

/-- Literal mixed coefficient Gaussian Stein identity for the actual
sphere SDE. The Hessian term at time t and the state-response term at time
s are both present; no mean-field equation is an input. -/
theorem coefficient_gradient_pairing_stein_actual (hN : 0 < N) (hp : 0 < p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) (I : TensorIndex N p) :
    (∫ J : Disorder N p,J I*(∫ ω,
      inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
        (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω) ∂P) ∂disorderLaw N p)=
      ∫ J : Disorder N p,∫ ω,
        inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1) ω))
          (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω)+
        inner ℝ (gradient (hamiltonianCoefficient I)
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T s (Pi.single I 1) ω)
            ∂P ∂disorderLaw N p := by
  let D := NullAugmentation.driver D₀
  let Xt := fun J : Disorder N p => stateClass D β R hR J x T t
  let Xs := fun J : Disorder N p => stateClass D β R hR J x T s
  let Dt := fun J : Disorder N p => stateResponse D β R hR J x T t
  let Ds := fun J : Disorder N p => stateResponse D β R hR J x T s
  let Z := fun J : Disorder N p => pairClassOperator N P (Xt J,Xs J)
  let DZ := fun J : Disorder N p => (pairClassOperator N P).comp ((Dt J).prod (Ds J))
  have hZ (J : Disorder N p) : HasFDerivAt Z (DZ J) J :=
    (pairClassOperator N P).hasFDerivAt.comp J
      ((stateClass_hasFDerivAt_disorder D₀ β R hR J x T t).prodMk
        (stateClass_hasFDerivAt_disorder D₀ β R hR J x T s))
  let Bt := fun J : Disorder N p => (disorderConstant (N := N) (p := p) β R hR : ℝ)*
    Real.exp (exponentBase (N := N) (p := p) β R hR t / 2 +
      ((exponentSlope (N := N) (p := p) β R hR t / 2 : ℝ≥0) : ℝ)*‖J‖)
  let Bs := fun J : Disorder N p => (disorderConstant (N := N) (p := p) β R hR : ℝ)*
    Real.exp (exponentBase (N := N) (p := p) β R hR s / 2 +
      ((exponentSlope (N := N) (p := p) β R hR s / 2 : ℝ≥0) : ℝ)*‖J‖)
  let B := fun J : Disorder N p => ‖pairClassOperator N P‖*(Bt J+Bs J)
  have hBi : Integrable B (disorderLaw N p) := by
    exact (((disorder_affine_exp_integrable hN hp
      (exponentBase (N := N) (p := p) β R hR t / 2)
      (exponentSlope (N := N) (p := p) β R hR t / 2)).const_mul
      (disorderConstant (N := N) (p := p) β R hR : ℝ)).add
      ((disorder_affine_exp_integrable hN hp
      (exponentBase (N := N) (p := p) β R hR s / 2)
      (exponentSlope (N := N) (p := p) β R hR s / 2)).const_mul
      (disorderConstant (N := N) (p := p) β R hR : ℝ))).const_mul _
  have hB (J : Disorder N p) : ‖DZ J (Pi.single I 1)‖ ≤ B J := by
    have htB := stateResponse_coordinate_growth D₀ β R hR J x T t ht I
    have hsB := stateResponse_coordinate_growth D₀ β R hR J x T s hs I
    change ‖pairClassOperator N P (Dt J (Pi.single I 1),Ds J (Pi.single I 1))‖ ≤ _
    refine ((pairClassOperator N P).le_opNorm _).trans ?_
    rw [Prod.norm_def]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (max_le_max htB hsB).trans (max_le_add_of_nonneg (by positivity) (by positivity))
  obtain ⟨C,K,L,hC,hK,hL⟩ := mixedCutoff_bounds I
  have hh := compact_observable_stein I (mixedCutoff I) (mixedCutoff_contDiff I) C K L
    hC hK hL Z DZ hZ B hBi hB
  have he : (fun J : Disorder N p => ∫ ω,mixedCutoff I (Z J ω) ∂P)=
      (fun J : Disorder N p => ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (Xt J ω))
        (Xs J ω) ∂P) := by
    funext J
    apply integral_congr_ae
    filter_upwards [pairClassOperator_ae (Xt J) (Xs J),
      stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht,
      stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T s hs] with ω hz hxt hxs
    rw [hz,(mixedCutoff_eventuallyEq_onSphere I _ _ hxt hxs).eq_of_nhds]
    simp only [mixedPolynomial,firstState_joinState,secondState_joinState]
    rfl
  change (∫ J : Disorder N p,J I*((fun K : Disorder N p => ∫ ω,mixedCutoff I (Z K ω) ∂P) J) ∂disorderLaw N p)=_ at hh
  rw [he] at hh
  refine hh.trans (integral_congr_ae (.of_forall (fun J => ?_)))
  obtain ⟨A,hA,hpair⟩ := actual_mixed_expectation_hasFDerivAt (Nat.ne_of_gt hN) D₀ β R hR hNR
    J x hx T s t hs ht I
  dsimp only [Xt,Xs,D]
  rw [hA.fderiv]
  exact hpair _

end SphericalAging.MixedHamiltonianGaussianStein
