module

public import SphericalAging.HamiltonianObservableDerivative
public import SphericalAging.HamiltonianDisorderTerminalDerivative
public import SphericalAging.GaussianObservableDerivative
public import SphericalAging.FiniteCorrelationIto

public section

/-! Genuine differentiation of a two-time Hamiltonian coefficient-gradient
pairing. Both actual terminal L² states are joined in an honest Euclidean
space, a compact smooth mixed test is differentiated, and the cutoff is
removed on the proved physical sphere support. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.MixedHamiltonianObservableDerivative
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
open GaussianObservableDerivative HamiltonianDisorderTerminalDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def splitState (N : ℕ) : State (N+N) ≃L[ℝ] State N × State N := EuclideanSpace.finAddEquivProd

@[expose] def joinState (N : ℕ) : State N × State N →L[ℝ] State (N+N) :=
  (splitState N).symm.toContinuousLinearMap

@[expose] def firstState (N : ℕ) : State (N+N) →L[ℝ] State N :=
  (ContinuousLinearMap.fst ℝ (State N) (State N)).comp (splitState N).toContinuousLinearMap

@[expose] def secondState (N : ℕ) : State (N+N) →L[ℝ] State N :=
  (ContinuousLinearMap.snd ℝ (State N) (State N)).comp (splitState N).toContinuousLinearMap

@[simp] lemma firstState_joinState (N : ℕ) (x y : State N) :
    firstState N (joinState N (x,y))=x := by
  change ((splitState N) ((splitState N).symm (x,y))).1=x
  rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] lemma secondState_joinState (N : ℕ) (x y : State N) :
    secondState N (joinState N (x,y))=y := by
  change ((splitState N) ((splitState N).symm (x,y))).2=y
  rw [ContinuousLinearEquiv.apply_symm_apply]

@[expose] def joinFirst (N : ℕ) : State N →L[ℝ] State (N+N) :=
  (joinState N).comp (ContinuousLinearMap.inl ℝ (State N) (State N))

@[expose] def joinSecond (N : ℕ) : State N →L[ℝ] State (N+N) :=
  (joinState N).comp (ContinuousLinearMap.inr ℝ (State N) (State N))

@[expose] def pairClassOperator (N : ℕ) (P : Measure Ω) :
    Lp (State N) 2 P × Lp (State N) 2 P →L[ℝ] Lp (State (N+N)) 2 P :=
  ((joinFirst N).compLpL 2 P).comp (ContinuousLinearMap.fst ℝ _ _)+
    ((joinSecond N).compLpL 2 P).comp (ContinuousLinearMap.snd ℝ _ _)

theorem pairClassOperator_ae (U V : Lp (State N) 2 P) :
    (pairClassOperator N P (U,V) : Ω → State (N+N))=ᵐ[P]
      (fun ω => joinState N (U ω,V ω)) := by
  have hleft := (joinFirst N).coeFn_compLpL (p := 2) U
  have hright := (joinSecond N).coeFn_compLpL (p := 2) V
  have hadd := Lp.coeFn_add ((joinFirst N).compLpL 2 P U) ((joinSecond N).compLpL 2 P V)
  filter_upwards [hleft,hright,hadd] with ω hleft hright hadd
  change (((joinFirst N).compLpL 2 P U)+((joinSecond N).compLpL 2 P V)) ω=_
  rw [hadd]
  change ((joinFirst N).compLpL 2 P U) ω+((joinSecond N).compLpL 2 P V) ω=_
  rw [hleft,hright]
  change joinState N (U ω,0)+joinState N (0,V ω)=joinState N (U ω,V ω)
  rw [← map_add]
  congr 1
  simp

@[expose] def mixedPolynomial (I : TensorIndex N p) (z : State (N+N)) : ℝ :=
  inner ℝ (gradient (hamiltonianCoefficient I) (firstState N z)) (secondState N z)

@[expose] def mixedRadius (N : ℕ) : ℝ := ‖joinState N‖*Real.sqrt N+1

lemma mixedRadius_pos (N : ℕ) : 0<mixedRadius N := by
  unfold mixedRadius
  positivity

@[expose] def mixedCutoff (I : TensorIndex N p) (z : State (N+N)) : ℝ :=
  coefficientBump (N := N+N) (mixedRadius N) (mixedRadius_pos N) z*mixedPolynomial I z

lemma coefficientGradient_contDiff (I : TensorIndex N p) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient (hamiltonianCoefficient I)) :=
  (InnerProductSpace.toDual ℝ (State N)).symm.toContinuousLinearEquiv.contDiff.comp
    ((HamiltonianDerivativeCovariance.coefficient_contDiff I).fderiv_right (m := (⊤ : ℕ∞)) (by simp))

lemma mixedPolynomial_contDiff (I : TensorIndex N p) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedPolynomial I) :=
  ((coefficientGradient_contDiff I).comp (firstState N).contDiff).inner ℝ (secondState N).contDiff

lemma mixedCutoff_contDiff (I : TensorIndex N p) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedCutoff I) :=
  (coefficientBump (N := N+N) (mixedRadius N) (mixedRadius_pos N)).contDiff.mul (mixedPolynomial_contDiff I)

lemma mixedCutoff_hasCompactSupport (I : TensorIndex N p) : HasCompactSupport (mixedCutoff I) :=
  (coefficientBump (N := N+N) (mixedRadius N) (mixedRadius_pos N)).hasCompactSupport.mul_right

lemma mixedCutoff_eventuallyEq_onSphere (I : TensorIndex N p) (x y : State N)
    (hx : OnSphere x) (hy : OnSphere y) :
    mixedCutoff I=ᶠ[𝓝 (joinState N (x,y))] mixedPolynomial I := by
  have hp : ‖(x,y)‖=Real.sqrt N := by rw [Prod.norm_def,FiniteCorrelationIto.sphere_norm hx,FiniteCorrelationIto.sphere_norm hy,max_self]
  have hnorm : ‖joinState N (x,y)‖<mixedRadius N := by
    have hb := (joinState N).le_opNorm (x,y)
    rw [hp] at hb
    unfold mixedRadius
    linarith
  have hm : joinState N (x,y)∈Metric.ball (0 : State (N+N))
      (coefficientBump (N := N+N) (mixedRadius N) (mixedRadius_pos N)).rIn := by
    simpa only [coefficientBump,Metric.mem_ball,dist_zero_right] using hnorm
  exact ((coefficientBump (N := N+N) (mixedRadius N) (mixedRadius_pos N)).eventuallyEq_one_of_mem_ball hm).mono
    (fun z hz => by simp only [mixedCutoff,hz,Pi.one_apply,one_mul])

lemma mixedCutoff_bounds (I : TensorIndex N p) :
    ∃ C K L : ℝ≥0,(∀ z,‖mixedCutoff I z‖≤C) ∧ (∀ z,‖fderiv ℝ (mixedCutoff I) z‖≤K) ∧
      LipschitzWith L (fderiv ℝ (mixedCutoff I)) := by
  have hg := mixedCutoff_contDiff I
  have hs := mixedCutoff_hasCompactSupport I
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hg.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv (by simp))
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ)
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (by simp)
  exact ⟨⟨max C 0,le_max_right _ _⟩,⟨max K 0,le_max_right _ _⟩,L,
    (fun z => (hC z).trans (le_max_left _ _)),(fun z => (hK z).trans (le_max_left _ _)),hL⟩

lemma mixedPolynomial_fderiv_apply (I : TensorIndex N p) (x y a b : State N) :
    fderiv ℝ (mixedPolynomial I) (joinState N (x,y)) (joinState N (a,b))=
      inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) x a) y+
        inner ℝ (gradient (hamiltonianCoefficient I) x) b := by
  have hg := (coefficientGradient_contDiff I).differentiable (by simp)
  change fderiv ℝ (fun z => inner ℝ (gradient (hamiltonianCoefficient I) (firstState N z))
    (secondState N z)) (joinState N (x,y)) (joinState N (a,b))=_
  have hf : DifferentiableAt ℝ (fun z => gradient (hamiltonianCoefficient I) (firstState N z))
      (joinState N (x,y)) := by
    simpa only [Function.comp_def] using hg.differentiableAt.comp (joinState N (x,y))
      (firstState N).differentiableAt
  rw [fderiv_inner_apply ℝ hf (secondState N).differentiableAt]
  have hdf := hg.differentiableAt.hasFDerivAt.comp (joinState N (x,y)) (firstState N).hasFDerivAt
  have hde : fderiv ℝ (fun z => gradient (hamiltonianCoefficient I) (firstState N z))
      (joinState N (x,y))=(fderiv ℝ (gradient (hamiltonianCoefficient I))
        (firstState N (joinState N (x,y)))).comp (firstState N) := by
    simpa only [Function.comp_def] using hdf.fderiv
  rw [hde]
  simp only [ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,
    firstState_joinState,secondState_joinState]
  rw [add_comm]

/-- A true two-time coefficient-gradient expectation derivative for any
actual L² pair family with proved physical sphere support. -/
theorem mixed_expectation_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : TensorIndex N p) {X Y : E → Lp (State N) 2 P}
    {DX DY : E →L[ℝ] Lp (State N) 2 P} {e : E}
    (hX : HasFDerivAt X DX e) (hY : HasFDerivAt Y DY e)
    (hXs : ∀ a,∀ᵐ ω ∂P,OnSphere (X a ω)) (hYs : ∀ a,∀ᵐ ω ∂P,OnSphere (Y a ω)) :
    ∃ A : E →L[ℝ] ℝ,
      HasFDerivAt (fun a => ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X a ω)) (Y a ω) ∂P) A e ∧
      ∀ v,A v=∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (X e ω) (DX v ω)) (Y e ω)+
        inner ℝ (gradient (hamiltonianCoefficient I) (X e ω)) (DY v ω) ∂P := by
  let Z := fun a => pairClassOperator N P (X a,Y a)
  let DZ := (pairClassOperator N P).comp (DX.prod DY)
  have hZ : HasFDerivAt Z DZ e := (pairClassOperator N P).hasFDerivAt.comp e (hX.prodMk hY)
  obtain ⟨C,K,L,hC,hK,hL⟩ := mixedCutoff_bounds I
  let A := (observableDerivative (mixedCutoff I) (mixedCutoff_contDiff I) K hK (Z e)).comp DZ
  have hd := observable_family_hasFDerivAt (mixedCutoff I) (mixedCutoff_contDiff I) C K L hC hK hL hZ
  have he : (fun a => ∫ ω,mixedCutoff I (Z a ω) ∂P)=
      (fun a => ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X a ω)) (Y a ω) ∂P) := by
    funext a
    apply integral_congr_ae
    filter_upwards [pairClassOperator_ae (X a) (Y a),hXs a,hYs a] with ω hz hx hy
    rw [hz,(mixedCutoff_eventuallyEq_onSphere I _ _ hx hy).eq_of_nhds]
    simp only [mixedPolynomial,firstState_joinState,secondState_joinState]
  refine ⟨A,by simpa only [he] using hd,?_⟩
  intro v
  change observableDerivative (mixedCutoff I) (mixedCutoff_contDiff I) K hK (Z e) (DZ v)=_
  rw [observableDerivative_apply]
  apply integral_congr_ae
  filter_upwards [pairClassOperator_ae (X e) (Y e),pairClassOperator_ae (DX v) (DY v),hXs e,hYs e] with ω hz hv hx hy
  change fderiv ℝ (mixedCutoff I) (Z e ω) ((pairClassOperator N P (DX v,DY v)) ω)=_
  rw [hz,hv,(mixedCutoff_eventuallyEq_onSphere I _ _ hx hy).fderiv_eq,mixedPolynomial_fderiv_apply]

/-- Genuine mixed two-terminal derivative of the actual Hamiltonian
process in its finite ordered tensor disorder, with every analytic input
supplied by the constructed process and its variational equation. -/
theorem actual_mixed_expectation_hasFDerivAt (hN : N ≠ 0)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) (I : TensorIndex N p) :
    ∃ A : Disorder N p →L[ℝ] ℝ,
      HasFDerivAt (fun K : Disorder N p => ∫ ω,
        inner ℝ (gradient (hamiltonianCoefficient I)
          (stateClass (NullAugmentation.driver D₀) β R hR K x T t ω))
          (stateClass (NullAugmentation.driver D₀) β R hR K x T s ω) ∂P) A J ∧
      ∀ δ,A δ=∫ ω,
        inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ ω))
          (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω)+
        inner ℝ (gradient (hamiltonianCoefficient I)
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T s δ ω) ∂P := by
  exact mixed_expectation_hasFDerivAt I
    (stateClass_hasFDerivAt_disorder D₀ β R hR J x T t)
    (stateClass_hasFDerivAt_disorder D₀ β R hR J x T s)
    (fun K => stateClass_onSphere hN D₀ β R hR hNR K x hx T t ht)
    (fun K => stateClass_onSphere hN D₀ β R hR hNR K x hx T s hs)

end SphericalAging.MixedHamiltonianObservableDerivative
