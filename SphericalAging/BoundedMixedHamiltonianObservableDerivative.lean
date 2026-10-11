module

public import SphericalAging.MixedHamiltonianObservableDerivative

public section

/-! Compact smooth differentiation of a true Hamiltonian coefficient
pairing against a bounded L² vector, which need not lie on the sphere.
The second vector may be a Brownian truncation independent of disorder. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.BoundedMixedHamiltonianObservableDerivative
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  MixedHamiltonianObservableDerivative HamiltonianDisorderTerminalDerivative
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

@[expose] def boundedMixedRadius (N : ℕ) (K : ℝ≥0) : ℝ := ‖joinState N‖*(Real.sqrt N+K)+1

lemma boundedMixedRadius_pos (N : ℕ) (K : ℝ≥0) : 0<boundedMixedRadius N K := by
  unfold boundedMixedRadius
  positivity

@[expose] def boundedMixedCutoff (I : TensorIndex N p) (K : ℝ≥0) (z : State (N+N)) : ℝ :=
  coefficientBump (N := N+N) (boundedMixedRadius N K) (boundedMixedRadius_pos N K) z*
    mixedPolynomial I z

lemma boundedMixedCutoff_contDiff (I : TensorIndex N p) (K : ℝ≥0) :
    ContDiff ℝ (⊤ : ℕ∞) (boundedMixedCutoff I K) :=
  (coefficientBump (N := N+N) (boundedMixedRadius N K) (boundedMixedRadius_pos N K)).contDiff.mul
    (mixedPolynomial_contDiff I)

lemma boundedMixedCutoff_hasCompactSupport (I : TensorIndex N p) (K : ℝ≥0) :
    HasCompactSupport (boundedMixedCutoff I K) :=
  (coefficientBump (N := N+N) (boundedMixedRadius N K) (boundedMixedRadius_pos N K)).hasCompactSupport.mul_right

lemma boundedMixedCutoff_eventuallyEq (I : TensorIndex N p) (K : ℝ≥0) (x y : State N)
    (hx : OnSphere x) (hy : ‖y‖≤K) :
    boundedMixedCutoff I K=ᶠ[𝓝 (joinState N (x,y))] mixedPolynomial I := by
  have hp : ‖(x,y)‖≤Real.sqrt N+K := by
    rw [Prod.norm_def,FiniteCorrelationIto.sphere_norm hx]
    exact max_le (le_add_of_nonneg_right K.2) (hy.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _)))
  have hnorm : ‖joinState N (x,y)‖<boundedMixedRadius N K := by
    have hb := ((joinState N).le_opNorm (x,y)).trans
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
    unfold boundedMixedRadius
    linarith
  have hm : joinState N (x,y)∈Metric.ball (0 : State (N+N))
      (coefficientBump (N := N+N) (boundedMixedRadius N K) (boundedMixedRadius_pos N K)).rIn := by
    simpa only [coefficientBump,Metric.mem_ball,dist_zero_right] using hnorm
  exact ((coefficientBump (N := N+N) (boundedMixedRadius N K) (boundedMixedRadius_pos N K)).eventuallyEq_one_of_mem_ball hm).mono
    (fun z hz => by simp only [boundedMixedCutoff,hz,Pi.one_apply,one_mul])

lemma boundedMixedCutoff_bounds (I : TensorIndex N p) (K : ℝ≥0) :
    ∃ C A L : ℝ≥0,(∀ z,‖boundedMixedCutoff I K z‖≤C) ∧
      (∀ z,‖fderiv ℝ (boundedMixedCutoff I K) z‖≤A) ∧
      LipschitzWith L (fderiv ℝ (boundedMixedCutoff I K)) := by
  have hg := boundedMixedCutoff_contDiff I K
  have hs := boundedMixedCutoff_hasCompactSupport I K
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hg.continuous
  obtain ⟨A,hA⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv (by simp))
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ)
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (by simp)
  exact ⟨⟨max C 0,le_max_right _ _⟩,⟨max A 0,le_max_right _ _⟩,L,
    (fun z => (hC z).trans (le_max_left _ _)),(fun z => (hA z).trans (le_max_left _ _)),hL⟩

 theorem bounded_mixed_expectation_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : TensorIndex N p) (K : ℝ≥0) {X Y : E → Lp (State N) 2 P}
    {DX DY : E →L[ℝ] Lp (State N) 2 P} {e : E}
    (hX : HasFDerivAt X DX e) (hY : HasFDerivAt Y DY e)
    (hXs : ∀ a,∀ᵐ ω ∂P,OnSphere (X a ω)) (hYs : ∀ a,∀ᵐ ω ∂P,‖Y a ω‖≤K) :
    ∃ A : E →L[ℝ] ℝ,
      HasFDerivAt (fun a => ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X a ω)) (Y a ω) ∂P) A e ∧
      ∀ v,A v=∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (X e ω) (DX v ω)) (Y e ω)+
        inner ℝ (gradient (hamiltonianCoefficient I) (X e ω)) (DY v ω) ∂P := by
  let Z := fun a => pairClassOperator N P (X a,Y a)
  let DZ := (pairClassOperator N P).comp (DX.prod DY)
  have hZ : HasFDerivAt Z DZ e := (pairClassOperator N P).hasFDerivAt.comp e (hX.prodMk hY)
  obtain ⟨C,A,L,hC,hA,hL⟩ := boundedMixedCutoff_bounds I K
  let B := (observableDerivative (boundedMixedCutoff I K) (boundedMixedCutoff_contDiff I K) A hA (Z e)).comp DZ
  have hd := observable_family_hasFDerivAt (boundedMixedCutoff I K) (boundedMixedCutoff_contDiff I K) C A L hC hA hL hZ
  have he : (fun a => ∫ ω,boundedMixedCutoff I K (Z a ω) ∂P)=
      (fun a => ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X a ω)) (Y a ω) ∂P) := by
    funext a
    apply integral_congr_ae
    filter_upwards [pairClassOperator_ae (X a) (Y a),hXs a,hYs a] with ω hz hx hy
    rw [hz,(boundedMixedCutoff_eventuallyEq I K _ _ hx hy).eq_of_nhds]
    simp only [mixedPolynomial,firstState_joinState,secondState_joinState]
  refine ⟨B,by simpa only [he] using hd,?_⟩
  intro v
  change observableDerivative (boundedMixedCutoff I K) (boundedMixedCutoff_contDiff I K) A hA (Z e) (DZ v)=_
  rw [observableDerivative_apply]
  apply integral_congr_ae
  filter_upwards [pairClassOperator_ae (X e) (Y e),pairClassOperator_ae (DX v) (DY v),hXs e,hYs e] with ω hz hv hx hy
  change fderiv ℝ (boundedMixedCutoff I K) (Z e ω) ((pairClassOperator N P (DX v,DY v)) ω)=_
  rw [hz,hv,(boundedMixedCutoff_eventuallyEq I K _ _ hx hy).fderiv_eq,mixedPolynomial_fderiv_apply]

end SphericalAging.BoundedMixedHamiltonianObservableDerivative
