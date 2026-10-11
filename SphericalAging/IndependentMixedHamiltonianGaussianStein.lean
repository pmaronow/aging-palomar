module

public import SphericalAging.IndependentMixedCoefficientDerivative

public section

/-! Genuine disorder Gaussian Stein against any independent vector L²
class. Bounded Brownian truncations converge by Cauchy–Schwarz and
Bochner dominated convergence; no unbounded observable derivative is an
assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.IndependentMixedHamiltonianGaussianStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  BoundedMixedHamiltonianGaussianStein IndependentMixedCoefficientDerivative
  HamiltonianDisorderTerminalDerivative HamiltonianCoefficientL2Classes
  BoundedStateL2Approximation HamiltonianDisorderResponseGrowth HamiltonianPredictableForcing
  DisorderExponentialIntegrability HamiltonianEnergySteinActual
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma coefficientObservable_trunc_tendsto (hN : 0<N)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (Y : Lp (State N) 2 P) (J : Disorder N p) :
    Tendsto (fun n : ℕ => coefficientObservable D₀ β R hR x T t I (truncClass n Y) J) atTop
      (𝓝 (coefficientObservable D₀ β R hR x T t I Y J)) := by
  let X := stateClass (NullAugmentation.driver D₀) β R hR J x T t
  have hX := stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht
  have h := truncClass_pairing_tendsto (coefficientGradientClass hN I X hX) Y
  simpa only [← L2.inner_def (𝕜 := ℝ),coefficientGradientClass_pairing,coefficientObservable,X] using h

lemma coefficientResponseObservable_trunc_tendsto (hN : N≠0)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (Y : Lp (State N) 2 P) (J : Disorder N p) :
    Tendsto (fun n : ℕ => coefficientResponseObservable D₀ β R hR x T t I (truncClass n Y) J) atTop
      (𝓝 (coefficientResponseObservable D₀ β R hR x T t I Y J)) := by
  let X := stateClass (NullAugmentation.driver D₀) β R hR J x T t
  let V := stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)
  have hX := stateClass_onSphere hN D₀ β R hR hNR J x hx T t ht
  have h := truncClass_pairing_tendsto (hessianClass I X V hX) Y
  simpa only [← L2.inner_def (𝕜 := ℝ),hessianClass_pairing,coefficientResponseObservable,X,V] using h

 theorem independent_coefficient_observables_measurable (hN : 0<N)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (Y : Lp (State N) 2 P) :
    StronglyMeasurable (coefficientObservable D₀ β R hR x T t I Y) ∧
      StronglyMeasurable (coefficientResponseObservable D₀ β R hR x T t I Y) := by
  have hm (n : ℕ) := bounded_independent_coefficient_measurable (Nat.ne_of_gt hN)
    D₀ β R hR hNR x hx T t ht I n (truncClass n Y) (truncClass_ae_bound n Y)
  exact ⟨stronglyMeasurable_of_tendsto atTop (fun n => (hm n).1)
      (tendsto_pi_nhds.mpr (coefficientObservable_trunc_tendsto hN D₀ β R hR hNR x hx T t ht I Y)),
    stronglyMeasurable_of_tendsto atTop (fun n => (hm n).2)
      (tendsto_pi_nhds.mpr (coefficientResponseObservable_trunc_tendsto (Nat.ne_of_gt hN) D₀ β R hR hNR x hx T t ht I Y))⟩

 theorem independent_coefficient_gradient_pairing_stein_actual (hN : 0<N) (hp : 0<p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (Y : Lp (State N) 2 P) :
    (∫ J : Disorder N p,J I*coefficientObservable D₀ β R hR x T t I Y J ∂disorderLaw N p)=
      ∫ J : Disorder N p,coefficientResponseObservable D₀ β R hR x T t I Y J ∂disorderLaw N p := by
  let B := fun J : Disorder N p => (disorderConstant (N := N) (p := p) β R hR : ℝ)*
    Real.exp (exponentBase (N := N) (p := p) β R hR t/2+
      ((exponentSlope (N := N) (p := p) β R hR t/2 : ℝ≥0) : ℝ)*‖J‖)
  have hBi : Integrable B (disorderLaw N p) :=
    (disorder_affine_exp_integrable hN hp
      (exponentBase (N := N) (p := p) β R hR t/2)
      (exponentSlope (N := N) (p := p) β R hR t/2)).const_mul _
  have hm (n : ℕ) := independent_coefficient_observables_measurable hN D₀ β R hR hNR x hx T t ht I (truncClass n Y)
  have hLbound : Integrable (fun J : Disorder N p => |J I| *((p : ℝ)*‖Y‖)) (disorderLaw N p) := by
    simpa only [Real.norm_eq_abs] using
      ((coordinate_memLp N p I).integrable (by norm_num)).norm.mul_const ((p : ℝ)*‖Y‖)
  have hLb (n : ℕ) (J : Disorder N p) :
      ‖J I*coefficientObservable D₀ β R hR x T t I (truncClass n Y) J‖≤|J I| *((p : ℝ)*‖Y‖) := by
    let X := stateClass (NullAugmentation.driver D₀) β R hR J x T t
    have hX := stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht
    have he := coefficientGradientClass_pairing hN I X (truncClass n Y) hX
    change ‖J I*(∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (truncClass n Y ω) ∂P)‖≤_
    rw [← he,norm_mul,Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans ?_) (abs_nonneg _)
    exact mul_le_mul (coefficientGradientClass_norm_le hN I X hX) (truncClass_norm_le n Y)
      (norm_nonneg _) (Nat.cast_nonneg p)
  have hRbound : Integrable (fun J : Disorder N p => (hessianCeiling I : ℝ)*B J*‖Y‖) (disorderLaw N p) :=
    (hBi.const_mul (hessianCeiling I : ℝ)).mul_const ‖Y‖
  have hRb (n : ℕ) (J : Disorder N p) :
      ‖coefficientResponseObservable D₀ β R hR x T t I (truncClass n Y) J‖≤
        (hessianCeiling I : ℝ)*B J*‖Y‖ := by
    let X := stateClass (NullAugmentation.driver D₀) β R hR J x T t
    let V := stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)
    have hX := stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht
    have he := hessianClass_pairing I X V (truncClass n Y) hX
    change ‖∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω) (V ω)) (truncClass n Y ω) ∂P‖≤_
    rw [← he]
    refine (norm_inner_le_norm (𝕜 := ℝ) _ _).trans ?_
    have hv : ‖hessianClass I X V hX‖≤(hessianCeiling I : ℝ)*B J :=
      (hessianClass_norm_le I X V hX).trans (mul_le_mul_of_nonneg_left
        (stateResponse_coordinate_growth D₀ β R hR J x T t ht I) (hessianCeiling I).2)
    exact mul_le_mul hv (truncClass_norm_le n Y) (norm_nonneg _)
      (mul_nonneg (hessianCeiling I).2 (by dsimp [B];positivity))
  have hL := tendsto_integral_of_dominated_convergence (fun J : Disorder N p => |J I| *((p : ℝ)*‖Y‖))
    (fun n => ((continuous_apply I).stronglyMeasurable.mul (hm n).1).aestronglyMeasurable)
    hLbound (fun n => .of_forall (hLb n))
    (.of_forall (fun J => (coefficientObservable_trunc_tendsto hN D₀ β R hR hNR x hx T t ht I Y J).const_mul (J I)))
  have hRlim := tendsto_integral_of_dominated_convergence (fun J : Disorder N p => (hessianCeiling I : ℝ)*B J*‖Y‖)
    (fun n => (hm n).2.aestronglyMeasurable) hRbound (fun n => .of_forall (hRb n))
    (.of_forall (coefficientResponseObservable_trunc_tendsto (Nat.ne_of_gt hN) D₀ β R hR hNR x hx T t ht I Y))
  have he (n : ℕ) := bounded_coefficient_gradient_pairing_stein_actual hN hp D₀ β R hR hNR
    x hx T t ht I n (truncClass n Y) (truncClass_ae_bound n Y)
  exact tendsto_nhds_unique hL (hRlim.congr' (.of_forall (fun n => (he n).symm)))

end SphericalAging.IndependentMixedHamiltonianGaussianStein
