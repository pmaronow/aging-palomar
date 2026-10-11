module

public import SphericalAging.MixedHamiltonianGaussianStein
public import SphericalAging.AnnealedHamiltonianEnergyStein

public section

/-! True full-law two-time Hamiltonian-gradient Gaussian Stein formula,
including the actual independent normalized surface initial state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedMixedHamiltonianStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts HamiltonianCoefficientBounds
  HamiltonianDisorderTerminalDerivative HamiltonianParameter AnnealedHamiltonianEnergyStein
  MixedHamiltonianGaussianStein MixedHamiltonianObservableDerivative
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma gradient_pairing_sum (J : Disorder N p) (x y : State N) :
    inner ℝ (hamiltonianGradient J x) y=
      ∑ I : TensorIndex N p,J I*inner ℝ (gradient (hamiltonianCoefficient I) x) y := by
  have hg := congrFun (gradient_sum_basis J) x
  simp only [Finset.sum_apply,Pi.smul_apply] at hg
  rw [hg,sum_inner]
  apply Finset.sum_congr rfl
  intro I _
  rw [real_inner_smul_left]
  congr 1
  change inner ℝ (gradient (Hamiltonian N p (basisDisorder I)) x) y=_
  rw [← coefficient_eq_basisHamiltonian]

lemma weighted_coefficient_pair_integrable (hN : 0 < N) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (s t : ℝ≥0) (I : TensorIndex N p) :
    Integrable (fun q : (Disorder N p × State N) × Ω => q.1.1 I*
      inner ℝ (gradient (hamiltonianCoefficient I) (process D₀ β R hR t q))
        (process D₀ β R hR s q)) ((AnnealedModelLaw.parameterLaw N p).prod P) := by
  let D := NullAugmentation.driver D₀
  let hJ := AnnealedModelLaw.parameter_disorder_memLp N p
  have hm (u : ℝ≥0) := (AnnealedGlobalSDE.globalProcess_stronglyAdapted D β R hR hJ u).mono
    ((IndependentBackgroundDriver.filtration (AnnealedCutoffProcess.Parameter N p)
      (NullAugmentation.augment F P)).le u)
  have hs := (AnnealedGlobalSDE.globalProcess_physical (Nat.ne_of_gt hN) D₀ β R hR hNR hJ
    (AnnealedModelLaw.parameter_initial_onSphere hN p)).2
  have hcoef : MemLp (fun q : (Disorder N p × State N) × Ω =>
      inner ℝ (gradient (hamiltonianCoefficient I) (process D₀ β R hR t q))
        (process D₀ β R hR s q)) 2 ((AnnealedModelLaw.parameterLaw N p).prod P) := by
    apply MemLp.of_bound (((coefficientGradient_contDiff I).continuous.comp_aestronglyMeasurable
      (hm t).aestronglyMeasurable).inner (hm s).aestronglyMeasurable) ((p : ℝ)*Real.sqrt N)
    filter_upwards [hs] with q hq
    calc
      _ ≤ ‖gradient (hamiltonianCoefficient I) (process D₀ β R hR t q)‖*
          ‖process D₀ β R hR s q‖ := norm_inner_le_norm _ _
      _ ≤ (p : ℝ)*Real.sqrt N := by
        have hn : ‖process D₀ β R hR s q‖=Real.sqrt N :=
          FiniteCorrelationIto.sphere_norm (show OnSphere (process D₀ β R hR s q) from hq s)
        rw [hn]
        exact mul_le_mul_of_nonneg_right
          (coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp (hq t)))
          (Real.sqrt_nonneg _)
  have hcoord := ((coordinate_memLp N p I).comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst P
  exact memLp_one_iff_integrable.mp (hcoord.mul hcoef)

/-- Actual full-law gradient pairing is integrable before applying Stein. -/
theorem gradient_pair_integrable (hN : 0 < N) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (s t : ℝ≥0) :
    Integrable (fun q : (Disorder N p × State N) × Ω =>
      inner ℝ (hamiltonianGradient q.1.1 (process D₀ β R hR t q)) (process D₀ β R hR s q))
        ((AnnealedModelLaw.parameterLaw N p).prod P) := by
  have hi := integrable_finsetSum Finset.univ (fun (I : TensorIndex N p) _ => weighted_coefficient_pair_integrable
    hN D₀ β R hR hNR s t I)
  convert hi using 1
  funext q
  exact gradient_pairing_sum _ _ _

/-- Literal actual annealed mixed-gradient Stein identity. All process
regularity, full-law integrability, sphere support and Gaussian derivative
conditions are conclusions of the constructed physical model. -/
theorem actual_gradient_pairing_stein (hN : 0 < N) (hp : 0 < p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) :
    (∫ q : (Disorder N p × State N) × Ω,
      inner ℝ (hamiltonianGradient q.1.1 (process D₀ β R hR t q))
        (process D₀ β R hR s q) ∂(AnnealedModelLaw.parameterLaw N p).prod P)=
      ∫ x : State N,∑ I : TensorIndex N p,∫ J : Disorder N p,∫ ω,
        inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1) ω))
          (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω)+
        inner ℝ (gradient (hamiltonianCoefficient I)
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T s (Pi.single I 1) ω)
            ∂P ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
  let f := fun I : TensorIndex N p => fun q : (Disorder N p × State N) × Ω => q.1.1 I*
    inner ℝ (gradient (hamiltonianCoefficient I) (process D₀ β R hR t q)) (process D₀ β R hR s q)
  have hfi (I : TensorIndex N p) := weighted_coefficient_pair_integrable hN D₀ β R hR hNR s t I
  have he (I : TensorIndex N p) :
      (fun q : Disorder N p × State N => ∫ ω,f I (q,ω) ∂P)=ᵐ[AnnealedModelLaw.parameterLaw N p]
      (fun q : Disorder N p × State N => q.1 I*(∫ ω,
        inner ℝ (gradient (hamiltonianCoefficient I)
          (stateClass (NullAugmentation.driver D₀) β R hR q.1 q.2 T t ω))
          (stateClass (NullAugmentation.driver D₀) β R hR q.1 q.2 T s ω) ∂P)) := by
    filter_upwards [process_sections D₀ β R hR T t ht,process_sections D₀ β R hR T s hs] with q hqt hqs
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hqt,hqs] with ω hqt hqs
    dsimp only [f]
    rw [hqt,hqs]
  have hei (I : TensorIndex N p) := (hfi I).integral_prod_left.congr (he I)
  have hswap (I : TensorIndex N p) :
      (∫ q,f I q ∂(AnnealedModelLaw.parameterLaw N p).prod P)=
        ∫ x : State N,∫ J : Disorder N p,J I*(∫ ω,
          inner ℝ (gradient (hamiltonianCoefficient I)
            (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
            (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω) ∂P)
          ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
    rw [integral_prod _ (hfi I),integral_congr_ae (he I)]
    exact integral_prod_symm _ (hei I)
  have hleft : (∫ q : (Disorder N p × State N) × Ω,
      inner ℝ (hamiltonianGradient q.1.1 (process D₀ β R hR t q)) (process D₀ β R hR s q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)=∑ I : TensorIndex N p,
        ∫ q,f I q ∂(AnnealedModelLaw.parameterLaw N p).prod P := by
    simp_rw [gradient_pairing_sum]
    exact integral_finsetSum Finset.univ (fun I _ => hfi I)
  rw [hleft]
  simp_rw [hswap]
  have hix (I : TensorIndex N p) : Integrable (fun x : State N => ∫ J : Disorder N p,J I*(∫ ω,
      inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
        (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω) ∂P) ∂disorderLaw N p)
      (SphereInitialLaw.sphereLaw N) := by
    simpa only [Function.comp_def,Prod.swap_prod_mk] using (hei I).swap.integral_prod_left
  rw [← integral_finsetSum Finset.univ (fun I _ => hix I)]
  apply integral_congr_ae
  filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
  apply Finset.sum_congr rfl
  intro I _
  exact coefficient_gradient_pairing_stein_actual hN hp D₀ β R hR hNR x
    ((onSphere_iff_norm_sq _).mpr hx) T s t hs ht I

end SphericalAging.AnnealedMixedHamiltonianStein
