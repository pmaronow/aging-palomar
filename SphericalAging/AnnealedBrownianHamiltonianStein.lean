module

public import SphericalAging.ActualBrownianCoefficientStein
public import SphericalAging.AnnealedMixedHamiltonianStein

public section

/-! True full-law two-time Hamiltonian-gradient Gaussian Stein formula,
including the actual independent normalized surface initial state and unbounded Brownian direction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedBrownianHamiltonianStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts HamiltonianCoefficientBounds
  HamiltonianDisorderTerminalDerivative HamiltonianParameter AnnealedHamiltonianEnergyStein
  IndependentMixedHamiltonianGaussianStein IndependentMixedCoefficientDerivative
  ActualDisorderGammaVariance BrownianVectorMoments MixedHamiltonianObservableDerivative
  AnnealedMixedHamiltonianStein
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma weighted_brownian_coefficient_integrable (hN : 0 < N) 
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (s t : ℝ≥0) (I : TensorIndex N p) :
    Integrable (fun q : (Disorder N p × State N) × VectorBrownian.Space N => q.1.1 I*
      inner ℝ (gradient (hamiltonianCoefficient I) (process (VectorBrownian.driver N) β R hR t q))
        (brownianVector s q.2)) ((AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N)) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let hJ := AnnealedModelLaw.parameter_disorder_memLp N p
  have hm (u : ℝ≥0) := (AnnealedGlobalSDE.globalProcess_stronglyAdapted D β R hR hJ u).mono
    ((IndependentBackgroundDriver.filtration (AnnealedCutoffProcess.Parameter N p)
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N))).le u)
  have hs := (AnnealedGlobalSDE.globalProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR hJ
    (AnnealedModelLaw.parameter_initial_onSphere hN p)).2
  have hBm : AEStronglyMeasurable (fun q : (Disorder N p × State N) × VectorBrownian.Space N => brownianVector s q.2)
      ((AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N)) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable.comp
      (VectorBrownian.process_measurable N s)).stronglyMeasurable.comp_snd.aestronglyMeasurable
  have hB2 := (brownianVector_memLp (N := N) s (q := 2) (by norm_num)).comp_snd (AnnealedModelLaw.parameterLaw N p)
  have hcoef : MemLp (fun q : (Disorder N p × State N) × VectorBrownian.Space N =>
      inner ℝ (gradient (hamiltonianCoefficient I) (process (VectorBrownian.driver N) β R hR t q))
        (brownianVector s q.2)) 2 ((AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N)) := by
    apply hB2.of_le_mul (c := (p : ℝ)) (((coefficientGradient_contDiff I).continuous.comp_aestronglyMeasurable
      (hm t).aestronglyMeasurable).inner hBm)
    filter_upwards [hs] with q hq
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp (hq t))) (norm_nonneg _))
  have hcoord := ((coordinate_memLp N p I).comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst (VectorBrownian.law N)
  exact memLp_one_iff_integrable.mp (hcoord.mul hcoef)

/-- Actual full-law gradient pairing is integrable before applying Stein. -/
theorem brownian_gradient_pair_integrable (hN : 0 < N) 
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (s t : ℝ≥0) :
    Integrable (fun q : (Disorder N p × State N) × VectorBrownian.Space N =>
      inner ℝ (hamiltonianGradient q.1.1 (process (VectorBrownian.driver N) β R hR t q)) (brownianVector s q.2))
        ((AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N)) := by
  have hi := integrable_finsetSum Finset.univ (fun (I : TensorIndex N p) _ => weighted_brownian_coefficient_integrable
    hN β R hR hNR s t I)
  convert hi using 1
  funext q
  exact gradient_pairing_sum _ _ _

/-- Literal actual annealed mixed-gradient Stein identity. All process
regularity, full-law integrability, sphere support and Gaussian derivative
conditions are conclusions of the constructed physical model. -/
theorem actual_brownian_gradient_pairing_stein (hN : 0 < N) (hp : 0 < p)
     (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) :
    (∫ q : (Disorder N p × State N) × VectorBrownian.Space N,
      inner ℝ (hamiltonianGradient q.1.1 (process (VectorBrownian.driver N) β R hR t q))
        (brownianVector s q.2) ∂(AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N))=
      ∫ x : State N,∑ I : TensorIndex N p,∫ J : Disorder N p,∫ ω,
        inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
          (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω)
          (stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t (Pi.single I 1) ω))
          (brownianVector s ω)
            ∂VectorBrownian.law N ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
  let f := fun I : TensorIndex N p => fun q : (Disorder N p × State N) × VectorBrownian.Space N => q.1.1 I*
    inner ℝ (gradient (hamiltonianCoefficient I) (process (VectorBrownian.driver N) β R hR t q)) (brownianVector s q.2)
  have hfi (I : TensorIndex N p) := weighted_brownian_coefficient_integrable hN β R hR hNR s t I
  have he (I : TensorIndex N p) :
      (fun q : Disorder N p × State N => ∫ ω,f I (q,ω) ∂VectorBrownian.law N)=ᵐ[AnnealedModelLaw.parameterLaw N p]
      (fun q : Disorder N p × State N => q.1 I*(∫ ω,
        inner ℝ (gradient (hamiltonianCoefficient I)
          (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2 T t ω))
          (brownianVector s ω) ∂VectorBrownian.law N)) := by
    filter_upwards [process_sections (VectorBrownian.driver N) β R hR T t ht] with q hqt
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hqt] with ω hqt
    dsimp only [f]
    rw [hqt]
  have hei (I : TensorIndex N p) := (hfi I).integral_prod_left.congr (he I)
  have hswap (I : TensorIndex N p) :
      (∫ q,f I q ∂(AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N))=
        ∫ x : State N,∫ J : Disorder N p,J I*(∫ ω,
          inner ℝ (gradient (hamiltonianCoefficient I)
            (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω))
            (brownianVector s ω) ∂VectorBrownian.law N)
          ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
    rw [integral_prod _ (hfi I),integral_congr_ae (he I)]
    exact integral_prod_symm _ (hei I)
  have hleft : (∫ q : (Disorder N p × State N) × VectorBrownian.Space N,
      inner ℝ (hamiltonianGradient q.1.1 (process (VectorBrownian.driver N) β R hR t q)) (brownianVector s q.2)
        ∂(AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N))=∑ I : TensorIndex N p,
        ∫ q,f I q ∂(AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N) := by
    simp_rw [gradient_pairing_sum]
    exact integral_finsetSum Finset.univ (fun I _ => hfi I)
  rw [hleft]
  simp_rw [hswap]
  have hix (I : TensorIndex N p) : Integrable (fun x : State N => ∫ J : Disorder N p,J I*(∫ ω,
      inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω))
        (brownianVector s ω) ∂VectorBrownian.law N) ∂disorderLaw N p)
      (SphereInitialLaw.sphereLaw N) := by
    simpa only [Function.comp_def,Prod.swap_prod_mk] using (hei I).swap.integral_prod_left
  rw [← integral_finsetSum Finset.univ (fun I _ => hix I)]
  apply integral_congr_ae
  filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
  apply Finset.sum_congr rfl
  intro I _
  have hh := independent_coefficient_gradient_pairing_stein_actual hN hp (VectorBrownian.driver N) β R hR hNR x
    ((onSphere_iff_norm_sq _).mpr hx) T t ht I (brownianClass s)
  have he : (fun J : Disorder N p => J I*coefficientObservable (VectorBrownian.driver N) β R hR x T t I (brownianClass s) J)=
      (fun J => J I*(∫ ω,inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω))
          (brownianVector s ω) ∂VectorBrownian.law N)) := by
    funext J
    congr 1
    apply integral_congr_ae
    filter_upwards [brownianClass_ae (N := N) s] with ω hω
    rw [hω]
  rw [he] at hh
  exact hh.trans (integral_congr_ae (.of_forall (fun J => by
    unfold coefficientResponseObservable
    apply integral_congr_ae
    filter_upwards [brownianClass_ae (N := N) s] with ω hω
    rw [hω])))

end SphericalAging.AnnealedBrownianHamiltonianStein
