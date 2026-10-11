module

public import SphericalAging.HamiltonianEnergySteinActual
public import SphericalAging.AnnealedGlobalSDE

public section

/-! Genuine Gaussian energy identity for the literal annealed physical
process, including its independent normalized surface initial point.
The left side is the actual product-law energy expectation. The right
side uses the proved actual tensor-disorder terminal Jacobian. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedHamiltonianEnergyStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
open HamiltonianDisorderTerminalDerivative HamiltonianEnergySteinActual
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The actual integral-constructed all-time annealed process, with the
literal independent Gaussian tensor and normalized surface initial law. -/
@[expose] def process (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) :
    ℝ≥0 → (AnnealedCutoffProcess.Parameter N p × Ω) → State N :=
  AnnealedGlobalSDE.globalProcess (NullAugmentation.driver D₀) β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p)

/-- The actual annealed process agrees in each parameter section with the
true terminal state class on every fixed physical horizon. -/
lemma process_sections (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (T t : ℝ≥0) (ht : t ≤ T) :
    ∀ᵐ q ∂AnnealedModelLaw.parameterLaw N p, ∀ᵐ omega ∂P,
      process D₀ β R hR t (q,omega) =
        (stateClass (NullAugmentation.driver D₀) β R hR q.1 q.2 T t) omega := by
  let D := NullAugmentation.driver D₀
  let hJ := AnnealedModelLaw.parameter_disorder_memLp N p
  have hg := Measure.ae_ae_of_ae_prod (AnnealedGlobalSDE.globalProcess_eq_horizon D β R hR hJ T)
  have hf := AnnealedCutoffProcess.process_slice_allTimes D β R hR hJ T
  filter_upwards [hg,hf] with q hg hf
  filter_upwards [hg,hf,stateClass_ae D β R hR q.1 q.2 T t] with omega hg hf hs
  exact (hg t ht).trans ((hf t).trans hs.symm)

/-- Actual full-law Hamiltonian energy is integrable, derived coefficient
by coefficient from genuine Gaussian L² and sphere support. -/
theorem energy_integrable (hN : 0 < N) (hp : 0 < p) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2) (t : ℝ≥0) :
    Integrable (fun omega => Hamiltonian N p omega.1.1 (process D₀ β R hR t omega))
      ((AnnealedModelLaw.parameterLaw N p).prod P) := by
  let D := NullAugmentation.driver D₀
  let hJ := AnnealedModelLaw.parameter_disorder_memLp N p
  have hm := (AnnealedGlobalSDE.globalProcess_stronglyAdapted D β R hR hJ t).mono
    ((IndependentBackgroundDriver.filtration (AnnealedCutoffProcess.Parameter N p)
      (NullAugmentation.augment F P)).le t)
  have hs := (AnnealedGlobalSDE.globalProcess_physical (Nat.ne_of_gt hN) D₀ β R hR hNR hJ
    (AnnealedModelLaw.parameter_initial_onSphere hN p)).2
  have hsq : ∀ᵐ omega ∂(AnnealedModelLaw.parameterLaw N p).prod P,
      ‖process D₀ β R hR t omega‖^2 = (N : ℝ) :=
    hs.mono (fun omega homega => (onSphere_iff_norm_sq _).mp (homega t))
  have hi : ∀ I : TensorIndex N p, Integrable (fun omega => omega.1.1 I *
      hamiltonianCoefficient I (process D₀ β R hR t omega))
        ((AnnealedModelLaw.parameterLaw N p).prod P) := by
    intro I
    have hcoord := ((coordinate_memLp N p I).comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst P
    have hcoeff := HamiltonianCoefficientBounds.coefficient_memLp_of_sphere hN hp I
      (process D₀ β R hR t) hm.aestronglyMeasurable hsq
    exact memLp_one_iff_integrable.mp (hcoord.mul hcoeff)
  have hall := integrable_finsetSum Finset.univ (fun I _ => hi I)
  convert hall using 1
  funext omega
  exact hamiltonian_eq_sum_coefficients _ _

/-- Exact actual annealed energy equals the normalized-surface average of
the genuine coefficient-gradient / disorder-Jacobian Stein expression.
No derivative or growth premise is supplied. -/
theorem actual_energy_stein (hN : 0 < N) (hp : 0 < p) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (T t : ℝ≥0) (ht : t ≤ T) :
    (∫ omega, Hamiltonian N p omega.1.1 (process D₀ β R hR t omega)
      ∂(AnnealedModelLaw.parameterLaw N p).prod P) =
      ∫ x : State N,
        (∑ I : TensorIndex N p, ∫ J : Disorder N p, ∫ omega,
          inner ℝ (gradient (hamiltonianCoefficient I)
            ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) omega))
            ((stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)) omega)
              ∂P ∂disorderLaw N p) ∂SphereInitialLaw.sphereLaw N := by
  have hi := energy_integrable hN hp D₀ β R hR hNR t
  have he : (fun q : AnnealedCutoffProcess.Parameter N p => ∫ omega,
      Hamiltonian N p q.1 (process D₀ β R hR t (q,omega)) ∂P) =ᵐ[AnnealedModelLaw.parameterLaw N p]
      (fun q => ∫ omega,Hamiltonian N p q.1
        ((stateClass (NullAugmentation.driver D₀) β R hR q.1 q.2 T t) omega) ∂P) := by
    filter_upwards [process_sections D₀ β R hR T t ht] with q hq
    exact integral_congr_ae (hq.mono (fun omega homega => congrArg (Hamiltonian N p q.1) homega))
  have hinner : Integrable (fun q : AnnealedCutoffProcess.Parameter N p => ∫ omega,
      Hamiltonian N p q.1 ((stateClass (NullAugmentation.driver D₀) β R hR q.1 q.2 T t) omega) ∂P)
        (AnnealedModelLaw.parameterLaw N p) := hi.integral_prod_left.congr he
  rw [integral_prod _ hi,integral_congr_ae he]
  change (∫ q : Disorder N p × State N, ∫ omega,
      Hamiltonian N p q.1 ((stateClass (NullAugmentation.driver D₀) β R hR q.1 q.2 T t) omega) ∂P
        ∂(disorderLaw N p).prod (SphereInitialLaw.sphereLaw N)) = _
  rw [integral_prod_symm _ hinner]
  apply integral_congr_ae
  filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
  exact hamiltonian_energy_stein_actual hN hp D₀ β R hR hNR x
    ((onSphere_iff_norm_sq x).mpr hx) T t ht

lemma modelRadius_pos (N : ℕ) : 0 < ((N+1 : ℝ≥0) : ℝ) := by
  simp only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  positivity

lemma modelRadius_sq (N : ℕ) : (N : ℝ) < ((N+1 : ℝ≥0) : ℝ)^2 := by
  simp only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  nlinarith [Nat.cast_nonneg (α := ℝ) N,sq_nonneg (N : ℝ)]

/-- Actual model process on the independent normalized surface, Gaussian
tensor, and vector Wiener law. Its deterministic compact cutoff is removed
on its proved all-time sphere event. -/
@[expose] def modelProcess (N p : ℕ) (β : ℝ) :
    ℝ≥0 → (AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N) → State N :=
  process (VectorBrownian.driver N) β (N+1) (modelRadius_pos N)

/-- Concrete actual-model energy Stein receipt, with no Brownian driver,
derivative, integrability, growth or SDE premise. -/
theorem actual_model_energy_stein {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (β : ℝ) (T t : ℝ≥0) (ht : t ≤ T) :
    (∫ omega, Hamiltonian N p omega.1.1 (modelProcess N p β t omega)
      ∂AnnealedModelLaw.law N p) =
      ∫ x : State N,
        (∑ I : TensorIndex N p, ∫ J : Disorder N p, ∫ omega,
          inner ℝ (gradient (hamiltonianCoefficient I)
            ((stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
              (modelRadius_pos N) J x T t) omega))
            ((stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
              (modelRadius_pos N) J x T t (Pi.single I 1)) omega)
              ∂VectorBrownian.law N ∂disorderLaw N p) ∂SphereInitialLaw.sphereLaw N :=
  actual_energy_stein hN hp (VectorBrownian.driver N) β (N+1) (modelRadius_pos N)
    (modelRadius_sq N) T t ht

end SphericalAging.AnnealedHamiltonianEnergyStein
