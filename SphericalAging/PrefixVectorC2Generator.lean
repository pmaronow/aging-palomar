module

public import SphericalAging.PrefixVectorC2Ito

public section

/-! Product integrability of the genuine C² Itô generator. The derivative
and Hessian weights are evaluated on the actual process; L² diffusion
classes prove every mixed product integrable. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.PrefixVectorC2Generator
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open MultivariateTaylor MultivariateItoWeights MultivariateItoSums SDEWeightedLinear WeightedItoSums
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def derivativeCut (f : State N → ℝ) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) (i : Fin N) :
    ℝ≥0 × Ω → ℝ := FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => fderiv ℝ f (X s ω) (basisVector i)) T

@[expose] def hessianCut (f : State N → ℝ) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) (i k : Fin N) :
    ℝ≥0 × Ω → ℝ := FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => Hessian f (X s ω) (basisVector i) (basisVector k)) T

@[expose] def generator (f : State N → ℝ) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (q : ℝ≥0 × Ω) : ℝ :=
  (∑ i : Fin N,derivativeCut f X T i q*cutRepresentative (A i) T q)+
    (1/2:ℝ)*(∑ i : Fin N,∑ k : Fin N,hessianCut f X T i k q*
      (∑ j : Fin N,(U i j : TimeProcessL2 P) q*(U k j : TimeProcessL2 P) q))

theorem components_integrable {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω)) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (K L : ℝ≥0)
    (hK : ∀ i x,‖fderiv ℝ f x (basisVector i)‖≤K)
    (hL : ∀ i k x,‖Hessian f x (basisVector i) (basisVector k)‖≤L) :
    (∀ i,Integrable (fun q => derivativeCut f X T i q*cutRepresentative (A i) T q)
      (nonnegativeLebesgueMeasure.prod P)) ∧
    (∀ i k,Integrable (fun q => hessianCut f X T i k q*
      (∑ j : Fin N,(U i j : TimeProcessL2 P) q*(U k j : TimeProcessL2 P) q))
      (nonnegativeLebesgueMeasure.prod P)) := by
  have hDa (i : Fin N) : StronglyAdapted F (fun s ω => fderiv ℝ f (X s ω) (basisVector i)) :=
    fun s => (derivative_basis_continuous hf i).comp_stronglyMeasurable (hXa s)
  have hDc (i : Fin N) : ∀ᵐ ω ∂P,Continuous (fun s => fderiv ℝ f (X s ω) (basisVector i)) :=
    hXc.mono (fun _ h => (derivative_basis_continuous hf i).comp h)
  have hHa (i k : Fin N) : StronglyAdapted F
      (fun s ω => Hessian f (X s ω) (basisVector i) (basisVector k)) :=
    fun s => (hessian_basis_continuous hf i k).comp_stronglyMeasurable (hXa s)
  have hHc (i k : Fin N) : ∀ᵐ ω ∂P,Continuous
      (fun s => Hessian f (X s ω) (basisVector i) (basisVector k)) :=
    hXc.mono (fun _ h => (hessian_basis_continuous hf i k).comp h)
  have hDm (i : Fin N) : AEStronglyMeasurable (derivativeCut f X T i)
      (nonnegativeLebesgueMeasure.prod P) :=
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F _ (hDa i) (hDc i) T).mono
      (predictable_le_prod F)
  have hHm (i k : Fin N) : AEStronglyMeasurable (hessianCut f X T i k)
      (nonnegativeLebesgueMeasure.prod P) :=
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F _ (hHa i k) (hHc i k) T).mono
      (predictable_le_prod F)
  have hDi (i : Fin N) : Integrable (fun q => derivativeCut f X T i q*cutRepresentative (A i) T q)
      (nonnegativeLebesgueMeasure.prod P) :=
    (cutRepresentative_integrable (A i) T).bdd_mul (hDm i)
      (.of_forall (timeCut_bound _ K (fun s ω => hK i (X s ω)) T))
  have hHi (i k : Fin N) : Integrable (fun q => hessianCut f X T i k q*
      (∑ j : Fin N,(U i j : TimeProcessL2 P) q*(U k j : TimeProcessL2 P) q))
      (nonnegativeLebesgueMeasure.prod P) := by
    have hUi := integrable_finsetSum Finset.univ (fun j _ =>
      (Lp.memLp (U i j : TimeProcessL2 P)).integrable_mul (Lp.memLp (U k j : TimeProcessL2 P)))
    exact hUi.bdd_mul (hHm i k)
      (.of_forall (timeCut_bound _ L (fun s ω => hL i k (X s ω)) T))
  exact ⟨hDi,hHi⟩

theorem generator_integrable {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω)) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (K L : ℝ≥0)
    (hK : ∀ i x,‖fderiv ℝ f x (basisVector i)‖≤K)
    (hL : ∀ i k x,‖Hessian f x (basisVector i) (basisVector k)‖≤L) :
    Integrable (generator f X T A U) (nonnegativeLebesgueMeasure.prod P) := by
  obtain ⟨hDi,hHi⟩ := components_integrable hf X hXa hXc T A U K L hK hL
  exact (integrable_finsetSum Finset.univ (fun i _ => hDi i)).add
    ((integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun k _ => hHi i k))).const_mul (1/2:ℝ))

theorem generator_zero_outside {f : State N → ℝ} (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (q : ℝ≥0 × Ω) (hq : q.1∉Ioc (0 : ℝ≥0) T) : generator f X T A U q=0 := by
  simp only [generator,derivativeCut,hessianCut,FourPapersCommon.continuousAdaptedTimeCut,hq,
    ite_false,zero_mul,Finset.sum_const_zero,mul_zero,zero_add]

end SphericalAging.PrefixVectorC2Generator
