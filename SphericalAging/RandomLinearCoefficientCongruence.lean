module

public import SphericalAging.RandomLinearVariationalSDE

public section

/-! Changing bounded predictable linear coefficient representatives on
product-measure null sets preserves the actual strong SDE, including its
real drift integrals at every terminal time. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.RandomLinearCoefficientCongruence
open HardSphereDynamics LocalSDE PredictableLinearCoefficient PredictableDriftTime
set_option maxHeartbeats 1600000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks Kb' Ks' : ℝ≥0}

/-- A true strong solution is independent of product-null changes in the
actual predictable Jacobian coefficient representatives. -/
theorem strongSolution_congr_coefficients
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (a' : Fin N → Coefficient (N := N) (F := F) (P := P) Kb')
    (sigma' : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks')
    (ha : ∀ i,(a i).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (a' i).value)
    (hsigma : ∀ i j,(sigma i j).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (sigma' i j).value)
    (D : BrownianDriver N P F) (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hX : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D Z0 X T) :
    RandomLinearVariationalSDE.IsStrongSolutionOn a' sigma' D Z0 X T := by
  obtain ⟨hXa,hXc,A,U,hA,hU,hEq⟩ := hX
  have hA' : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (a' i).value (s,omega) (X s omega)) T := by
    intro i
    filter_upwards [hA i,ha i] with q hA ha
    rw [hA]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;>
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,ite_false,ha]
  have hU' : ∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (sigma' i j).value (s,omega) (X s omega)) T := by
    intro i j
    filter_upwards [hU i j,hsigma i j] with q hU hs
    rw [hU]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;>
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,ite_false,hs]
  refine ⟨hXa,hXc,A,U,hA',hU',?_⟩
  intro t ht i
  have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun s omega => (a i).value (s,omega) (X s omega)) T (A i) (hA i)
  have hd' := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun s omega => (a' i).value (s,omega) (X s omega)) T (A i) (hA' i)
  filter_upwards [hEq t ht i,hd,hd'] with omega hEq hd hd'
  rw [← hd t ht,hd' t ht] at hEq
  exact hEq

end SphericalAging.RandomLinearCoefficientCongruence
