module

public import SphericalAging.InhomogeneousLinearSDE
public import SphericalAging.VariationalCoefficients

public section

/-! Bound certificates do not alter the actual predictable derivative
values or the actual SDE they define. This lets genuine sharper coefficient
bounds be used for moment estimates without changing the proved process. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.CoefficientRebinding
open HardSphereDynamics PredictableLinearCoefficient
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Ka Kb Ks Kt B : ℝ≥0}

lemma apply_eq_of_values (a : Coefficient (N := N) (F := F) (P := P) Ka)
    (b : Coefficient (N := N) (F := F) (P := P) Kb)
    (hab : ∀ q, a.value q = b.value q) (U : PredictableStateL2 N F P) :
    PredictableLinearCoefficient.apply a U = PredictableLinearCoefficient.apply b U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [apply_coeFn a U,apply_coeFn b U] with q ha hb
  rw [ha,hb,hab q]

/-- True affine strong equations are preserved when only the bound
certificates on their identical actual coefficient values change. -/
theorem affine_strongSolution_congr
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Ka)
    (b : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (tau : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Kt)
    (ha : ∀ i q, (b i).value q = (a i).value q)
    (hs : ∀ i j q, (tau i j).value q = (sigma i j).value q)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (D : BrownianDriver N P F) (v0 : State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hX : InhomogeneousLinearSDE.IsStrongSolutionOn a sigma forcing D v0 X T) :
    InhomogeneousLinearSDE.IsStrongSolutionOn b tau forcing D v0 X T := by
  simpa only [InhomogeneousLinearSDE.IsStrongSolutionOn,ha,hs] using hX

end SphericalAging.CoefficientRebinding
