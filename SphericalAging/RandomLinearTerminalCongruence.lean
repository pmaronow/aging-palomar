module

public import SphericalAging.RandomLinearCoefficientCongruence
public import SphericalAging.RandomLinearTerminalOperations

public section

/-! Terminal values of actual random-initial linear SDEs are invariant
under genuine product-almost-everywhere coefficient equality. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RandomLinearTerminalCongruence
open HardSphereDynamics LocalSDE PredictableLinearCoefficient RandomLinearVariationalSDE
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks Kb' Ks' : ℝ≥0}

theorem terminalClass_coefficients_congr (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (a' : Fin N → Coefficient (N := N) (F := F) (P := P) Kb')
    (sigma' : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks')
    (ha : ∀ i,(a i).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (a' i).value)
    (hsigma : ∀ i j,(sigma i j).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (sigma' i j).value)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T t : ℝ≥0) (ht : t≤T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    terminalClass D a sigma Z0 hZ0 hmem T t=terminalClass D a' sigma' Z0 hZ0 hmem T t := by
  have hX := process_strongSolution D a sigma Z0 hZ0 hmem T
  have hX' := RandomLinearCoefficientCongruence.strongSolution_congr_coefficients
    a sigma a' sigma' ha hsigma D Z0 (process D a sigma Z0 hZ0 hmem T) T hX
  have hY := process_strongSolution D a' sigma' Z0 hZ0 hmem T
  have he := pathwise_uniqueness hX' hY hnull
  apply Lp.ext
  filter_upwards [terminalClass_ae D a sigma Z0 hZ0 hmem T t,
    terminalClass_ae D a' sigma' Z0 hZ0 hmem T t,he] with omega hX hY he
  rw [hX,hY]
  exact he t ht

end SphericalAging.RandomLinearTerminalCongruence
