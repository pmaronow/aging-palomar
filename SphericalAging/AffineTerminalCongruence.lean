module

public import SphericalAging.AffineVariationalSolution

public section

/-! Actual bounded affine response classes and terminal values depend
only on their genuine coefficient and forcing classes. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.AffineTerminalCongruence
open HardSphereDynamics LocalSDE PredictableLinearCoefficient LinearVariationalSDE
open TerminalStateRepresentation AffineVariationalSolution
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks Kb' Ks' B B' : ℝ≥0}

lemma coefficient_apply_congr {K K' : ℝ≥0}
    (a : Coefficient (N := N) (F := F) (P := P) K)
    (a' : Coefficient (N := N) (F := F) (P := P) K')
    (ha : a.value=ᵐ[nonnegativeLebesgueMeasure.prod P] a'.value) (Q : PredictableStateL2 N F P) :
    PredictableLinearCoefficient.apply a Q=PredictableLinearCoefficient.apply a' Q := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [apply_coeFn a Q,apply_coeFn a' Q,ha] with q h1 h2 ha
  rw [h1,h2,ha]

lemma forcingClass_congr
    (f : InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (f' : InhomogeneousLinearSDE.Forcing (F := F) (P := P) B') (T : ℝ≥0)
    (he : FourPapersCommon.continuousAdaptedTimeCut (fun s omega => f.value (s,omega)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s omega => f'.value (s,omega)) T) :
    forcingClass f T=forcingClass f' T := by
  apply Subtype.ext
  apply Lp.ext
  exact (forcingClass_coe f T).trans (he.trans (forcingClass_coe f' T).symm)

section Congruence
variable (D : BrownianDriver N P F)
  (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
  (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
  (a' : Fin N → Coefficient (N := N) (F := F) (P := P) Kb')
  (sigma' : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks')
  (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
  (forcing' : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B') (T : ℝ≥0)
  (ha : ∀ i,(a i).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (a' i).value)
  (hsigma : ∀ i j,(sigma i j).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (sigma' i j).value)
  (hf : ∀ i,FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (forcing i).value (s,omega)) T
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (forcing' i).value (s,omega)) T)

include ha hsigma hf in
theorem responseClass_congr :
    AffineVariationalSolution.responseClass D a sigma forcing T=
      AffineVariationalSolution.responseClass D a' sigma' forcing' T := by
  let S := StochasticLinearizationError.driftSource T (fun i => forcingClass (forcing i) T)
  have hS : S=StochasticLinearizationError.driftSource T (fun i => forcingClass (forcing' i) T) := by
    unfold S
    congr 1
    funext i
    exact forcingClass_congr (forcing i) (forcing' i) T (hf i)
  have hd (Q : PredictableStateL2 N F P) : finiteDriftPicardMap a T Q=finiteDriftPicardMap a' T Q := by
    simp only [finiteDriftPicardMap,driftCoefficientMap]
    exact Finset.sum_congr rfl (fun i _ => congrArg
      (fun A => PredictableItoTime.scalarToStatePredictable i (PredictableDriftTime.driftVolterra T A))
      (coefficient_apply_congr (a i) (a' i) (ha i) Q))
  have hn (Q : PredictableStateL2 N F P) : finiteNoisePicardMap D sigma T Q=finiteNoisePicardMap D sigma' T Q := by
    simp only [finiteNoisePicardMap,stochasticCoefficientMap]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact Finset.sum_congr rfl (fun j _ => congrArg _ (coefficient_apply_congr (sigma i j) (sigma' i j) (hsigma i j) Q))
  have hQ := sourceClass_fixedPoint D a sigma T S
  rw [hd,hn] at hQ
  have he := (exists_unique_picard_fixedPoint D a' sigma' T S).choose_spec.2 _ hQ
  change sourceClass D a sigma T S=sourceClass D a' sigma' T _
  rw [← hS]
  exact he

/-- Literal terminal class of the true affine response. -/
@[expose] def terminal (t : ℝ≥0) : Lp (State N) 2 P :=
  TerminalStateRepresentation.terminalClass D 0
    (fun i => PredictableLinearCoefficient.apply (a i) (AffineVariationalSolution.responseClass D a sigma forcing T)+forcingClass (forcing i) T)
    (fun i j => PredictableLinearCoefficient.apply (sigma i j) (AffineVariationalSolution.responseClass D a sigma forcing T)) T t

include ha hsigma hf in
theorem terminal_congr (t : ℝ≥0) : terminal D a sigma forcing T t=terminal D a' sigma' forcing' T t := by
  have hQ := responseClass_congr D a sigma a' sigma' forcing forcing' T ha hsigma hf
  unfold terminal
  rw [hQ]
  congr 2
  · funext i
    rw [coefficient_apply_congr (a i) (a' i) (ha i),forcingClass_congr (forcing i) (forcing' i) T (hf i)]
  · funext i j
    exact coefficient_apply_congr (sigma i j) (sigma' i j) (hsigma i j) _

end Congruence
end SphericalAging.AffineTerminalCongruence
