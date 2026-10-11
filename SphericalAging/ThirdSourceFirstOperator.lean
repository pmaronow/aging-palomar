module

public import SphericalAging.ThirdVariationalLinearity

public section

/-! The literal third source is a true continuous linear map of its
first direction. This operator is constructed from proved linearity. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdSourceFirstOperator
open HardSphereDynamics
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Source
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls L M : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hL : LipschitzWith L (fderiv ℝ g))
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (u v : State N)

@[expose] def firstLinearMap : State N→ₗ[ℝ] PredictableProcessL2 F P where
  toFun := fun a => ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a u v
  map_add' a c := ThirdVariationalLinearity.source_add_first D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a c u v
  map_smul' c a := ThirdVariationalLinearity.source_smul_first D hbg hsg hb hs hbd hsd hnull x T g hg hL hM c a u v

@[expose] def firstOperator : State N→L[ℝ] PredictableProcessL2 F P :=
  (firstLinearMap D hbg hsg hb hs hbd hsd hnull x T g hg hL hM u v).toContinuousLinearMap

@[simp] theorem firstOperator_apply (a : State N) :
    firstOperator D hbg hsg hb hs hbd hsd hnull x T g hg hL hM u v a=
      ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a u v := rfl
end Source
end SphericalAging.ThirdSourceFirstOperator
