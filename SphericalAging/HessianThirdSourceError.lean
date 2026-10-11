module

public import SphericalAging.ThirdVariationPointwiseError
public import SphericalAging.FirstResponseRemainderMixed
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public section

/-! Literal third-derivative remainder for the constructed Hessian
forcing. Every field below is part of the genuine same-driver flow. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianThirdSourceError
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls L M : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x y : State N) (T : ℝ≥0) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hL : LipschitzWith L (fderiv ℝ g))
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
  (u v : State N)

@[expose] def sourceError : PredictableProcessL2 F P :=
  HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL u v-
    HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL u v-
    ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL (y-x) u v-
    ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL (y-x) v u-
    ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull x T g hg hM (y-x) u v

include hbg hsg hb hs hbd hsd hnull hg hL hM in
 theorem sourceError_pointwise_bound {A : ℝ≥0}
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g)))) :
    ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖(sourceError D hbg hsg hb hs hbd hsd hnull x y T g hg hL hM u v : TimeProcessL2 P) q‖≤
      (A:ℝ)*‖stateTimeCut (NonlinearIncrementFourthMoment.increment D hb hs x y T) T q‖^2*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T u) T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖+
      (M:ℝ)*‖FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T u) T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖+
      (M:ℝ)*‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
        ‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T u q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖+
      (M:ℝ)*‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T q‖*
        ‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v q‖+
      (L:ℝ)*‖FirstResponseRemainderFourthBound.remainderCut D hbg hsg hb hs hbd hsd hnull x y T u q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T q‖+
      (L:ℝ)*‖FirstResponseRemainderFourthBound.remainderCut D hbg hsg hb hs hbd hsd hnull x y T u q‖*
        ‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v q‖+
      (L:ℝ)*‖stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (y-x) u) T q‖*
        ‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v q‖+
      (L:ℝ)*‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T q‖*
        ‖FirstResponseRemainderFourthBound.remainderCut D hbg hsg hb hs hbd hsd hnull x y T v q‖ := by
  let S₁ := HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL u v
  let S₂ := HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL u v
  let S₃ := ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL (y-x) u v
  let S₄ := ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL (y-x) v u
  let S₅ := ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull x T g hg hM (y-x) u v
  filter_upwards [HessianInitialSource.source_coe D hbg hsg hb hs hnull y T g hg hL u v,
    HessianInitialSource.source_coe D hbg hsg hb hs hnull x T g hg hL u v,
    ThirdVariationalSources.mixedSource_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL (y-x) u v,
    ThirdVariationalSources.mixedSource_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL (y-x) v u,
    ThirdVariationalSources.cubicSource_coe D hbg hsg hb hs hnull x T g hg hM (y-x) u v,
    Lp.coeFn_sub (S₁ : TimeProcessL2 P) S₂,
    Lp.coeFn_sub ((S₁-S₂ : PredictableProcessL2 F P) : TimeProcessL2 P) S₃,
    Lp.coeFn_sub ((S₁-S₂-S₃ : PredictableProcessL2 F P) : TimeProcessL2 P) S₄,
    Lp.coeFn_sub ((S₁-S₂-S₃-S₄ : PredictableProcessL2 F P) : TimeProcessL2 P) S₅]
    with q h₁ h₂ h₃ h₄ h₅ h₁₂ h₁₂₃ h₁₂₃₄ h₁₂₃₄₅
  change ‖((S₁ : TimeProcessL2 P)-(S₂ : TimeProcessL2 P)-(S₃ : TimeProcessL2 P)-
    (S₄ : TimeProcessL2 P)-(S₅ : TimeProcessL2 P)) q‖≤_
  simp only [Submodule.coe_sub] at h₁₂₃ h₁₂₃₄ h₁₂₃₄₅
  rw [h₁₂₃₄₅,Pi.sub_apply,h₁₂₃₄,Pi.sub_apply,h₁₂₃,Pi.sub_apply,h₁₂,Pi.sub_apply,h₁,h₂,h₃,h₄,h₅]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_true,
      FirstVariationDifferenceLpBounds.differenceCut,FirstResponseRemainderFourthBound.remainderCut,
      FlowLinearizationLpBounds.remainderCut,NonlinearIncrementFourthMoment.increment,
      HessianQuadraticSource.hessianField,ThirdVariationalSources.mixedField,
      ThirdVariationalSources.cubicField,CubicVariationalSource.cubicField]
    rw [((hg.contDiffAt (x:=GlobalSDE.horizonProcess D hb hs x T q.1 q.2)).isSymmSndFDerivAt
      (by simp)).eq
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (y-x) v q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs x T u q.1 q.2)]
    have hh := ThirdVariationPointwiseError.hessian_variation_error_bound hg hL hM hA
      (GlobalSDE.horizonProcess D hb hs x T q.1 q.2)
      (GlobalSDE.horizonProcess D hb hs y T q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x) q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs x T u q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs y T u q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs x T v q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs y T v q.1 q.2)
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (y-x) u q.1 q.2)
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (y-x) v q.1 q.2)
    convert hh using 1 <;> ring
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_false,
      FirstVariationDifferenceLpBounds.differenceCut,FirstResponseRemainderFourthBound.remainderCut,
      FlowLinearizationLpBounds.remainderCut,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
      mul_zero,zero_mul,zero_add,le_refl]
end Flow
end SphericalAging.HessianThirdSourceError
