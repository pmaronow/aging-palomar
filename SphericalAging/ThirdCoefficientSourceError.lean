module

public import SphericalAging.SecondResponseDifferenceLpBounds
public import SphericalAging.HessianThirdSourceLittleO
public import SphericalAging.FiniteLpBasisMultiplier

public section

/-! The literal coefficient variation forcing at the actual second
response. The third response derivative contribution is subtracted
explicitly, retaining its genuine mixed Hessian source. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdCoefficientSourceError
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open StochasticFlowDerivative PredictableLinearCoefficient SecondVariationSourceError
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls K L M : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x y : State N) (T : ℝ≥0) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g)) (u v : State N)

@[expose] def sourceError : PredictableProcessL2 F P :=
  apply (row D hb hs T g hg hK y)
      (SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull y T u v)-
    apply (row D hb hs T g hg hK x)
      (SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull y T u v)-
    ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v (y-x)

theorem sourceError_bound (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) :
    ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖(sourceError D hbg hsg hb hs hbd hsd hnull x y T g hg hK hL u v : TimeProcessL2 P) q‖≤
      (M:ℝ)*‖stateTimeCut (increment D hb hs x y T) T q‖^2*
        ‖stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T q‖+
      (L:ℝ)*‖FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T q‖*
        ‖stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T q‖+
      (L:ℝ)*‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
        ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖ := by
  let U := SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull y T u v
  let A := apply (row D hb hs T g hg hK y) U
  let B := apply (row D hb hs T g hg hK x) U
  let C := ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v (y-x)
  have hY := SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull y T u v
  rw [stateTimeCut_eq_indicator] at hY
  filter_upwards [Lp.coeFn_sub ((A-B : PredictableProcessL2 F P) : TimeProcessL2 P) C,
    Lp.coeFn_sub (A : TimeProcessL2 P) B,
    LinearVariationalSDE.apply_eq_actual hY (row D hb hs T g hg hK y),
    LinearVariationalSDE.apply_eq_actual hY (row D hb hs T g hg hK x),
    ThirdVariationalSources.mixedSource_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL u v (y-x)]
    with q hsub hsub' hy hx hc
  change ‖((A-B-C : PredictableProcessL2 F P) : TimeProcessL2 P) q‖≤_
  simp only [Submodule.coe_sub] at hsub ⊢
  rw [hsub,Pi.sub_apply,hsub',Pi.sub_apply,hy,hx,hc]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simp only [row,VariationalCoefficients.derivativeRow,FourPapersCommon.continuousAdaptedTimeCut,
      stateTimeCut,increment,FlowLinearizationLpBounds.remainderCut,
      SecondResponseDifferenceLpBounds.differenceCut,ThirdVariationalSources.mixedField,
      HessianQuadraticSource.hessianField,ht,ite_true]
    rw [((hg.contDiffAt (x:=GlobalSDE.horizonProcess D hb hs x T q.1 q.2)).isSymmSndFDerivAt
      (by simp)).eq
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x) q.1 q.2)]
    rw [←ContinuousLinearMap.sub_apply]
    exact SecondVariationPointwiseError.jacobian_variation_error_bound hg hL hM _ _ _ _ _
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,
      FlowLinearizationLpBounds.remainderCut,SecondResponseDifferenceLpBounds.differenceCut,
      ht,ite_false,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero,le_refl]
end Flow
end SphericalAging.ThirdCoefficientSourceError
