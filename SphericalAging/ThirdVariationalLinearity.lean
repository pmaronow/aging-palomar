module

public import SphericalAging.ThirdVariationalSDE
public import SphericalAging.SecondVariationTimeCutLinearity
public import SphericalAging.FirstVariationLpLift

public section

/-! The constructed actual third response is linear and continuous in
its first initial direction. Its linearity is proved from actual
first- and second-response process cuts. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdVariationalLinearity
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
open StochasticLinearizationError LinearResolvent
set_option maxHeartbeats 2400000
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
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))

theorem source_add_first (a c u v : State N) :
    ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM (a+c) u v=
      ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a u v+
        ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM c u v := by
  let S := fun w => ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM w u v
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [ThirdVariationalSources.source_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL hM (a+c) u v,
    ThirdVariationalSources.source_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a u v,
    ThirdVariationalSources.source_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL hM c u v,
    SecondVariationTimeCutLinearity.timeCut_add_left D hbg hsg hb hs hbd hsd hnull x T a u c,
    SecondVariationTimeCutLinearity.timeCut_add_left D hbg hsg hb hs hbd hsd hnull x T a v c,
    FirstVariationLpLift.timeCut_add D hbg hsg hb hs x T a c,
    Lp.coeFn_add (S a : TimeProcessL2 P) (S c)] with q ha hb' hc hqu hqv hy hs'
  change (S (a+c) : TimeProcessL2 P) q=((S a : TimeProcessL2 P)+(S c : TimeProcessL2 P)) q
  rw [hs',Pi.add_apply,ha,hb',hc]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simp only [stateTimeCut,ht,ite_true] at hqu hqv hy
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
      ThirdVariationalSources.field,ThirdVariationalSources.mixedField,ThirdVariationalSources.cubicField,
      HessianQuadraticSource.hessianField,CubicVariationalSource.cubicField,hqu,hqv,hy,map_add,
      ContinuousLinearMap.add_apply]
    ring
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,zero_add]

theorem source_smul_first (c : ℝ) (a u v : State N) :
    ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM (c • a) u v=
      c • ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a u v := by
  let S := fun w => ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM w u v
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [ThirdVariationalSources.source_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL hM (c • a) u v,
    ThirdVariationalSources.source_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a u v,
    SecondVariationTimeCutLinearity.timeCut_smul_left D hbg hsg hb hs hbd hsd hnull x T c a u,
    SecondVariationTimeCutLinearity.timeCut_smul_left D hbg hsg hb hs hbd hsd hnull x T c a v,
    FirstVariationLpLift.timeCut_smul D hbg hsg hb hs x T c a,
    Lp.coeFn_smul c (S a : TimeProcessL2 P)] with q ha hb' hqu hqv hy hs'
  change (S (c • a) : TimeProcessL2 P) q=(c • (S a : TimeProcessL2 P)) q
  rw [hs',Pi.smul_apply,ha,hb']
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simp only [stateTimeCut,ht,ite_true] at hqu hqv hy
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
      ThirdVariationalSources.field,ThirdVariationalSources.mixedField,ThirdVariationalSources.cubicField,
      HessianQuadraticSource.hessianField,CubicVariationalSource.cubicField,hqu,hqv,hy,map_smul,
      ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,smul_zero]
end Source

section Response
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0)

theorem responseClass_add_first (a c u v : State N) :
    ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T (a+c) u v=
      ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T a u v+
        ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T c u v := by
  have hd (i : Fin N) := source_add_first D hbg hsg hb hs hbd hsd hnull x T (b i) (hbg i) (hbd i) (hbd2 i) a c u v
  have hn (i j : Fin N) := source_add_first D hbg hsg hb hs hbd hsd hnull x T (s i j) (hsg i j) (hsd i j) (hsd2 i j) a c u v
  simp only [ThirdVariationalSDE.responseClass,L2AffineVariationalSolution.responseClass,
    ←sourceLinearMap_apply,ThirdVariationalSDE.driftSource,ThirdVariationalSDE.noiseSource,
    hd,hn,driftSource,noiseSource,map_add,Finset.sum_add_distrib]
  abel

theorem responseClass_smul_first (c : ℝ) (a u v : State N) :
    ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T (c • a) u v=
      c • ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T a u v := by
  have hd (i : Fin N) := source_smul_first D hbg hsg hb hs hbd hsd hnull x T (b i) (hbg i) (hbd i) (hbd2 i) c a u v
  have hn (i j : Fin N) := source_smul_first D hbg hsg hb hs hbd hsd hnull x T (s i j) (hsg i j) (hsd i j) (hsd2 i j) c a u v
  simp only [ThirdVariationalSDE.responseClass,L2AffineVariationalSolution.responseClass,
    ←sourceLinearMap_apply,ThirdVariationalSDE.driftSource,ThirdVariationalSDE.noiseSource,
    hd,hn,driftSource,noiseSource,map_smul,←Finset.smul_sum,←smul_add]

@[expose] def firstLinearMap (u v : State N) : State N→ₗ[ℝ] PredictableStateL2 N F P where
  toFun := fun a => ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T a u v
  map_add' a c := responseClass_add_first D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T a c u v
  map_smul' c a := responseClass_smul_first D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T c a u v

@[expose] def firstOperator (u v : State N) : State N→L[ℝ] PredictableStateL2 N F P :=
  (firstLinearMap D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v).toContinuousLinearMap

@[simp] theorem firstOperator_apply (a u v : State N) :
    firstOperator D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v a=
      ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T a u v := rfl
end Response
end SphericalAging.ThirdVariationalLinearity
