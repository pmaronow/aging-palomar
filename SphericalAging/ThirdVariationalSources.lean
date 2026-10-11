module

public import SphericalAging.CubicVariationalSource

public section

/-! Literal third variational forcing along the genuine flow: the three
mixed Hessian terms and the cubic first-response term. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.ThirdVariationalSources
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
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

@[expose] def mixedField (u v w : State N) : ℝ≥0→Ω→ℝ :=
  HessianQuadraticSource.hessianField g (GlobalSDE.horizonProcess D hb hs x T)
    (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w)

@[expose] def mixedSource (u v w : State N) : PredictableProcessL2 F P :=
  HessianQuadraticSource.source g hg hL (GlobalSDE.horizonProcess D hb hs x T)
    (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (SecondVariationalSDE.process_strongSolution D hbg hsg hb hs hbd hsd hnull x T u v).1
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_continuous D hb hs x T)
    (SecondVariationalSDE.process_strongSolution D hbg hsg hb hs hbd hsd hnull x T u v).2.1
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T w) T
    (SecondVariationFourthMoment.process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull x T u v)
    (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull w).1

lemma mixedSource_coe (u v w : State N) :
    (mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w : TimeProcessL2 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (mixedField D hbg hsg hb hs hbd hsd hnull x T g u v w) T :=
  HessianQuadraticSource.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

@[expose] def cubicField (u v w : State N) : ℝ≥0→Ω→ℝ :=
  CubicVariationalSource.cubicField g (GlobalSDE.horizonProcess D hb hs x T)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T u)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w)

@[expose] def cubicSource (u v w : State N) : PredictableProcessL2 F P :=
  CubicVariationalSource.source g hg hM (GlobalSDE.horizonProcess D hb hs x T)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T u)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T u)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_continuous D hb hs x T)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T u)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T w) T
    (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull u).1
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v).1
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull w).1

lemma cubicSource_coe (u v w : State N) :
    (cubicSource D hbg hsg hb hs hnull x T g hg hM u v w : TimeProcessL2 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (cubicField D hbg hsg hb hs x T g u v w) T :=
  CubicVariationalSource.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

@[expose] def field (u v w : State N) : ℝ≥0→Ω→ℝ := fun t omega =>
  mixedField D hbg hsg hb hs hbd hsd hnull x T g u v w t omega+
  mixedField D hbg hsg hb hs hbd hsd hnull x T g u w v t omega+
  mixedField D hbg hsg hb hs hbd hsd hnull x T g v w u t omega+
  cubicField D hbg hsg hb hs x T g u v w t omega

@[expose] def source (u v w : State N) : PredictableProcessL2 F P :=
  mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w+
  mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u w v+
  mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL v w u+
  cubicSource D hbg hsg hb hs hnull x T g hg hM u v w

lemma source_coe (u v w : State N) :
    (source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM u v w : TimeProcessL2 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (field D hbg hsg hb hs hbd hsd hnull x T g u v w) T := by
  let A := mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w
  let B := mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u w v
  let C := mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL v w u
  let E := cubicSource D hbg hsg hb hs hnull x T g hg hM u v w
  filter_upwards [Lp.coeFn_add ((A+B+C:PredictableProcessL2 F P):TimeProcessL2 P) E,
    Lp.coeFn_add ((A+B:PredictableProcessL2 F P):TimeProcessL2 P) C,
    Lp.coeFn_add (A:TimeProcessL2 P) B,
    mixedSource_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w,
    mixedSource_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL u w v,
    mixedSource_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL v w u,
    cubicSource_coe D hbg hsg hb hs hnull x T g hg hM u v w] with q he hc hb h1 h2 h3 h4
  change ((A+B+C+E:PredictableProcessL2 F P):TimeProcessL2 P) q=_
  simp only [Submodule.coe_add] at he hc hb ⊢
  rw [he,Pi.add_apply,hc,Pi.add_apply,hb,Pi.add_apply,h1,h2,h3,h4]
  by_cases hq : q.1∈Ioc (0:ℝ≥0) T <;>
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,ite_false,field,zero_add]
end Flow
end SphericalAging.ThirdVariationalSources
