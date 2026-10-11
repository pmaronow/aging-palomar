module

public import SphericalAging.ThirdCoefficientSourceError
public import SphericalAging.ThirdVariationalLinearity
public import SphericalAging.LinearResponseDifferentSourceDifference

public section

/-! Exact second-response difference minus the actual third response.
The remainder is the genuine resolvent applied to the two proved
coefficient and Hessian forcing errors. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdVariationResolventError
open HardSphereDynamics LocalSDE StochasticFlowDerivative PredictableLinearCoefficient
open LinearResolvent StochasticLinearizationError
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem response_remainder_eq (D : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[F 0] S)
    (x y : State N) (T : ℝ≥0) (u v : State N) :
    SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull y T u v-
      SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T u v-
      ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T (y-x) u v=
    sourceLinearMap D (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T) T
      (driftSource T (fun i =>
        ThirdCoefficientSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (b i) (hbg i) (hb i) (hbd i) u v+
        HessianThirdSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (b i) (hbg i) (hbd i) (hbd2 i) u v)+
       noiseSource D T (fun i j =>
        ThirdCoefficientSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (s i j) (hsg i j) (hs i j) (hsd i j) u v+
        HessianThirdSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (s i j) (hsg i j) (hsd i j) (hsd2 i j) u v)) := by
  let ax := driftRows D hbg hb hs x T
  let ay := driftRows D hbg hb hs y T
  let sx := noiseRows D hsg hb hs x T
  let sy := noiseRows D hsg hb hs y T
  let Q := fun z => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull z T u v
  let Hb := fun z => SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull z T u v
  let Hs := fun z => SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull z T u v
  let Tb := ThirdVariationalSDE.driftSource D hbg hsg hb hs hbd hsd hbd2 hnull x T (y-x) u v
  let Ts := ThirdVariationalSDE.noiseSource D hbg hsg hb hs hbd hsd hsd2 hnull x T (y-x) u v
  let Ay := driftSource T (Hb y)+noiseSource D T (Hs y)
  let Ax := driftSource T (Hb x)+noiseSource D T (Hs x)
  let rb := fun i => apply (ay i) (Q y)-apply (ax i) (Q y)
  let rs := fun i j => apply (sy i j) (Q y)-apply (sx i j) (Q y)
  let Eb := fun i => ThirdCoefficientSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (b i) (hbg i) (hb i) (hbd i) u v+
    HessianThirdSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (b i) (hbg i) (hbd i) (hbd2 i) u v
  let Es := fun i j => ThirdCoefficientSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (s i j) (hsg i j) (hs i j) (hsd i j) u v+
    HessianThirdSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (s i j) (hsg i j) (hsd i j) (hsd2 i j) u v
  have heb (i : Fin N) : Eb i=rb i+Hb y i-Hb x i-Tb i := by
    dsimp [Eb,rb,Hb,Tb,ax,ay,Q]
    simp only [ThirdCoefficientSourceError.sourceError,HessianThirdSourceError.sourceError,
      ThirdVariationalSDE.driftSource,SecondVariationalSDE.driftSource,
      StochasticFlowDerivative.driftRows,SecondVariationSourceError.row,ThirdVariationalSources.source,HessianInitialSource.source]
    abel
  have hes (i j : Fin N) : Es i j=rs i j+Hs y i j-Hs x i j-Ts i j := by
    dsimp [Es,rs,Hs,Ts,sx,sy,Q]
    simp only [ThirdCoefficientSourceError.sourceError,HessianThirdSourceError.sourceError,
      ThirdVariationalSDE.noiseSource,SecondVariationalSDE.noiseSource,
      StochasticFlowDerivative.noiseRows,SecondVariationSourceError.row,ThirdVariationalSources.source,HessianInitialSource.source]
    abel
  have hd : driftSource T Eb=driftSource T rb+driftSource T (Hb y)-driftSource T (Hb x)-driftSource T Tb := by
    simp only [driftSource,heb,map_add,map_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hn : noiseSource D T Es=noiseSource D T rs+noiseSource D T (Hs y)-noiseSource D T (Hs x)-noiseSource D T Ts := by
    simp only [noiseSource,hes,map_add,map_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  let L := sourceLinearMap D ax sx T
  have hdiff := LinearResponseDifferentSourceDifference.different_source_difference D ax ay sx sy T Ax Ay
  change Q y-Q x=L (Ay-Ax+driftSource T rb+noiseSource D T rs) at hdiff
  have hsource : driftSource T Eb+noiseSource D T Es=
      Ay-Ax+driftSource T rb+noiseSource D T rs-(driftSource T Tb+noiseSource D T Ts) := by
    rw [hd,hn]
    dsimp [Ay,Ax]
    abel
  change Q y-Q x-L (driftSource T Tb+noiseSource D T Ts)=L (driftSource T Eb+noiseSource D T Es)
  rw [hdiff,←map_sub,hsource]

end SphericalAging.ThirdVariationResolventError
