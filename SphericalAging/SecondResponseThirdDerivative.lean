module

public import SphericalAging.ThirdVariationResolventError
public import SphericalAging.ThirdCoefficientSourceLittleO

public section

/-! The actual third variational strong SDE is genuinely the Fréchet
derivative of each constructed second response. The derivative identity
and all forcing remainders are conclusions, not assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondResponseThirdDerivative
open HardSphereDynamics LocalSDE StochasticFlowDerivative LinearResolvent
open StochasticLinearizationError VolterraLinearity
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

theorem responseClass_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms Ab As : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (hbd3 : ∀i,LipschitzWith Ab (fderiv ℝ (fderiv ℝ (fderiv ℝ (b i)))))
    (hsd3 : ∀i j,LipschitzWith As (fderiv ℝ (fderiv ℝ (fderiv ℝ (s i j)))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (u v : State N) :
    HasFDerivAt (fun y => SecondVariationalSDE.responseClass (NullAugmentation.driver D₀)
      hbg hsg hb hs hbd hsd (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) y T u v)
      (ThirdVariationalLinearity.firstOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T u v) x := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let rb := fun i y => ThirdCoefficientSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T
      (b i) (hbg i) (hb i) (hbd i) u v+
    HessianThirdSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (b i) (hbg i) (hbd i) (hbd2 i) u v
  let rs := fun i j y => ThirdCoefficientSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T
      (s i j) (hsg i j) (hs i j) (hsd i j) u v+
    HessianThirdSourceError.sourceError D hbg hsg hb hs hbd hsd hnull x y T (s i j) (hsg i j) (hsd i j) (hsd2 i j) u v
  have hrb (i : Fin N) : rb i=o[𝓝 x] (fun y => y-x) :=
    (ThirdCoefficientSourceLittleO.sourceError_isLittleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
      (b i) (hbg i) (hb i) (hbd i) (hbd2 i) u v).add
    (HessianThirdSourceLittleO.sourceError_isLittleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
      (b i) (hbg i) (hbd i) (hbd2 i) (hbd3 i) u v)
  have hrs (i j : Fin N) : rs i j=o[𝓝 x] (fun y => y-x) :=
    (ThirdCoefficientSourceLittleO.sourceError_isLittleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
      (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j) u v).add
    (HessianThirdSourceLittleO.sourceError_isLittleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
      (s i j) (hsg i j) (hsd i j) (hsd2 i j) (hsd3 i j) u v)
  have hd : (fun y => driftSource T (fun i => rb i y))=o[𝓝 x] (fun y => y-x) := by
    have hh := Asymptotics.IsLittleO.sum (s:=(Finset.univ : Finset (Fin N)))
      (A:=fun i y => ((stateInclusion i).comp (driftOperator T)) (rb i y))
      (fun i _ => (((stateInclusion i).comp (driftOperator T)).isBigO_comp (rb i) (𝓝 x)).trans_isLittleO (hrb i))
    simpa only [driftSource,ContinuousLinearMap.comp_apply,Finset.sum_fn] using hh
  have hn : (fun y => noiseSource D T (fun i j => rs i j y))=o[𝓝 x] (fun y => y-x) := by
    have hinner (i : Fin N) := Asymptotics.IsLittleO.sum (s:=(Finset.univ : Finset (Fin N)))
      (A:=fun j y => itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (rs i j y))
      (fun j _ => ((itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T).isBigO_comp
        (rs i j) (𝓝 x)).trans_isLittleO (hrs i j))
    have hinner' (i : Fin N) : (fun y => ∑j : Fin N,
        itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (rs i j y))=o[𝓝 x] (fun y => y-x) := by
      simpa only [Finset.sum_fn] using hinner i
    have hh := Asymptotics.IsLittleO.sum (s:=(Finset.univ : Finset (Fin N)))
      (A:=fun i y => stateInclusion i (∑j : Fin N,
        itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (rs i j y)))
      (fun i _ => ((stateInclusion i).isBigO_comp _ (𝓝 x)).trans_isLittleO (hinner' i))
    simpa only [noiseSource,Finset.sum_fn] using hh
  let L := sourceLinearMap D (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T) T
  have hh := (L.isBigO_comp _ (𝓝 x)).trans_isLittleO (hd.add hn)
  rw [hasFDerivAt_iff_isLittleO]
  simpa only [ThirdVariationalLinearity.firstOperator_apply] using
    hh.congr_left (fun y => (ThirdVariationResolventError.response_remainder_eq
      D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x y T u v).symm)

end SphericalAging.SecondResponseThirdDerivative
