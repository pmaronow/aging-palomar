module

public import SphericalAging.SecondResponseThirdDerivative
public import SphericalAging.ThirdSourceFirstOperator
public import SphericalAging.FirstCoefficientSecondDerivative

public section

/-! The genuine second coefficient row has a third spatial derivative:
its actual third-response coefficient and literal third forcing. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondCoefficientThirdDerivative
open HardSphereDynamics LocalSDE StochasticFlowDerivative PredictableLinearCoefficient
open SecondVariationSourceError FlowCoefficientDerivative TerminalLinearity
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
section Definition
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms K L M : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (u v : State N)

@[expose] def secondCoefficient : PredictableProcessL2 F P :=
  apply (row D hb hs T g hg hK x)
    (SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T u v)+
  HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL u v

@[expose] def rowThirdOperator : State N→L[ℝ] PredictableProcessL2 F P :=
  (coefficientOperator (row D hb hs T g hg hK x)).comp
    (ThirdVariationalLinearity.firstOperator D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v)+
  ThirdSourceFirstOperator.firstOperator D hbg hsg hb hs hbd hsd hnull x T g hg hL hM u v

@[simp] theorem rowThirdOperator_apply (a : State N) :
    rowThirdOperator D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T g hg hK hL hM u v a=
      apply (row D hb hs T g hg hK x)
        (ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T a u v)+
      ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T g hg hL hM a u v := rfl
end Definition

theorem secondCoefficient_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms Ab As K L M A : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (hbd3 : ∀i,LipschitzWith Ab (fderiv ℝ (fderiv ℝ (fderiv ℝ (b i)))))
    (hsd3 : ∀i j,LipschitzWith As (fderiv ℝ (fderiv ℝ (fderiv ℝ (s i j)))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g)))) (u v : State N) :
    HasFDerivAt (fun y => secondCoefficient (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) y T g hg hK hL u v)
    (rowThirdOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hK hL hM u v) x := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fun y => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull y T u v
  let G := fun y => apply (row D hb hs T g hg hK y) (Q y)-apply (row D hb hs T g hg hK x) (Q y)+
    HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL u v
  have he := (ThirdCoefficientSourceLittleO.sourceError_isLittleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
      g hg hK hL hM u v).add
    (HessianThirdSourceLittleO.sourceError_isLittleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT g hg hL hM hA u v)
  have hG : HasFDerivAt G (ThirdSourceFirstOperator.firstOperator D hbg hsg hb hs hbd hsd hnull x T g hg hL hM u v) x := by
    rw [hasFDerivAt_iff_isLittleO]
    apply he.congr_left
    intro y
    simp only [G,Q,ThirdSourceFirstOperator.firstOperator_apply,ThirdVariationalSources.source,
      ThirdCoefficientSourceError.sourceError,HessianThirdSourceError.sourceError]
    abel
  have hQ := SecondResponseThirdDerivative.responseClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 x T hT u v
  have hh := ((coefficientOperator (row D hb hs T g hg hK x)).hasFDerivAt.comp x hQ).add hG
  convert hh using 1
  · funext y
    change apply (row D hb hs T g hg hK y) (Q y)+
      HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL u v=
      apply (row D hb hs T g hg hK x) (Q y)+
        (apply (row D hb hs T g hg hK y) (Q y)-apply (row D hb hs T g hg hK x) (Q y)+
          HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL u v)
    abel
  · rfl
end SphericalAging.SecondCoefficientThirdDerivative
