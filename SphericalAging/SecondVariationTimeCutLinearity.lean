module

public import SphericalAging.SecondVariationBilinear

public section

/-! Direction linearity of the literal second variational process cuts
follows from the already proved actual L² response identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationTimeCutLinearity
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0)

theorem timeCut_add_left (u v w : State N) :
    stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (u+w) v) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v) T q+
          stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T w v) T q) := by
  let Q := fun a => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T a v
  have he : (Q (u+w) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))=
      (Q u : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))+(Q w : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
    congrArg Subtype.val (SecondVariationBilinear.responseClass_add_left D hbg hsg hb hs hbd hsd hnull x T u v w)
  filter_upwards [SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T (u+w) v,
    SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T u v,
    SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T w v,
    Lp.coeFn_add (Q u : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) (Q w)] with q ha hu hw hs
  rw [ha,he,hs,Pi.add_apply,←hu,←hw]

theorem timeCut_smul_left (c : ℝ) (u v : State N) :
    stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (c • u) v) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => c • stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v) T q) := by
  let Q := fun a => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T a v
  have he : (Q (c • u) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))=
      c • (Q u : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
    congrArg Subtype.val (SecondVariationBilinear.responseClass_smul_left D hbg hsg hb hs hbd hsd hnull x T c u v)
  filter_upwards [SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T (c • u) v,
    SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T u v,
    Lp.coeFn_smul c (Q u : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))] with q ha hu hs
  rw [ha,he,hs,Pi.smul_apply,←hu]
end Flow
end SphericalAging.SecondVariationTimeCutLinearity
