module

public import SphericalAging.SecondVariationFourthBounds
public import SphericalAging.AdaptedTimeFourthIntegralBound

public section

/-! Uniform direction-homogeneous L⁴ bounds in the genuine time-product
space used by differentiating the variational equations. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.SecondVariationTimeFourthBounds
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment SecondVariationFourthBounds
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def normCeiling (N : ℕ) (Kb Ks Lb Ls T : ℝ≥0) : ℝ :=
  ((T:ℝ)*momentCeiling N Kb Ks Lb Ls T)^((1:ℝ)/4)

section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0) (u v : State N)

theorem process_time_fourth_bound :
    (∫q,‖stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v) T q‖^4
      ∂nonnegativeLebesgueMeasure.prod P)≤(T:ℝ)*momentCeiling N Kb Ks Lb Ls T*‖u‖^4*‖v‖^4 := by
  have hh := AdaptedTimeFourthIntegralBound.time_fourth_integral_le _ T
    (momentCeiling N Kb Ks Lb Ls T*‖u‖^4*‖v‖^4)
    (SecondVariationFourthMoment.process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull x T u v)
    (fun t ht => process_fourthMoment_bound D hbg hsg hb hs hnull x T u v hbd hsd t ht)
  simpa only [mul_assoc] using hh

theorem responseClass_lpNorm_four_le :
    lpNorm (SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T u v :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) 4 (nonnegativeLebesgueMeasure.prod P)≤
        normCeiling N Kb Ks Lb Ls T*‖u‖*‖v‖ := by
  have hm := SecondVariationFourthMoment.responseClass_memLp_fourth D hbg hsg hb hs hbd hsd hnull x T u v
  have hi : (∫q,‖(SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T u v :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q‖^4∂nonnegativeLebesgueMeasure.prod P)≤
        ((T:ℝ)*momentCeiling N Kb Ks Lb Ls T*‖u‖^4)*‖v‖^4 := by
    have he : (∫q,‖stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v) T q‖^4
        ∂nonnegativeLebesgueMeasure.prod P)=
        (∫q,‖(SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T u v :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q‖^4∂nonnegativeLebesgueMeasure.prod P) :=
      integral_congr_ae ((SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T u v).mono
        (fun _ he => congrArg (fun z : State N => ‖z‖^4) he))
    rw [←he]
    exact process_time_fourth_bound D hbg hsg hb hs hbd hsd hnull x T u v
  have hC := momentCeiling_nonneg N Kb Ks Lb Ls T
  have hh := LpMomentBounds.lpNorm_four_le_of_moment hm (by positivity : 0≤(T:ℝ)*momentCeiling N Kb Ks Lb Ls T*‖u‖^4) hi
  apply hh.trans_eq
  rw [Real.mul_rpow (by positivity : 0≤(T:ℝ)*momentCeiling N Kb Ks Lb Ls T) (by positivity)]
  have hr : (‖u‖^4)^((1:ℝ)/4)=‖u‖ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [hr]
  rfl

end Flow
end SphericalAging.SecondVariationTimeFourthBounds
