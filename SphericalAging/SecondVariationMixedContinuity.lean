module

public import SphericalAging.SecondVariationContinuity
public import SphericalAging.SecondVariationTimeFourthBounds
public import SphericalAging.LpFourthMultiplierTruncation

public section

/-! Genuine second responses, multiplied by any fixed L⁴ field, are
spatially continuous in the actual product-time L² norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationMixedContinuity
open HardSphereDynamics LocalSDE SecondVariationTimeFourthBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem actual_mixed_difference_tendsto (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (u v : State N)
    {E : Type*} [NormedAddCommGroup E] (W : ℝ≥0×Ω→E)
    (hW : MemLp W 4 (nonnegativeLebesgueMeasure.prod P)) :
    Tendsto (fun y => lpNorm (fun q =>
      ‖((SecondVariationalSDE.responseClass (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) y T u v-
        SecondVariationalSDE.responseClass (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
          (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T u v :
            PredictableStateL2 N (NullAugmentation.augment F P) P) :
              Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q‖*‖W q‖) 2
                (nonnegativeLebesgueMeasure.prod P)) (𝓝 x) (𝓝 0) := by
  let D := NullAugmentation.driver D₀
  let F' := NullAugmentation.augment F P
  let μ := nonnegativeLebesgueMeasure.prod P
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F' 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fun y => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull y T u v
  let f : State N→ℝ≥0×Ω→State N := fun y => ((Q y-Q x : PredictableStateL2 N F' P) : Lp (State N) 2 μ)
  have hm (y : State N) := SecondVariationFourthMoment.responseClass_memLp_fourth D hbg hsg hb hs hbd hsd hnull y T u v
  have hf2 (y : State N) : MemLp (f y) 2 μ := Lp.memLp _
  have hf4 (y : State N) : MemLp (f y) 4 μ :=
    ((hm y).sub (hm x)).ae_eq (Lp.coeFn_sub
      (Q y : Lp (State N) 2 μ) (Q x : Lp (State N) 2 μ)).symm
  have he (y : State N) : lpNorm (f y) 2 μ=‖Q y-Q x‖ := by
    change (eLpNorm _ 2 μ).toReal=‖((Q y-Q x : PredictableStateL2 N F' P) : Lp (State N) 2 μ)‖
    rw [Lp.norm_def]
  have hQ : Continuous Q := SecondVariationContinuity.responseClass_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT u v
  have hzero : Tendsto (fun y => lpNorm (f y) 2 μ) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y => ‖Q y-Q x‖) := (hQ.sub continuous_const).norm
    simpa only [he,sub_self,norm_zero] using hc.tendsto x
  let C := 2*normCeiling N Kb Ks Lb Ls T*‖u‖*‖v‖
  have hC : 0≤C := by
    have hE : 0≤normCeiling N Kb Ks Lb Ls T := Real.rpow_nonneg
      (mul_nonneg T.coe_nonneg (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
    dsimp [C];positivity
  have hb4 (y : State N) : lpNorm (f y) 4 μ≤C := by
    have ha := Lp.coeFn_sub (Q y : Lp (State N) 2 μ) (Q x : Lp (State N) 2 μ)
    change (eLpNorm ((Q y : Lp (State N) 2 μ)-(Q x : Lp (State N) 2 μ)) 4 μ).toReal≤C
    rw [eLpNorm_congr_ae ha]
    apply (lpNorm_sub_le (hm y) (by norm_num)).trans
    have hy := responseClass_lpNorm_four_le D hbg hsg hb hs hbd hsd hnull y T u v
    have hx := responseClass_lpNorm_four_le D hbg hsg hb hs hbd hsd hnull x T u v
    exact (add_le_add hy hx).trans_eq (by dsimp [C];ring)
  apply LpFourthMultiplierTruncation.lpNorm_two_tendsto_zero hW (f:=f) (L:=1) (C:=C) (by norm_num) hC
    (.of_forall hf2) (.of_forall hf4)
  · exact .of_forall (fun y => (hf2 y).aestronglyMeasurable.norm.mul hW.aestronglyMeasurable.norm)
  · exact .of_forall (fun y => .of_forall (fun q => by
      rw [Real.norm_of_nonneg (by positivity : 0≤‖f y q‖*‖W q‖),one_mul]))
  · exact .of_forall hb4
  · exact hzero

end SphericalAging.SecondVariationMixedContinuity
