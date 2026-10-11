module

public import SphericalAging.FirstResponseRemainderFourthBound

public section

/-! Genuine mixed first-response Taylor errors vanish relative to the
initial increment in the actual product-time L² space. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstResponseRemainderMixed
open HardSphereDynamics LocalSDE StochasticFlowDerivative FirstResponseRemainderFourthBound
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem remainder_two_quadratic_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) :
    ∃C : ℝ,0≤C ∧ ∀y v : State N,
      MemLp (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T v) 2
          (nonnegativeLebesgueMeasure.prod P) ∧
      lpNorm (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T v) 2
          (nonnegativeLebesgueMeasure.prod P)≤C*‖y-x‖^2*‖v‖ := by
  obtain ⟨C,hC,hbound⟩ := FirstResponseQuadraticRemainder.response_remainder_quadratic_bound
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
  refine ⟨C,hC,?_⟩
  intro y v
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let R := response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v-
    SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T (y-x) v
  have he := remainderCut_class_ae D hbg hsg hb hs hbd hsd hnull x y T v
  refine ⟨(Lp.memLp (R : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).ae_eq he.symm,?_⟩
  have hn : lpNorm (remainderCut D hbg hsg hb hs hbd hsd hnull x y T v) 2
      (nonnegativeLebesgueMeasure.prod P)=‖R‖ := by
    change (eLpNorm _ 2 _).toReal=‖(R : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))‖
    rw [eLpNorm_congr_ae he,Lp.norm_def]
  rw [hn]
  exact hbound y v

theorem actual_mixed_remainder_littleO (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (v : State N)
    {E : Type*} [NormedAddCommGroup E] (W : ℝ≥0×Ω→E)
    (hW : MemLp W 4 (nonnegativeLebesgueMeasure.prod P)) :
    (fun y => lpNorm (fun q =>
      ‖remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T v q‖*‖W q‖) 2
          (nonnegativeLebesgueMeasure.prod P))=o[𝓝 x] (fun y => y-x) := by
  obtain ⟨C,hC,hbound⟩ := remainder_two_quadratic_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let R := fun y => remainderCut D hbg hsg hb hs hbd hsd hnull x y T v
  have hfour (y : State N) := remainder_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT v
  have hE : 0≤SecondVariationTimeFourthBounds.normCeiling N Kb Ks Lb Ls T :=
    Real.rpow_nonneg (mul_nonneg T.coe_nonneg
      (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
  apply LpFourthMultiplierTruncation.isLittleO_of_quadratic_two_linear_four x hW
    (f:=R) (L:=1) (A:=C*‖v‖) (B:=2*SecondVariationTimeFourthBounds.normCeiling N Kb Ks Lb Ls T*‖v‖)
    (by norm_num) (mul_nonneg hC (norm_nonneg _)) (by positivity)
  · intro y; exact (hbound y v).1
  · intro y; exact (hfour y).1
  · intro y; exact ((hbound y v).1.aestronglyMeasurable.norm.mul hW.aestronglyMeasurable.norm)
  · intro y
    exact .of_forall (fun q => by rw [Real.norm_of_nonneg (by positivity : 0≤‖R y q‖*‖W q‖),one_mul])
  · intro y; simpa only [R,D,mul_assoc,mul_left_comm,mul_comm] using (hbound y v).2
  · intro y; simpa only [R,D,mul_assoc,mul_left_comm,mul_comm] using (hfour y).2

end SphericalAging.FirstResponseRemainderMixed
