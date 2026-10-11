module

public import SphericalAging.SecondVariationSourceQuadraticRate
public import SphericalAging.SecondVariationResolventError
public import SphericalAging.LinearResolventUniformBound

public section

/-! Actual first-response spatial Taylor errors have a quadratic L²
bound, uniform in the response direction. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstResponseQuadraticRemainder
open HardSphereDynamics LocalSDE StochasticFlowDerivative LinearResolvent
open StochasticLinearizationError SecondVariationSourceError VolterraLinearity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem response_remainder_quadratic_bound (D₀ : BrownianDriver N P F)
    {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) :
    ∃ C : ℝ,0≤C ∧ ∀ y v : State N,
      ‖response (NullAugmentation.driver D₀) hbg hsg hb hs y T v-
        response (NullAugmentation.driver D₀) hbg hsg hb hs x T v-
        SecondVariationalSDE.responseClass (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
          (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T (y-x) v‖≤
          C*‖y-x‖^2*‖v‖ := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  have hd (i : Fin N) := SecondVariationSourceQuadraticRate.sourceError_quadratic_rate D₀
    hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT (b i) (hbg i) (hb i) (hbd i) (hbd2 i)
  have hn (i j : Fin N) := SecondVariationSourceQuadraticRate.sourceError_quadratic_rate D₀
    hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j)
  choose Ab hAb hdb using hd
  choose As hAs hns using hn
  let Cb := ∑i : Fin N,Ab i
  let Cs := ∑i : Fin N,∑j : Fin N,As i j
  have hCb : 0≤Cb := Finset.sum_nonneg (fun i _ => hAb i)
  have hCs : 0≤Cs := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hAs i j))
  let L := sourceLinearMap D (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T) T
  let C := ‖L‖*((N:ℝ)*T*Cb+(N:ℝ)^2*Real.sqrt T*Cs)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro y v
  let rb := fun i => sourceError D hbg hsg hb hs hnull x y T (b i) (hbg i) (hb i) (hbd i) v
  let rs := fun i j => sourceError D hbg hsg hb hs hnull x y T (s i j) (hsg i j) (hs i j) (hsd i j) v
  have hbr (i : Fin N) : ‖rb i‖≤Cb*‖y-x‖^2*‖v‖ := by
    apply (hdb i y v).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hAb j) (Finset.mem_univ i)) (sq_nonneg _)) (norm_nonneg _)
  have hsr (i j : Fin N) : ‖rs i j‖≤Cs*‖y-x‖^2*‖v‖ := by
    apply (hns i j y v).trans
    have ha : As i j≤Cs := (Finset.single_le_sum (fun k _ => hAs i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hAs k l)) (Finset.mem_univ i))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (sq_nonneg _)) (norm_nonneg _)
  rw [SecondVariationResolventError.response_remainder_eq]
  change ‖L (driftSource T rb+noiseSource D T rs)‖≤_
  calc
    _≤‖L‖*‖driftSource T rb+noiseSource D T rs‖ := L.le_opNorm _
    _≤‖L‖*(‖driftSource T rb‖+‖noiseSource D T rs‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg L)
    _≤‖L‖*((N:ℝ)*T*(Cb*‖y-x‖^2*‖v‖)+(N:ℝ)^2*Real.sqrt T*(Cs*‖y-x‖^2*‖v‖)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (driftSource_norm_le T rb _ hbr) (noiseSource_norm_le D T rs _ hsr)) (norm_nonneg L)
    _=_ := by dsimp [C];ring

end SphericalAging.FirstResponseQuadraticRemainder
