module

public import SphericalAging.VectorIto
public import SphericalAging.ActualSphereBackwardVariance

public section

/-! Genuine pairing of the full-filtration vector Itô integral with an
actual Brownian terminal coordinate. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology ENNReal NNReal InnerProductSpace BigOperators
namespace SphericalAging.BrownianIntegralPairing
open HardSphereDynamics VectorIto
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def onePrefix (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (s : ℝ≥0) :
    PredictableProcessL2 F P := elementaryPredictable F 0 s (adaptedOne F 0)

theorem onePrefix_coeFn (s : ℝ≥0) :
    (onePrefix (P := P) F s : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => if q.1∈Ioc (0 : ℝ≥0) s then 1 else 0 := by
  have hone : ∀ᵐ q : ℝ≥0 × Ω ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedOne (P := P) F 0 : Ω → ℝ) q.2=1 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_const 2 P (1 : ℝ))
  filter_upwards [elementaryPredictable_coeFn F 0 s (adaptedOne (P := P) F 0),hone] with q hq ho
  simpa only [onePrefix,ho] using hq

theorem coordinateIto_onePrefix_ae (D : BrownianDriver N P F) (i : Fin N) (s : ℝ≥0) :
    (coordinateIto D i (onePrefix F s) : Ω → ℝ)=ᵐ[P] D.coordinate i s := by
  have hito := FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i)
    (show (0 : ℝ≥0)≤s from zero_le) (adaptedOne (P := P) F 0)
  change coordinateIto D i (onePrefix F s)=_ at hito
  rw [hito]
  filter_upwards [FourPapersCommon.FilteredBrownian.coeFn_elementaryBrownianValue
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i)
      (show (0 : ℝ≥0)≤s from zero_le) (adaptedOne (P := P) F 0),
    Lp.coeFn_const 2 P (1 : ℝ),(D.filtered i).toIsPreBrownianReal.eval_zero_ae_eq_zero]
    with ω hi ho hz
  simpa only [adaptedOne,ho,hz,Pi.zero_apply,Function.const_apply,mul_one,one_mul,sub_zero] using hi

theorem inner_vectorIto_coordinate_prefix (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) (i : Fin N) (s : ℝ≥0) :
    ⟪vectorIto D U,coordinateIto D i (onePrefix F s)⟫_ℝ=⟪U i,onePrefix F s⟫_ℝ := by
  unfold vectorIto
  rw [sum_inner,Finset.sum_eq_single i]
  · exact inner_coordinateIto_same D i (U i) (onePrefix F s)
  · intro j hj hji
    exact inner_coordinateIto_cross D hji (U j) (onePrefix F s)
  · simp

/-- Actual Brownian pairing equals the inner product of the genuine
predictable integrand with the deterministic prefix indicator. -/
theorem integral_vectorIto_mul_coordinate (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) (i : Fin N) (s : ℝ≥0) :
    (∫ ω,(vectorIto D U : Ω → ℝ) ω*D.coordinate i s ω ∂P)=⟪U i,onePrefix F s⟫_ℝ := by
  have he := inner_vectorIto_coordinate_prefix D U i s
  rw [L2.inner_def] at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [coordinateIto_onePrefix_ae D i s] with ω hω
  simp only [RCLike.inner_apply,conj_trivial,hω,mul_comm]

end SphericalAging.BrownianIntegralPairing
