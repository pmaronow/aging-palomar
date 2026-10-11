module

public import SphericalAging.BrownianIntegralPairing

public section

/-! The actual predictable-prefix pairing is its genuine time integral. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology ENNReal NNReal InnerProductSpace
namespace SphericalAging.PredictablePrefixPairing
open HardSphereDynamics VectorIto BrownianIntegralPairing
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- True stochastic-integrand pairing against the prefix indicator,
with both horizons retained exactly. -/
theorem inner_onePrefix_timeCut (U : PredictableProcessL2 F P)
    (g : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (hU : (U : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut g T) :
    Integrable (FourPapersCommon.continuousAdaptedTimeCut g (min T s))
      (nonnegativeLebesgueMeasure.prod P) ∧
    ⟪U,onePrefix F s⟫_ℝ=
      ∫ r in Ioc (0 : ℝ≥0) (min T s),∫ ω,g r ω ∂P ∂nonnegativeLebesgueMeasure := by
  let E : TimeProcessL2 P := (onePrefix (P := P) F s).val
  have hi := L2.integrable_inner (𝕜 := ℝ) (U : TimeProcessL2 P) E
  have he : (fun q => ⟪(U : TimeProcessL2 P) q,E q⟫_ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut g (min T s) := by
    filter_upwards [hU,onePrefix_coeFn (P := P) (F := F) s] with q hu he
    change E q=(if q.1∈Ioc (0 : ℝ≥0) s then 1 else 0) at he
    simp only [RCLike.inner_apply,conj_trivial,hu,he,FourPapersCommon.continuousAdaptedTimeCut]
    have hm : q.1∈Ioc (0 : ℝ≥0) (min T s) ↔ q.1∈Ioc (0 : ℝ≥0) T ∧ q.1∈Ioc (0 : ℝ≥0) s := by
      simp only [mem_Ioc,le_min_iff]
      tauto
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;> by_cases hs : q.1∈Ioc (0 : ℝ≥0) s <;>
      simp only [ht,hs,hm,ite_true,ite_false,true_and,false_and,and_true,and_false,
        one_mul,zero_mul,mul_zero]
  have hg := hi.congr he
  refine ⟨hg,?_⟩
  change ⟪(U : TimeProcessL2 P),E⟫_ℝ=_
  rw [L2.inner_def,integral_congr_ae he,integral_prod _ hg,← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun r => by
    by_cases hr : r∈Ioc (0 : ℝ≥0) (min T s)
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,if_pos hr,indicator_of_mem hr]
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,if_neg hr,integral_zero,indicator_of_notMem hr])

variable {N : ℕ}

theorem vectorIto_coordinate_timeCut (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) (i : Fin N)
    (g : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (hU : (U i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut g T) :
    (∫ ω,(vectorIto D U : Ω → ℝ) ω*D.coordinate i s ω ∂P)=
      ∫ r in Ioc (0 : ℝ≥0) (min T s),∫ ω,g r ω ∂P ∂nonnegativeLebesgueMeasure := by
  rw [integral_vectorIto_mul_coordinate]
  exact (inner_onePrefix_timeCut (U i) g T s hU).2

end SphericalAging.PredictablePrefixPairing
