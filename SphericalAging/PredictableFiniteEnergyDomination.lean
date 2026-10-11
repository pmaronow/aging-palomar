module

public import SphericalAging.WholeVectorCoefficientEnergy

public section

/-! Finite whole-vector predictable energy retains its true pointwise
quadratic domination before any dimension sum is estimated. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.PredictableFiniteEnergyDomination
open HardSphereDynamics WholeVectorCoefficientEnergy
set_option maxHeartbeats 1500000
variable {I : Type*} [Fintype I] {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem finite_restricted_energy_le (A : I→PredictableProcessL2 F P)
    (b : I→ℝ≥0→Ω→ℝ) (T : ℝ≥0)
    (hA : ∀i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (b i) T)
    (Z : ℝ≥0×Ω→State N) (hZ : MemLp Z 2 (nonnegativeLebesgueMeasure.prod P))
    (K : ℝ) (hK : 0≤K)
    (hb : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑i,(FourPapersCommon.continuousAdaptedTimeCut (b i) T q)^2)≤K*‖Z q‖^2) :
    (∑i,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F T (A i)‖^2)≤
      K*(∫q,‖Z q‖^2 ∂nonnegativeLebesgueMeasure.prod P) := by
  have hi (i : I) : Integrable
      (fun q => (FourPapersCommon.continuousAdaptedTimeCut (b i) T q)^2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (timeCut_memLp (A i) (b i) T T le_rfl (hA i)).integrable_sq
  have hZi : Integrable (fun q => ‖Z q‖^2) (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      hZ.integrable_norm_rpow (by norm_num) (by norm_num)
  calc
    _=∫q,∑i,(FourPapersCommon.continuousAdaptedTimeCut (b i) T q)^2
        ∂nonnegativeLebesgueMeasure.prod P := by
      simp_rw [restricted_norm_sq_eq_product_integral _ _ T T le_rfl (hA _)]
      exact (integral_finsetSum Finset.univ (fun i _ => hi i)).symm
    _≤∫q,K*‖Z q‖^2 ∂nonnegativeLebesgueMeasure.prod P :=
      integral_mono_ae (integrable_finsetSum Finset.univ (fun i _ => hi i))
        (hZi.const_mul K) hb
    _=_ := integral_const_mul _ _

end SphericalAging.PredictableFiniteEnergyDomination
