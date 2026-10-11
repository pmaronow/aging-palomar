module

public import SphericalAging.WeightedBrownianNoiseRow

public section

/-! Zero mean and exact variance of a genuine predictable Brownian row. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.WeightedBrownianRowVariance
open HardSphereDynamics VectorIto WeightedBrownianNoiseRow
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem weighted_increment_integral (D : BrownianDriver N P F) (i : Fin N)
    {r q : ℝ≥0} (hrq : r≤q) (Z : Ω→ℝ) (hZ : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[F r] Z P) :
    (∫ ω,Z ω*increment D i r q ω ∂P)=0 := by
  have hi := FourPapersCommon.FilteredBrownian.indep_increment_of_natural_adapted
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) hrq hZm
  have he := hi.integral_fun_mul_eq_mul_integral
    (increment_memLp_two D i r q).aestronglyMeasurable (hZm.mono (F.le r))
  calc
    _=∫ ω,increment D i r q ω*Z ω ∂P := by
      apply integral_congr_ae
      exact .of_forall (fun _ => mul_comm _ _)
    _=(∫ ω,increment D i r q ω ∂P)*(∫ ω,Z ω ∂P) := he
    _=0 := by rw [increment_integral D i r q,zero_mul]

theorem row_integral (D : BrownianDriver N P F) {r q : ℝ≥0} (hrq : r≤q)
    (Z : Fin N→Ω→ℝ) (hZ : ∀j,MemLp (Z j) 2 P)
    (hZm : ∀j,AEStronglyMeasurable[F r] (Z j) P) :
    (∫ ω,∑j : Fin N,Z j ω*increment D j r q ω ∂P)=0 := by
  rw [integral_finsetSum _ (fun j _ => (weighted_increment_memLp D j hrq (Z j) (hZ j) (hZm j)).integrable (by norm_num))]
  simp only [weighted_increment_integral D _ hrq _ (hZ _) (hZm _),Finset.sum_const_zero]

/-- Genuine weighted-increment variance, with its zero mean derived from
future independence of the actual driving process. -/
theorem row_variance (D : BrownianDriver N P F) {r q : ℝ≥0} (hrq : r≤q)
    (Z : Fin N→Ω→ℝ) (hZ : ∀j,MemLp (Z j) 2 P)
    (hZm : ∀j,AEStronglyMeasurable[F r] (Z j) P) :
    variance (fun ω => ∑j : Fin N,Z j ω*increment D j r q ω) P=
      ((q : ℝ)-(r : ℝ))*(∫ ω,∑j : Fin N,(Z j ω)^2 ∂P) := by
  have hh := row_secondMoment D hrq Z hZ hZm
  rw [variance_of_integral_eq_zero hh.1.aestronglyMeasurable.aemeasurable (row_integral D hrq Z hZ hZm)]
  exact hh.2

end SphericalAging.WeightedBrownianRowVariance
