module

public import SphericalAging.WeightedBrownianTheorem
public import SphericalAging.WhitePrefixResponse
public import SphericalAging.CKPhysicalConsequences

public section

/-! Actual normalized remote-response test weight in source 11.11 Step 1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace RealInnerProductSpace
namespace SphericalAging.RemoteResponseTest
open CKSpecification CKPhysicalConsequences WhitePrefixResponse WeightedBrownianTheorem
open WienerVectorGaussian WienerTrunkWeight WienerForkTransfer FiniteModel

theorem remoteTail_eq_trunk (d : CKData) (T L : ℝ≥0) :
    remoteTail d (T+L) L=∫u in (0:ℝ)..(T:ℝ),(d.R (T+L) u)^2 := by
  unfold remoteTail
  simp only [NNReal.coe_add,add_sub_cancel_right,max_eq_right T.coe_nonneg]

theorem remoteTail_positive {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℝ≥0} (hT : 0<T) (L : ℝ≥0) :
    0<remoteTail d (T+L) L := by
  rw [remoteTail_eq_trunk]
  apply intervalIntegral.integral_pos (show (0:ℝ)<T by exact_mod_cast hT)
    ((response_row_continuous h T L).pow 2)
  · intro u _
    exact sq_nonneg _
  · refine ⟨0,⟨le_rfl,T.coe_nonneg⟩,?_⟩
    exact sq_pos_of_pos (response_strictly_positive h (by norm_num)
      (show (0:ℝ)≤(T+L:ℝ≥0) from (T+L).coe_nonneg))

@[expose] def testWeight (d : CKData) (T L : ℝ≥0) (u : ℝ) : ℝ :=
  d.R (T+L) u/Real.sqrt (remoteTail d (T+L) L)

theorem testWeight_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T L : ℝ≥0) : ContinuousOn (testWeight d T L) (Icc 0 (T:ℝ)) :=
  (response_row_continuous h T L).div_const _

theorem testWeight_unit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℝ≥0} (hT : 0<T) (L : ℝ≥0) :
    (∫u in (0:ℝ)..(T:ℝ),(testWeight d T L u)^2)=1 := by
  have hs := remoteTail_positive h hT L
  simp only [testWeight,div_pow]
  rw [intervalIntegral.integral_div,Real.sq_sqrt hs.le,←remoteTail_eq_trunk]
  exact div_self hs.ne'

theorem testWeight_response {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℝ≥0} (hT : 0<T) (L : ℝ≥0) :
    Real.sqrt 2*(∫u in (0:ℝ)..(T:ℝ),testWeight d T L u*d.R (T+L) u)=
      Real.sqrt (2*remoteTail d (T+L) L) := by
  have hs := remoteTail_positive h hT L
  have hsqrt := Real.sqrt_pos.mpr hs
  have hi : (∫u in (0:ℝ)..(T:ℝ),testWeight d T L u*d.R (T+L) u)=
      remoteTail d (T+L) L/Real.sqrt (remoteTail d (T+L) L) := by
    calc
      _ = ∫u in (0:ℝ)..(T:ℝ),(d.R (T+L) u)^2/Real.sqrt (remoteTail d (T+L) L) := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only [testWeight]
        ring
      _ = (∫u in (0:ℝ)..(T:ℝ),(d.R (T+L) u)^2)/Real.sqrt (remoteTail d (T+L) L) :=
        intervalIntegral.integral_div _ _
      _ = _ := by rw [remoteTail_eq_trunk]
  rw [hi,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  apply (div_eq_iff hsqrt.ne').mpr
  exact (Real.mul_self_sqrt hs.le).symm

end SphericalAging.RemoteResponseTest
