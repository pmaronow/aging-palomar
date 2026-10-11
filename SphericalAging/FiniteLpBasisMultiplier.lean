module

public import SphericalAging.FirstVariationLpLift
public import SphericalAging.LpFiniteDomination
public import SphericalAging.LpMultiplierTruncation

public section

/-! A literal finite-dimensional L⁴ linear field is controlled by its
basis fields when paired with a second L⁴ field in L². -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace SphericalAging.FiniteLpBasisMultiplier
open HardSphereDynamics LocalSDE
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {μ : Measure α}
local instance : Fact ((1:ℝ≥0∞)≤4) := ⟨by norm_num⟩

theorem field_norm_le_basis (L : State N→L[ℝ] Lp E 4 μ) (v : State N) :
    ∀ᵐq∂μ,‖L v q‖≤‖v‖*∑i : Fin N,‖L (basisVector i) q‖ := by
  classical
  let V : Fin N→Lp E 4 μ := fun i => v i • L (basisVector i)
  have he : L v=∑i,V i := by
    conv_lhs => rw [←state_sum_basis v,map_sum]
    simp only [map_smul,V]
  have hs (i : Fin N) := Lp.coeFn_smul (v i) (L (basisVector i))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ V,ae_all_iff.mpr hs] with q hsum hsmul
  rw [he,hsum,Finset.sum_apply]
  calc
    _≤∑i : Fin N,‖V i q‖ := norm_sum_le _ _
    _≤∑i : Fin N,‖v‖*‖L (basisVector i) q‖ := Finset.sum_le_sum (fun i _ => by
      change ‖(v i • L (basisVector i) : Lp E 4 μ) q‖≤_
      rw [hsmul i,Pi.smul_apply,norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _))
    _=_ := by rw [Finset.mul_sum]

theorem mixed_norm_le_basis {G : Type*} [NormedAddCommGroup G]
    (L : State N→L[ℝ] Lp E 4 μ) (v : State N) (Q : α→G) (hQ : MemLp Q 4 μ) :
    lpNorm (fun q => ‖L v q‖*‖Q q‖) 2 μ≤
      ‖v‖*∑i : Fin N,lpNorm (fun q => ‖L (basisVector i) q‖*‖Q q‖) 2 μ := by
  classical
  let A : Fin N→α→ℝ := fun i q => ‖v‖*(‖L (basisVector i) q‖*‖Q q‖)
  have hA (i : Fin N) : MemLp (A i) 2 μ := ((Lp.memLp (L (basisVector i))).norm.fun_mul hQ.norm).const_mul ‖v‖
  have hpos (i : Fin N) (q : α) : 0≤A i q := by dsimp [A];positivity
  have hb : ∀ᵐq∂μ,‖‖L v q‖*‖Q q‖‖≤∑i,A i q := by
    filter_upwards [field_norm_le_basis L v] with q hq
    rw [Real.norm_of_nonneg (by positivity : 0≤‖L v q‖*‖Q q‖)]
    have hh := mul_le_mul_of_nonneg_right hq (norm_nonneg (Q q))
    simpa only [A,Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm] using hh
  have hn := LpFiniteDomination.lpNorm_le_sum ((Lp.memLp (L v)).norm.fun_mul hQ.norm) A hA hpos hb
  apply hn.trans_eq
  simp only [A,LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg (norm_nonneg v)]
  rw [Finset.mul_sum]

end SphericalAging.FiniteLpBasisMultiplier
