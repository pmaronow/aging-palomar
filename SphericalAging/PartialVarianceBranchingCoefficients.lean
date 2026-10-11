module

public import SphericalAging.GaussianBranchingSuccess

public section

/-! Normalized Gaussian transitions for a prescribed nondecreasing partial
variance along a root-to-leaf path. The zero-variance case is constructed too. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.PartialVarianceBranchingCoefficients
open MeasureTheory ProbabilityTheory

@[expose] def parentRatio (v w : ℝ) : ℝ := if 0<w then Real.sqrt v/Real.sqrt w else 0
@[expose] def freshRatio (v w : ℝ) : ℝ := if 0<w then Real.sqrt (w-v)/Real.sqrt w else 1

theorem ratios_unit (v w : ℝ) (hv : 0≤v) (hvw : v≤w) :
    (parentRatio v w)^2+(freshRatio v w)^2=1 := by
  by_cases hw : 0<w
  · simp only [parentRatio,freshRatio,if_pos hw,div_pow,
      Real.sq_sqrt hv,Real.sq_sqrt hw.le,Real.sq_sqrt (sub_nonneg.mpr hvw)]
    field_simp
    ring
  · simp only [parentRatio,freshRatio,if_neg hw]
    norm_num

theorem scaled_parentRatio (v w : ℝ) (hv : 0≤v) (hvw : v≤w) :
    Real.sqrt w*parentRatio v w=Real.sqrt v := by
  by_cases hw : 0<w
  · simp only [parentRatio,if_pos hw]
    exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr hw).ne'
  · have hw0 : w=0 := le_antisymm (le_of_not_gt hw) (hv.trans hvw)
    have hv0 : v=0 := le_antisymm (hvw.trans_eq hw0) hv
    simp [hw0,hv0,parentRatio]

theorem scaled_freshRatio (v w : ℝ) (hv : 0≤v) (hvw : v≤w) :
    Real.sqrt w*freshRatio v w=Real.sqrt (w-v) := by
  by_cases hw : 0<w
  · simp only [freshRatio,if_pos hw]
    exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr hw).ne'
  · have hw0 : w=0 := le_antisymm (le_of_not_gt hw) (hv.trans hvw)
    have hv0 : v=0 := le_antisymm (hvw.trans_eq hw0) hv
    simp [hw0,hv0,freshRatio]

theorem actual_scaled_update {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v w : ℝ) (hv : 0≤v) (hvw : v≤w) (s g : E) :
    Real.sqrt w•(parentRatio v w•s+freshRatio v w•g)=
      Real.sqrt v•s+Real.sqrt (w-v)•g := by
  rw [smul_add,smul_smul,smul_smul,scaled_parentRatio v w hv hvw,
    scaled_freshRatio v w hv hvw]

@[expose] def parentCoefficient (V : ℕ→ℝ) (d : ℕ) : ℝ := parentRatio (V (d+1)) (V d)
@[expose] def freshCoefficient (V : ℕ→ℝ) (d : ℕ) : ℝ := freshRatio (V (d+1)) (V d)

theorem coefficients_unit (V : ℕ→ℝ) (hV : ∀d,0≤V d) (hmono : ∀d,V (d+1)≤V d) (d : ℕ) :
    (parentCoefficient V d)^2+(freshCoefficient V d)^2=1 :=
  ratios_unit _ _ (hV _) (hmono _)

end SphericalAging.PartialVarianceBranchingCoefficients
