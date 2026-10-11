module

public import SphericalAging.GaussianObservableDerivative
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Module.Convex

public section

/-! Expectation is a genuine contraction on the probability L² space.
The fourth moment bounds its actual expected vector by Jensen's inequality. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace SphericalAging.L2ProbabilityExpectation
set_option backward.isDefEq.respectTransparency false
variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Probability expectation contracts the L² norm. -/
theorem norm_integral_le_L2 (U : Lp E 2 P) : ‖∫ ω,U ω ∂P‖ ≤ ‖U‖ := by
  have h := (enorm_integral_le_lintegral_enorm (fun ω => U ω)).trans
    ((eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable U)).symm.le.trans
      (eLpNorm_le_eLpNorm_of_exponent_le (f := fun ω => U ω) (by norm_num : (1 : ℝ≥0∞)≤2)))
  have hr := ENNReal.toReal_mono (Lp.eLpNorm_ne_top U) h
  simpa only [enorm,ENNReal.coe_toReal,coe_nnnorm,← Lp.norm_def] using hr

/-- The actual Bochner expectation as a continuous linear map on L². -/
@[expose] def expectation : Lp E 2 P →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun U => ∫ ω,U ω ∂P
      map_add' := fun U V => by
        rw [integral_congr_ae (Lp.coeFn_add U V)]
        exact integral_add ((Lp.memLp U).integrable (by norm_num))
          ((Lp.memLp V).integrable (by norm_num))
      map_smul' := fun c U => by
        rw [integral_congr_ae (Lp.coeFn_smul c U)]
        exact integral_smul c (fun ω => U ω) }
    1 (fun U => by
      change ‖∫ ω,U ω ∂P‖≤1*‖U‖
      simpa only [one_mul] using norm_integral_le_L2 U)

@[simp] theorem expectation_apply (U : Lp E 2 P) : expectation U=∫ ω,U ω ∂P := rfl

/-- A real fourth moment bounds the fourth power of the actual mean. -/
theorem norm_integral_fourth_le {U : Ω → E} (hU : MemLp U 4 P) :
    ‖∫ ω,U ω ∂P‖^4 ≤ ∫ ω,‖U ω‖^4 ∂P := by
  have hi := (convexOn_pow (𝕜 := ℝ) 4).map_integral_le
    ((continuous_id.pow 4).continuousOn) isClosed_Ici
    (.of_forall (fun ω => show ‖U ω‖∈Ici (0 : ℝ) from norm_nonneg _))
    (hU.integrable (by norm_num)).norm hU.integrable_norm_pow'
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm U) 4).trans hi

/-- Taking the fourth root of an exponential fourth-moment estimate. -/
theorem norm_integral_le_of_fourth_exp {U : Ω → E} (hU : MemLp U 4 P)
    (a : ℝ) (C : ℝ) (hC : 0≤C)
    (hbound : (∫ ω,‖U ω‖^4 ∂P)≤C^4*Real.exp (4*a)) :
    ‖∫ ω,U ω ∂P‖≤Real.exp a*C := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) hC)
    (by norm_num : (4 : ℕ)≠0)).mp
  calc
    _ ≤ ∫ ω,‖U ω‖^4 ∂P := norm_integral_fourth_le hU
    _ ≤ C^4*Real.exp (4*a) := hbound
    _ = (Real.exp a*C)^4 := by
      rw [mul_pow]
      rw [← Real.exp_nat_mul a 4]
      exact mul_comm _ _

end SphericalAging.L2ProbabilityExpectation
