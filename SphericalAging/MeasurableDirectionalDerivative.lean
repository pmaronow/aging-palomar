module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

public section

/-! A spatial directional derivative of a jointly measurable family is
measurable when every spatial section is differentiable. The proof uses
literal positive difference quotients; parameter continuity is unnecessary. -/
noncomputable section
open MeasureTheory Set Filter Topology
namespace SphericalAging.MeasurableDirectionalDerivative
set_option maxHeartbeats 1000000
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_fderiv_direction {f : α→E→ℝ}
    (hm : Measurable (Function.uncurry f)) (hd : ∀a x,DifferentiableAt ℝ (f a) x) (v : E) :
    Measurable (fun z : α×E => fderiv ℝ (f z.1) z.2 v) := by
  let a : ℕ→ℝ := fun n => 1/((n : ℝ)+1)
  let q : ℕ→α×E→ℝ := fun n z => (a n)⁻¹*(f z.1 (z.2+a n • v)-f z.1 z.2)
  have hq (n : ℕ) : Measurable (q n) := by
    exact ((hm.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))).sub hm).const_mul _
  have ha : Tendsto a atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall (fun n => ?_)⟩
    change 0<1/((n : ℝ)+1)
    positivity
  have ht (z : α×E) : Tendsto (fun n => q n z) atTop (𝓝 (fderiv ℝ (f z.1) z.2 v)) := by
    have hline : HasDerivAt (fun u : ℝ => z.2+u • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z.2
    have hdf := (hd z.1 z.2).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    have hh := hdf.tendsto_slope_zero_right.comp ha
    simpa only [q,Function.comp_def,zero_add,zero_smul,add_zero,smul_eq_mul] using hh
  exact measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.mpr ht)

end SphericalAging.MeasurableDirectionalDerivative
